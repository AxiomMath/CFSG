module

public import CFSG.Quasithin.Vol2.Ch10Reselect.LineSub

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix
open scoped commutatorElement

private theorem matrix_eq_one_of_mulVec' {K : Type} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (h : ∀ y : Fin 2 → K, M *ᵥ y = y) : M = 1 := by
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hj
  simpa [Matrix.one_apply, Pi.single_apply] using hj

namespace UModel

variable {G : Type} [Group G] {A U Z L : Subgroup G} {K : Type} [Field K]

private theorem conj_mem_Z (M : UModel A U Z L K) {j z : G} (hjU : j ∈ U) (hzU : z ∈ U)
    (hz : z ∈ Z) : j⁻¹ * z * j ∈ Z := by
  have hpU : j⁻¹ * z * j ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hjU) hzU) hjU
  have e : (⟨j⁻¹ * z * j, hpU⟩ : ↥U) = (⟨j, hjU⟩ : ↥U)⁻¹ * ⟨z, hzU⟩ * ⟨j, hjU⟩ := rfl
  have hψz : M.ψ ⟨z, hzU⟩ = 1 := (M.ker ⟨z, hzU⟩).mpr hz
  have h1 : M.ψ ⟨j⁻¹ * z * j, hpU⟩ = 1 := by
    rw [e, map_mul, map_mul, map_inv, hψz, mul_one, inv_mul_cancel]
  exact (M.ker ⟨j⁻¹ * z * j, hpU⟩).mp h1

theorem commutator_lineJ [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hZL : Z ≤ Subgroup.centralizer (L : Set G)) :
    ⁅M.lineJ w, L⁆ = M.lineJ w := by
  have hLJ : L ≤ Subgroup.normalizer (M.lineJ w : Set G) := L_le_normalizer_lineJ M w hLU
  apply le_antisymm
  ·
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyx : y * x⁻¹ * y⁻¹ ∈ M.lineJ w :=
      (Subgroup.mem_normalizer_iff.mp (hLJ hy) x⁻¹).mp ((M.lineJ w).inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹)
      group
    rw [e]
    exact (M.lineJ w).mul_mem hx hyx
  ·
    show ⁅M.lineSub w, L⁆ ≤ ⁅M.lineJ w, L⁆
    rw [Subgroup.commutator_le]
    intro u hu l hl
    obtain ⟨j, hj, hzZ⟩ := exists_lineJ_mul_mem_Z M hw hLU hu
    have hjU : j ∈ U := lineJ_le_U M w hLU hj
    have huU : u ∈ U := lineSub_le_U M w hu
    have hzU : u * j⁻¹ ∈ U := U.mul_mem huU (U.inv_mem hjU)
    obtain ⟨z', hz'Z, hu_eq⟩ : ∃ z' ∈ Z, u = j * z' :=
      ⟨j⁻¹ * (u * j⁻¹) * j, conj_mem_Z M hjU hzU hzZ, by group⟩
    subst hu_eq
    have hcomm : l * z' = z' * l := Subgroup.mem_centralizer_iff.mp (hZL hz'Z) l hl
    have e : ⁅j * z', l⁆ = ⁅j, l⁆ := by
      show j * z' * l * (j * z')⁻¹ * l⁻¹ = j * l * j⁻¹ * l⁻¹
      have h2 : z' * l * z'⁻¹ = l := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hcomm.symm
      calc j * z' * l * (j * z')⁻¹ * l⁻¹ = j * (z' * l * z'⁻¹) * j⁻¹ * l⁻¹ := by group
        _ = j * l * j⁻¹ * l⁻¹ := by rw [h2]
    rw [e]
    exact Subgroup.commutator_mem_commutator hj hl

theorem exists_lineJ_not_mem_Z [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) : ∃ j ∈ M.lineJ w, j ∉ Z := by
  have he : (![1, 0] : Fin 2 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have hp : ((w 0 • (![1, 0] : Fin 2 → K), w 1 • (![1, 0] : Fin 2 → K)) : UTilde K) ∈
      lineAdd K w :=
    mem_lineAdd_iff.mpr ⟨_, rfl⟩
  obtain ⟨j, hj, hjU, hψj⟩ := exists_lineJ_psi_eq M hw hLU hp
  refine ⟨j, hj, fun hjZ => ?_⟩
  have h1 : M.ψ ⟨j, hjU⟩ = 1 := (M.ker ⟨j, hjU⟩).mpr hjZ
  have h2 : (w 0 • (![1, 0] : Fin 2 → K), w 1 • (![1, 0] : Fin 2 → K)) = 0 := by
    rw [← hψj, h1, toAdd_one]
  obtain ⟨h20, h21⟩ := Prod.mk_eq_zero.mp h2
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (funext hcon)
  fin_cases i
  · exact hi ((smul_eq_zero.mp h20).resolve_right he)
  · exact hi ((smul_eq_zero.mp h21).resolve_right he)

theorem lineJ_ne_bot [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) : M.lineJ w ≠ ⊥ := by
  intro h
  obtain ⟨j, hj, hjZ⟩ := exists_lineJ_not_mem_Z M hw hLU
  rw [h, Subgroup.mem_bot] at hj
  exact hjZ (by rw [hj]; exact Z.one_mem)

theorem lineJ_irreducible [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) {J' : Subgroup G} (h1 : M.lineJ w ⊓ Z ≤ J')
    (h2 : J' ≤ M.lineJ w) (h3 : L ≤ Subgroup.normalizer (J' : Set G)) :
    J' = M.lineJ w ⊓ Z ∨ J' = M.lineJ w := by
  let S : AddSubgroup (UTilde K) :=
    { carrier := {p | ∃ (j : G) (_ : j ∈ J') (hjU : j ∈ U),
        Multiplicative.toAdd (M.ψ ⟨j, hjU⟩) = p}
      zero_mem' := ⟨1, J'.one_mem, U.one_mem, by
        rw [show (⟨1, U.one_mem⟩ : ↥U) = 1 from rfl, map_one, toAdd_one]⟩
      add_mem' := by
        rintro _ _ ⟨j, hj, hjU, rfl⟩ ⟨j', hj', hjU', rfl⟩
        exact ⟨j * j', J'.mul_mem hj hj', U.mul_mem hjU hjU', by
          rw [show (⟨j * j', U.mul_mem hjU hjU'⟩ : ↥U) = ⟨j, hjU⟩ * ⟨j', hjU'⟩ from rfl,
            map_mul, toAdd_mul]⟩
      neg_mem' := by
        rintro _ ⟨j, hj, hjU, rfl⟩
        exact ⟨j⁻¹, J'.inv_mem hj, U.inv_mem hjU, by
          rw [show (⟨j⁻¹, U.inv_mem hjU⟩ : ↥U) = (⟨j, hjU⟩ : ↥U)⁻¹ from rfl, map_inv, toAdd_inv]⟩ }
  have hSle : S ≤ lineAdd K w := by
    rintro p ⟨j, hj, hjU, rfl⟩
    exact psi_mem_line_of_mem_lineJ M w hLU (h2 hj) hjU
  have hinv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (p : UTilde K), p ∈ S →
      rhoSL K g p ∈ S := by
    intro g p hp
    obtain ⟨j, hj, hjU, rfl⟩ := hp
    obtain ⟨l, rfl⟩ := M.γ_surj g
    have hlj : (l : G) * j * (l : G)⁻¹ ∈ J' :=
      (Subgroup.mem_normalizer_iff.mp (h3 l.2) j).mp hj
    have hljU : (l : G) * j * (l : G)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (hLU l.2) j).mp hjU
    refine ⟨(l : G) * j * (l : G)⁻¹, hlj, hljU, ?_⟩
    have e := congrArg Multiplicative.toAdd (M.equiv l ⟨j, hjU⟩ hljU)
    rw [toAdd_ofAdd] at e
    exact e
  rcases lineAdd_irreducible hw S hSle hinv with hbot | hline
  ·
    left
    have hJZ : J' ≤ M.lineJ w ⊓ Z := by
      intro j hj
      refine Subgroup.mem_inf.mpr ⟨h2 hj, ?_⟩
      have hjU : j ∈ U := lineJ_le_U M w hLU (h2 hj)
      have hmem : Multiplicative.toAdd (M.ψ ⟨j, hjU⟩) ∈ S := ⟨j, hj, hjU, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at hmem
      exact (M.ker ⟨j, hjU⟩).mp (toAdd_eq_zero.mp hmem)
    exact le_antisymm hJZ h1
  ·
    right
    apply le_antisymm h2
    intro j hj
    have hjU : j ∈ U := lineJ_le_U M w hLU hj
    have hmem : Multiplicative.toAdd (M.ψ ⟨j, hjU⟩) ∈ S := by
      rw [hline]
      exact psi_mem_line_of_mem_lineJ M w hLU hj hjU
    obtain ⟨j', hj', hj'U, hψeq⟩ := hmem
    have hψeq' : M.ψ ⟨j', hj'U⟩ = M.ψ ⟨j, hjU⟩ := Multiplicative.toAdd.injective hψeq
    have hZ : j'⁻¹ * j ∈ Z := by
      have h1' : M.ψ ⟨j'⁻¹ * j, U.mul_mem (U.inv_mem hj'U) hjU⟩ = 1 := by
        rw [show (⟨j'⁻¹ * j, U.mul_mem (U.inv_mem hj'U) hjU⟩ : ↥U) =
          (⟨j', hj'U⟩ : ↥U)⁻¹ * ⟨j, hjU⟩ from rfl, map_mul, map_inv, hψeq', inv_mul_cancel]
      exact (M.ker _).mp h1'
    have hJ'' : j'⁻¹ * j ∈ M.lineJ w ⊓ Z :=
      Subgroup.mem_inf.mpr ⟨(M.lineJ w).mul_mem ((M.lineJ w).inv_mem (h2 hj')) hj, hZ⟩
    have hmem2 : j'⁻¹ * j ∈ J' := h1 hJ''
    have := J'.mul_mem hj' hmem2
    rwa [mul_inv_cancel_left] at this

theorem eq_one_of_centralizes_lineJ [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K}
    (hw : w ≠ 0) (hLU : L ≤ Subgroup.normalizer (U : Set G)) (l : ↥L)
    (h : ∀ j ∈ M.lineJ w, (l : G) * j * (l : G)⁻¹ = j) : M.γ l = 1 := by
  have hfix : ∀ u : Fin 2 → K,
      rhoSL K (M.γ l) (w 0 • u, w 1 • u) = (w 0 • u, w 1 • u) := by
    intro u
    obtain ⟨j, hj, hjU, hψj⟩ := exists_lineJ_psi_eq M hw hLU
      (p := (w 0 • u, w 1 • u)) ⟨u, rfl⟩
    have hu' : (l : G) * j * (l : G)⁻¹ ∈ U := by
      rw [h j hj]
      exact hjU
    have hsub : (⟨(l : G) * j * (l : G)⁻¹, hu'⟩ : ↥U) = ⟨j, hjU⟩ := Subtype.ext (h j hj)
    have key : M.ψ ⟨j, hjU⟩ =
        Multiplicative.ofAdd (rhoSL K (M.γ l) (Multiplicative.toAdd (M.ψ ⟨j, hjU⟩))) :=
      (congrArg M.ψ hsub).symm.trans (M.equiv l ⟨j, hjU⟩ hu')
    have e := congrArg Multiplicative.toAdd key
    rw [toAdd_ofAdd, hψj] at e
    exact e.symm
  have hgu : ∀ u : Fin 2 → K, ((M.γ l : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) *ᵥ u = u := by
    intro u
    have h := hfix u
    rw [rhoSL_apply, Matrix.mulVec_smul, Matrix.mulVec_smul] at h
    have h0 := congrArg Prod.fst h
    have h1 := congrArg Prod.snd h
    simp only at h0 h1
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw (funext hcon)
    fin_cases i
    · exact smul_right_injective (Fin 2 → K) hi h0
    · exact smul_right_injective (Fin 2 → K) hi h1
  have hM : ((M.γ l : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    matrix_eq_one_of_mulVec' _ hgu
  exact Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact congrFun (congrFun hM i) j

theorem exists_hom_lineJ [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K} (hw : w ≠ 0)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    ∃ f : ↥(M.lineJ w) →* Multiplicative ↥(lineAdd K w), Function.Surjective f ∧
      ∀ j : ↥(M.lineJ w), f j = 1 ↔ (j : G) ∈ Z := by
  have hJU : ∀ j : ↥(M.lineJ w), (j : G) ∈ U := fun j => lineJ_le_U M w hLU j.2
  let φ : ↥(M.lineJ w) → Multiplicative ↥(lineAdd K w) := fun j =>
    Multiplicative.ofAdd ⟨Multiplicative.toAdd (M.ψ ⟨(j : G), hJU j⟩),
      psi_mem_line_of_mem_lineJ M w hLU j.2 (hJU j)⟩
  have hφmul : ∀ a b : ↥(M.lineJ w), φ (a * b) = φ a * φ b := by
    intro a b
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    show Multiplicative.toAdd (M.ψ ⟨((a * b : ↥(M.lineJ w)) : G), hJU (a * b)⟩) =
      Multiplicative.toAdd (M.ψ ⟨(a : G), hJU a⟩) + Multiplicative.toAdd (M.ψ ⟨(b : G), hJU b⟩)
    rw [show (⟨((a * b : ↥(M.lineJ w)) : G), hJU (a * b)⟩ : ↥U) =
      ⟨(a : G), hJU a⟩ * ⟨(b : G), hJU b⟩ from rfl, map_mul, toAdd_mul]
  refine ⟨MonoidHom.mk' φ hφmul, ?_, ?_⟩
  ·
    intro q
    obtain ⟨j, hj, hjU, hψ⟩ := exists_lineJ_psi_eq M hw hLU (Multiplicative.toAdd q).2
    refine ⟨⟨j, hj⟩, ?_⟩
    exact (congrArg Multiplicative.ofAdd (Subtype.ext hψ)).trans (ofAdd_toAdd q)
  · intro j
    constructor
    · intro h
      have h' : Multiplicative.ofAdd (⟨Multiplicative.toAdd (M.ψ ⟨(j : G), hJU j⟩),
          psi_mem_line_of_mem_lineJ M w hLU j.2 (hJU j)⟩ : ↥(lineAdd K w)) = 1 := h
      have h1 : (⟨Multiplicative.toAdd (M.ψ ⟨(j : G), hJU j⟩),
          psi_mem_line_of_mem_lineJ M w hLU j.2 (hJU j)⟩ : ↥(lineAdd K w)) = 0 := by
        have := congrArg Multiplicative.toAdd h'
        rwa [toAdd_ofAdd, toAdd_one] at this
      have h2 : Multiplicative.toAdd (M.ψ ⟨(j : G), hJU j⟩) = 0 := congrArg Subtype.val h1
      exact (M.ker ⟨(j : G), hJU j⟩).mp (toAdd_eq_zero.mp h2)
    · intro hjZ
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      show Multiplicative.toAdd (M.ψ ⟨(j : G), hJU j⟩) = 0
      rw [toAdd_eq_zero]
      exact (M.ker ⟨(j : G), hJU j⟩).mpr hjZ

theorem card_lineJ [Finite G] [Finite K] [Nontrivial K] (M : UModel A U Z L K) {w : Fin 2 → K}
    (hw : w ≠ 0) (hLU : L ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥(M.lineJ w) = Nat.card ↥(Z.subgroupOf (M.lineJ w)) * Nat.card K ^ 2 := by
  obtain ⟨f, hfsurj, hfker⟩ := exists_hom_lineJ M hw hLU
  have hker : f.ker = Z.subgroupOf (M.lineJ w) := by
    ext j
    rw [MonoidHom.mem_ker, hfker j, Subgroup.mem_subgroupOf]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hquot : Nat.card (↥(M.lineJ w) ⧸ f.ker) = Nat.card ↥(lineAdd K w) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv,
      Nat.card_congr (Multiplicative.ofAdd : ↥(lineAdd K w) ≃ Multiplicative ↥(lineAdd K w))]
  rw [hquot, card_lineAdd hw, hker] at hcard
  rw [hcard, mul_comm]

theorem card_eq_pow_four [Finite G] [Finite K] (M : UModel A U Z L K) :
    Nat.card ↥U = Nat.card ↥(Z.subgroupOf U) * Nat.card K ^ 4 := by
  have hsurj : Function.Surjective M.ψ := M.surj
  have hker : M.ψ.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, M.ker u, Subgroup.mem_subgroupOf]
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup M.ψ.ker
  have hquot : Nat.card (↥U ⧸ M.ψ.ker) = Nat.card (UTilde K) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective M.ψ hsurj).toEquiv,
      Nat.card_congr (Multiplicative.ofAdd : UTilde K ≃ Multiplicative (UTilde K))]
  rw [hquot, card_uTilde, hker] at hcard
  rw [hcard, mul_comm]

end UModel

end CFSG.Quasithin.Vol2.Ch10Reselect
