module

public import CFSG.RankThree.PartTwo.Sec21.Item233Pieces
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.PartTwo.Sec21.InnerDiagonal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.RankThree.PartTwo.KFacts
open Matrix

abbrev F4 := GaloisField 2 2

abbrev SL34 := SpecialLinearGroup (Fin 3) F4

theorem card_F4 : Nat.card F4 = 4 := GaloisField.card 2 2 (by norm_num)

theorem card_units_F4 : Nat.card F4ˣ = 3 := by
  classical
  have := Fintype.ofFinite F4
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, card_F4]

theorem ringAut_mul_self (σ : F4 ≃+* F4) : σ * σ = 1 := by
  obtain ⟨-, -, -, -, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    (F := F4) Nat.prime_two (n := 2) (by norm_num) (by rw [card_F4]; norm_num)
  have := pow_card_eq_one' (G := F4 ≃+* F4) (x := σ)
  rwa [hcard, sq] at this

theorem mem_of_sq_mem {M : Type*} [Group M] (S : Subgroup M) {α : M} (h2 : α ^ 2 ∈ S)
    (h3 : ∃ k : ℕ, α ^ 3 ^ k = 1) : α ∈ S := by
  obtain ⟨k, hk⟩ := h3
  obtain ⟨m, hm⟩ : ∃ m, 3 ^ k = 2 * m + 1 := Odd.pow (by decide : Odd 3)
  have hα : α = ((α ^ 2) ^ m)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_mul, ← pow_succ', ← hm, hk]
  rw [hα]
  exact S.inv_mem (S.pow_mem h2 m)

theorem conj_range_normal {M : Type*} [Group M] : (MulAut.conj : M →* MulAut M).range.Normal := by
  refine ⟨fun _ ⟨g, hg⟩ φ => ⟨φ g, ?_⟩⟩
  rw [← hg]
  ext x
  simp [MulAut.conj_apply]

@[expose] noncomputable def inndiag : Subgroup (MulAut SL34) :=
  (CatalogueBHigherLinearAction.slConjugation 3 F4).range

theorem slConjugation_toGL_eq (g : SL34) :
    CatalogueBHigherLinearAction.slConjugation 3 F4 (SpecialLinearGroup.toGL g) =
      MulAut.conj g := by
  ext h
  rw [slConjugation_toGL 3 F4 g h, MulAut.conj_apply]

theorem inn_le_inndiag : (MulAut.conj : SL34 →* MulAut SL34).range ≤ inndiag := by
  rintro _ ⟨g, rfl⟩
  exact ⟨SpecialLinearGroup.toGL g, slConjugation_toGL_eq g⟩

theorem descendAut_injective : Function.Injective (descendAut 3 F4) := by
  have : Group.IsPerfect SL34 :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro e he
  rw [MonoidHom.mem_ker] at he
  rw [Subgroup.mem_bot]
  refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h := congrArg (fun φ : MulAut (projectiveSL 3 F4) => φ (proj 3 F4 s)) he
  simp only [descendAut_proj, MulAut.one_apply] at h
  rw [proj_eq_proj_iff, scalars_eq_center] at h
  have := (Subgroup.center _).inv_mem h
  simpa using this

theorem inndiag_eq_comap : inndiag = (linearAutGroup 3 F4).comap (descendAut 3 F4) := by
  ext σ
  constructor
  · rintro ⟨A, rfl⟩
    exact conjAut_mem_linearAutGroup A
  · intro hσ
    rw [Subgroup.mem_comap, linearAutGroup_eq_range] at hσ
    obtain ⟨A, hA⟩ := hσ
    refine ⟨A, descendAut_injective ?_⟩
    exact hA

theorem inndiag_normal : inndiag.Normal := by
  rw [inndiag_eq_comap]
  have : (linearAutGroup 3 F4).Normal := (stdPinnedPSL_stable (n := 3) (K := F4) le_rfl).normal
  exact Subgroup.Normal.comap this _

theorem mem_linearAutGroup_of_pow (α : MulAut (projectiveSL 3 F4))
    (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) : α ∈ linearAutGroup 3 F4 := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F4) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hgen α
  obtain ⟨-, hff, -, hδδ, -, hδf, -⟩ := standard_automorphism_transport (K := F4) (n := 3)
  set r := fieldAut 3 F4 σ * dualAut 3 F4 ^ ε with hrdef
  have hff1 : fieldAut 3 F4 σ * fieldAut 3 F4 σ = 1 := by
    rw [hff, ringAut_mul_self, map_one]
  have hr : r * r = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · rw [hrdef, pow_zero, mul_one, hff1]
    · rw [hrdef, pow_one]
      calc fieldAut 3 F4 σ * dualAut 3 F4 * (fieldAut 3 F4 σ * dualAut 3 F4)
          = fieldAut 3 F4 σ * (dualAut 3 F4 * fieldAut 3 F4 σ * dualAut 3 F4) := by
            simp only [mul_assoc]
        _ = 1 := by rw [hδf, hff1]
  have hnorm : (linearAutGroup 3 F4).Normal :=
    (stdPinnedPSL_stable (n := 3) (K := F4) le_rfl).normal
  have hc := conjAut_mem_linearAutGroup (n := 3) (K := F4) A
  apply mem_of_sq_mem _ _ hα
  have hαr : α = conjAut 3 F4 A * r := by rw [hαeq, hrdef, mul_assoc]
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr
  rw [hαr, sq]
  have : conjAut 3 F4 A * r * (conjAut 3 F4 A * r) =
      conjAut 3 F4 A * (r * conjAut 3 F4 A * r⁻¹) := by
    rw [hrinv]
    simp only [mul_assoc]
  rw [this]
  exact Subgroup.mul_mem _ hc (hnorm.conj_mem _ hc r)

theorem mem_inndiag_of_pow (α : MulAut SL34) (hα : ∃ k : ℕ, α ^ 3 ^ k = 1) : α ∈ inndiag := by
  rw [inndiag_eq_comap, Subgroup.mem_comap]
  obtain ⟨k, hk⟩ := hα
  exact mem_linearAutGroup_of_pow _ ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem inndiag_le_of_not_mem {T : Subgroup (MulAut SL34)}
    (hT : (MulAut.conj : SL34 →* MulAut SL34).range ≤ T) {q : MulAut SL34} (hqD : q ∈ inndiag)
    (hqI : q ∉ (MulAut.conj : SL34 →* MulAut SL34).range) (hqT : q ∈ T) : inndiag ≤ T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨A, rfl⟩ := hqD
  set d := GeneralLinearGroup.det A with hd
  have hd1 : d ≠ 1 := by
    intro h1
    apply hqI
    have hdet : (A : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      rw [← GeneralLinearGroup.val_det_apply, ← hd, h1, Units.val_one]
    let g : SL34 := ⟨A, hdet⟩
    have hg : SpecialLinearGroup.toGL g = A := Units.ext rfl
    exact ⟨g, by rw [← slConjugation_toGL_eq, hg]⟩
  rintro _ ⟨B, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card card_units_F4 hd1 (g' := GeneralLinearGroup.det B))
  set C := B * (A ^ j)⁻¹ with hC
  have hCdet : (C : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hC, map_mul, map_inv, map_zpow, ← hd, hj,
      mul_inv_cancel, Units.val_one]
  let g : SL34 := ⟨C, hCdet⟩
  have hg : SpecialLinearGroup.toGL g = C := Units.ext rfl
  have hB : B = C * A ^ j := by rw [hC, inv_mul_cancel_right]
  rw [hB, map_mul, map_zpow, ← hg, slConjugation_toGL_eq]
  exact T.mul_mem (hT ⟨g, rfl⟩) (T.zpow_mem hqT j)

section Action

variable {H : Type} [Group H] {Y : Subgroup H} [hYn : Y.Normal] (e : Y ≃* SL34)

@[expose] noncomputable def act : H →* MulAut SL34 :=
  (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := Y))

theorem act_apply (h : H) (g : SL34) :
    act e h g = e ⟨h * (e.symm g : H) * h⁻¹, hYn.conj_mem _ (e.symm g).2 h⟩ := by
  change e (MulAut.conjNormal h (e.symm g)) = _
  congr 1

theorem act_mem (y : Y) : act e (y : H) = MulAut.conj (e y) := by
  ext g
  rw [act_apply, MulAut.conj_apply]
  have : (⟨(y : H) * (e.symm g : H) * (y : H)⁻¹, hYn.conj_mem _ (e.symm g).2 (y : H)⟩ : Y) =
      y * e.symm g * y⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem act_eq_one_iff (h : H) : act e h = 1 ↔ h ∈ Subgroup.centralizer (Y : Set H) := by
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 := congrArg (fun φ : MulAut SL34 => φ (e ⟨y, hy⟩)) h1
    simp only [MulAut.one_apply, act_apply, MulEquiv.symm_apply_apply] at h2
    have h3 := congrArg Subtype.val (e.injective h2)
    change h * y * h⁻¹ = y at h3
    calc y * h = h * y * h⁻¹ * h := by rw [h3]
      _ = h * y := by group
  · intro hh
    ext g
    rw [act_apply, MulAut.one_apply]
    have hc : h * (e.symm g : H) * h⁻¹ = (e.symm g : H) := by
      have := (Subgroup.mem_centralizer_iff.mp hh) _ (e.symm g).2
      rw [← this, mul_assoc, mul_inv_cancel, mul_one]
    have : (⟨h * (e.symm g : H) * h⁻¹, hYn.conj_mem _ (e.symm g).2 h⟩ : Y) = e.symm g :=
      Subtype.ext hc
    rw [this, MulEquiv.apply_symm_apply]

end Action

theorem innerDiagonalSL34 : InnerDiagonalSL34 := by
  intro H _ _ Y P hYn ⟨e⟩ hP
  set ψ := act e
  set Inn := (MulAut.conj : SL34 →* MulAut SL34).range
  have hInn : Inn.Normal := conj_range_normal
  set T := Inn ⊔ P.map ψ
  have hTn : T.Normal := by
    by_cases hPI : P.map ψ ≤ Inn
    · rw [show T = Inn from sup_eq_left.mpr hPI]
      exact hInn
    · obtain ⟨_, ⟨p, hp, rfl⟩, hpI⟩ := IsConcreteLE.not_le_iff_exists.mp hPI
      have hPD : P.map ψ ≤ inndiag := by
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
        refine mem_inndiag_of_pow _ ⟨k, ?_⟩
        have hk' : x ^ 3 ^ k = 1 := by
          have := congrArg Subtype.val (pow_orderOf_eq_one (⟨x, hx⟩ : P))
          rw [hk] at this
          simpa using this
        rw [← map_pow, hk', map_one]
      have hTD : T = inndiag := by
        refine le_antisymm (sup_le inn_le_inndiag hPD) ?_
        exact inndiag_le_of_not_mem le_sup_left (hPD ⟨p, hp, rfl⟩) hpI
          (Subgroup.mem_sup_right ⟨p, hp, rfl⟩)
      rw [hTD]
      exact inndiag_normal
  have heq : Y ⊔ Subgroup.centralizer (Y : Set H) ⊔ P = T.comap ψ := by
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro y hy
        rw [Subgroup.mem_comap]
        have : ψ y = MulAut.conj (e ⟨y, hy⟩) := act_mem e ⟨y, hy⟩
        rw [this]
        exact Subgroup.mem_sup_left ⟨_, rfl⟩
      · intro c hc
        rw [Subgroup.mem_comap, (act_eq_one_iff e c).mpr hc]
        exact T.one_mem
      · intro p hp
        exact Subgroup.mem_sup_right ⟨p, hp, rfl⟩
    · intro h hh
      rw [Subgroup.mem_comap] at hh
      have hmem : ψ h ∈ ((Inn ⊔ P.map ψ : Subgroup (MulAut SL34)) : Set (MulAut SL34)) := hh
      rw [Subgroup.normal_mul] at hmem
      obtain ⟨_, ⟨g, rfl⟩, _, ⟨p, hp, rfl⟩, hgp⟩ := hmem
      have hgp' : MulAut.conj g * act e p = act e h := hgp
      set y : Y := e.symm g
      have hc : (y : H)⁻¹ * h * p⁻¹ ∈ Subgroup.centralizer (Y : Set H) := by
        rw [← act_eq_one_iff e]
        have hy : act e (y : H) = MulAut.conj g := by
          rw [act_mem e y, MulEquiv.apply_symm_apply]
        rw [map_mul, map_mul, map_inv, map_inv, hy, ← hgp', inv_mul_cancel_left, mul_inv_cancel]
      have : h = (y : H) * ((y : H)⁻¹ * h * p⁻¹) * p := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left y.2))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hc))) (Subgroup.mem_sup_right hp)
  rw [heq]
  exact Subgroup.Normal.comap hTn ψ

end CFSG.RankThree.PartTwo.Sec21.InnerDiagonal
