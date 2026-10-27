module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open Matrix

section Products

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem inf_subgroupOf {H K X : Subgroup G} :
    (H ⊓ K).subgroupOf X = H.subgroupOf X ⊓ K.subgroupOf X := by
  ext x
  simp [Subgroup.mem_subgroupOf]

end Products

section ScalarMul

variable {K : Type} [Field K]

theorem commute_of_commute_mul_scalar {z w : GL (Fin 3) K} {s t : Kˣ}
    (h : z * GeneralLinearGroup.scalar (Fin 3) s * (w * GeneralLinearGroup.scalar (Fin 3) t) =
      w * GeneralLinearGroup.scalar (Fin 3) t * (z * GeneralLinearGroup.scalar (Fin 3) s)) :
    z * w = w * z := by
  have hs := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar s w
  have ht := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t z
  have hst := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t
    (GeneralLinearGroup.scalar (Fin 3) s)
  have e1 : z * GeneralLinearGroup.scalar (Fin 3) s * (w * GeneralLinearGroup.scalar (Fin 3) t) =
      z * w * (GeneralLinearGroup.scalar (Fin 3) s * GeneralLinearGroup.scalar (Fin 3) t) :=
    calc z * GeneralLinearGroup.scalar (Fin 3) s * (w * GeneralLinearGroup.scalar (Fin 3) t)
        = z * (GeneralLinearGroup.scalar (Fin 3) s * w) * GeneralLinearGroup.scalar (Fin 3) t := by
          group
      _ = z * (w * GeneralLinearGroup.scalar (Fin 3) s) * GeneralLinearGroup.scalar (Fin 3) t := by
          rw [← hs.eq]
      _ = _ := by group
  have e2 : w * GeneralLinearGroup.scalar (Fin 3) t * (z * GeneralLinearGroup.scalar (Fin 3) s) =
      w * z * (GeneralLinearGroup.scalar (Fin 3) s * GeneralLinearGroup.scalar (Fin 3) t) :=
    calc w * GeneralLinearGroup.scalar (Fin 3) t * (z * GeneralLinearGroup.scalar (Fin 3) s)
        = w * (GeneralLinearGroup.scalar (Fin 3) t * z) * GeneralLinearGroup.scalar (Fin 3) s := by
          group
      _ = w * (z * GeneralLinearGroup.scalar (Fin 3) t) * GeneralLinearGroup.scalar (Fin 3) s := by
          rw [← ht.eq]
      _ = w * z * (GeneralLinearGroup.scalar (Fin 3) t * GeneralLinearGroup.scalar (Fin 3) s) := by
          group
      _ = _ := by rw [← hst.eq]
  rw [e1, e2] at h
  exact mul_right_cancel h

end ScalarMul

section Heis

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite G] in
theorem type13_of_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {A : Subgroup G} {hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y}
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    {a : G} (ha : a ∈ A) (haC : a ∉ Subgroup.centralizer (L : Set G)) (ha3 : a ^ 3 = 1)
    {y : GL (Fin 3) K} (hy : IsPGLAt e a y) :
    Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3 := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  have hyZ : y ∉ zPi π 3 (p ^ f) K := fun hz =>
    haC (mem_centralizer_of_isPGLAt_scalar hy (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz))
  have hy3 := pow_three_mem_zPi hK hq ha3 hy
  have hcomm := range_pglHom_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm
  have hymem := mk_mem_range_pglHom ha hy (hK := hK) (hq := hq) (hA' := hpgl)
  rcases type123_exhaust hK hq hy.1 hyZ hy3 with h | h | h
  · exact Or.inl h
  · exfalso
    apply trace_ne_zero_of_type2 hK hq h
    by_cases hc1 : y * y₁ = y₁ * y
    · by_cases hc2 : y * y₂ = y₂ * y
      · exact absurd (mem_zPi_of_isPGLAt hK hq (mem_centralizer_of_isPGLAt_scalar hy
          (mem_statedScalars_of_commute_heis h3 hζ1 (pow_three_eq_one_of_conj_eq_scalar_mul hζ)
            hζ hc1 hc2)) hy) hyZ
      · obtain ⟨lam2, hlam2⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hy₂ _ hymem)
        refine trace_eq_zero_of_conj_eq_scalar_mul (fun h1 => hc2 ?_) hlam2
        rw [h1, map_one, one_mul] at hlam2
        calc y * y₂ = y₂ * y * y₂⁻¹ * y₂ := by rw [hlam2]
          _ = y₂ * y := by group
    · obtain ⟨lam1, hlam1⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hy₁ _ hymem)
      refine trace_eq_zero_of_conj_eq_scalar_mul (fun h1 => hc1 ?_) hlam1
      rw [h1, map_one, one_mul] at hlam1
      calc y * y₁ = y₁ * y * y₁⁻¹ * y₁ := by rw [hlam1]
        _ = y₁ * y := by group
  · exact Or.inr h

omit [Finite G] in
theorem exists_inner_decomp (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* slPi π 3 (p ^ f) K} {a : G} {y : GL (Fin 3) K} (hy : IsPGLAt e a y)
    (h1 : Type123 π (p ^ f) K y 1) :
    ∃ v : L, (v : G) ^ 3 = 1 ∧ a * v = v * a ∧ a * (v : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) ∧
      ∃ μ : Kˣ, ((e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        y * GeneralLinearGroup.scalar (Fin 3) μ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨τ', hτ', hτ1', z, hz, g, hg, hD⟩ := h1
  obtain ⟨μ, hμ⟩ := mem_statedScalars_of_mem_zPi hK hq hτ' hτ1' hz
  have hzH : z ∈ glPi π 3 (p ^ f) K := by
    obtain ⟨w, -, rfl⟩ := hz
    exact w.2
  set l₀ := y * z with hl₀
  have hl₀D : l₀ = g * diagTau hτ' * g⁻¹ := by rw [← hD]; group
  have hl₀det : (l₀ : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [hl₀D, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm,
      ← mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one, one_mul, coe_diagTau_eq_diagonal, Matrix.det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, mul_one]
    rw [← pow_succ', hτ']
  have hl₀S : l₀ ∈ slPi π 3 (p ^ f) K := (mem_slPi_iff hπ).mpr ⟨mul_mem hy.1 hzH, hl₀det⟩
  have hl₀3 : l₀ ^ 3 = 1 := by
    rw [hl₀D, conj_pow, diagTau_pow_three, mul_one, mul_inv_cancel]
  set v : L := e.symm ⟨l₀, hl₀S⟩ with hv
  have hev : ((e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K) = l₀ := by
    rw [hv, MulEquiv.apply_symm_apply]
  have hzc := commute_of_mem_statedScalars ⟨μ, hμ⟩ y
  refine ⟨v, ?_, ?_, ?_, μ, by rw [hev, hl₀, ← hμ]⟩
  · rw [← Subgroup.coe_pow, ← map_pow]
    have : (⟨l₀, hl₀S⟩ : slPi π 3 (p ^ f) K) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, hl₀3, Subgroup.coe_one])
    rw [this, map_one, Subgroup.coe_one]
  ·
    have h2 := hy.2 ⟨l₀, hl₀S⟩
    have h3 : y * l₀ * y⁻¹ = l₀ := by
      rw [hl₀]
      calc y * (y * z) * y⁻¹ = y * (z * y) * y⁻¹ := by rw [hzc]
        _ = y * z := by group
    rw [h3] at h2
    have h4 : slAct e ⟨a, mem_normalizer_of_normal a⟩ ⟨l₀, hl₀S⟩ = ⟨l₀, hl₀S⟩ := Subtype.ext h2
    rw [slAct_apply] at h4
    have h5 := congrArg (fun s => (e.symm s : G)) h4
    simp only [MulEquiv.symm_apply_apply] at h5
    change a * (v : G) * a⁻¹ = v at h5
    calc a * (v : G) = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [h5]
  ·
    have hvinv : IsPGLAt e ((v : G)⁻¹) l₀⁻¹ := by
      have := isPGLAt_of_mem e hπ (inv_mem v.2)
      have e1 : (⟨(v : G)⁻¹, inv_mem v.2⟩ : L) = v⁻¹ := rfl
      rw [e1, map_inv, Subgroup.coe_inv, hev] at this
      exact this
    have hprod := isPGLAt_mul e hy hvinv
    refine mem_centralizer_of_isPGLAt_scalar hprod ?_
    have hzi : z⁻¹ * y⁻¹ = y⁻¹ * z⁻¹ := by
      rw [← _root_.mul_inv_rev, ← _root_.mul_inv_rev, hzc]
    have : y * l₀⁻¹ = z⁻¹ := by rw [hl₀, _root_.mul_inv_rev, hzi, mul_inv_cancel_left]
    rw [this]
    exact inv_mem ⟨μ, hμ⟩

theorem isHeisThree_of (U : Type) [Group U] [Finite U] (hcard : Nat.card U = 27)
    (h3 : ∀ x : U, x ^ 3 = 1) (hnc : ¬ IsMulCommutative U) : IsHeisThree U := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 U := fun x => ⟨1, by rw [pow_one]; exact h3 x⟩
  refine ⟨CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three hP h3
    (by rw [hcard]; norm_num) hnc, hcard, ?_⟩
  have hdvd : Monoid.exponent U ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one h3
  have hne : Monoid.exponent U ≠ 1 := by
    intro h1
    rw [Monoid.exp_eq_one_iff] at h1
    have : Nat.card U = 1 := Nat.card_unique
    omega
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne
  · exact h

theorem heis_of_type1 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G} (hAel : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27' : Nat.card A = 27) {c : G} (hc3 : orderOf c = 3) (hcL : c ∈ L)
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) (hAL : A ⊓ L ≤ Subgroup.zpowers c)
    {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (h1 : ∀ a ∈ A, a ∉ Subgroup.centralizer (L : Set G) → ∀ y, IsPGLAt e a y →
      Type123 π (p ^ f) K y 1) :
    Nat.card ((A ⊔ L) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) = 27 ∧
      (∀ u ∈ (A ⊔ L) ⊓ Subgroup.centralizer (L : Set G), u ^ 3 = 1) ∧
      (A ⊔ L) ⊓ Subgroup.centralizer (L : Set G) ⊓ L = Subgroup.zpowers c ∧
      IsHeisCentral ↥(A ⊔ L) ↥L := by
  classical
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hALeq : A ⊓ L = Subgroup.zpowers c :=
    le_antisymm hAL (Subgroup.zpowers_le.mpr ⟨hcAC.1, hcL⟩)
  have hdec : ∀ a ∈ A, ∃ v : L, (v : G) ^ 3 = 1 ∧ a * v = v * a ∧
      a * (v : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro a ha
    by_cases haC : a ∈ Subgroup.centralizer (L : Set G)
    · exact ⟨1, by simp, by simp, by simpa using haC⟩
    · obtain ⟨y, hy⟩ := hpgl a ha
      obtain ⟨v, hv3, hva, hvC, -⟩ := exists_inner_decomp hK hq hy (h1 a ha haC y hy)
      exact ⟨v, hv3, hva, hvC⟩
  set U : Subgroup G := (A ⊔ L) ⊓ Subgroup.centralizer (L : Set G) with hU
  have hUL : U ⊔ L = A ⊔ L := by
    apply le_antisymm (sup_le inf_le_left le_sup_right)
    refine sup_le (fun a ha => ?_) le_sup_right
    obtain ⟨v, -, -, hvC⟩ := hdec a ha
    have hav : a * (v : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right (inv_mem v.2)), hvC⟩
    have : a = a * (v : G)⁻¹ * v := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hav) (Subgroup.mem_sup_right v.2)
  have hUinf : U ⊓ L = Subgroup.zpowers c := by
    rw [← hLC]
    ext x
    simp only [Subgroup.mem_inf, hU]
    constructor
    · rintro ⟨⟨-, h⟩, h'⟩
      exact ⟨h', h⟩
    · rintro ⟨h', h⟩
      exact ⟨⟨Subgroup.mem_sup_right h', h⟩, h'⟩
  have hcardAL := card_sup_mul_card_inf_of_normal A L
  rw [hALeq, Nat.card_zpowers, hc3, hA27'] at hcardAL
  have hcommUL : ∀ x ∈ U, ∀ y ∈ L, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp hx.2 y hy).symm
  have hcardUL := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U L hcommUL).1
  rw [hUL, hUinf, Nat.card_zpowers, hc3] at hcardUL
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hU27 : Nat.card U = 27 := by
    have : Nat.card U * Nat.card L = 27 * Nat.card L := by rw [← hcardUL, hcardAL]
    exact Nat.eq_of_mul_eq_mul_right hLpos this
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    obtain ⟨huAL, huC⟩ := Subgroup.mem_inf.mp hu
    obtain ⟨a, ha, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp huAL
    obtain ⟨v, hv3, hva, hvC⟩ := hdec a ha
    have hvl : (v : G) * l ∈ Subgroup.zpowers c := by
      rw [← hLC]
      refine Subgroup.mem_inf.mpr ⟨mul_mem v.2 hl, ?_⟩
      have : (v : G) * l = (a * (v : G)⁻¹)⁻¹ * (a * l) := by group
      rw [this]
      exact mul_mem (inv_mem hvC) huC
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvl
    have hal : a * l = (a * (v : G)⁻¹) * c ^ k := by rw [hk]; group
    rw [hal]
    have hca : Commute c a := (hAcomm c hcAC.1 a ha)
    have hcv : Commute c (v : G) := (Subgroup.mem_centralizer_iff.mp hcAC.2 v v.2).symm
    have hc1 : Commute (a * (v : G)⁻¹) (c ^ k) :=
      ((hca.mul_right hcv.inv_right).symm).zpow_right k
    have hc2 : Commute a (v : G)⁻¹ := (Commute.inv_right hva)
    rw [hc1.mul_pow, hc2.mul_pow, hAel.2 a ha, inv_pow, hv3, inv_one, one_mul, one_mul,
      ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hc3',
      _root_.one_zpow]
  have hUnc : ¬ ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
    intro hUc
    obtain ⟨⟨a₁, ha₁m⟩, hpa₁⟩ := hy₁
    obtain ⟨⟨a₂, ha₂m⟩, hpa₂⟩ := hy₂
    obtain ⟨z₁, hz₁⟩ := hpgl a₁ ha₁m
    obtain ⟨z₂, hz₂⟩ := hpgl a₂ ha₂m
    rw [pglHom_apply (⟨a₁, ha₁m⟩ : A) hz₁, QuotientGroup.eq] at hpa₁
    rw [pglHom_apply (⟨a₂, ha₂m⟩ : A) hz₂, QuotientGroup.eq] at hpa₂
    obtain ⟨t₁, ht₁⟩ := hpa₁
    obtain ⟨t₂, ht₂⟩ := hpa₂
    have hy₁z : y₁ = z₁ * GeneralLinearGroup.scalar (Fin 3) t₁ := by rw [ht₁]; group
    have hy₂z : y₂ = z₂ * GeneralLinearGroup.scalar (Fin 3) t₂ := by rw [ht₂]; group
    have hyy : y₁ * y₂ ≠ y₂ * y₁ := by
      intro hyy
      apply hζ1
      have h2 : GeneralLinearGroup.scalar (Fin 3) ζ * y₂ = y₂ := by
        rw [← hζ, hyy, mul_inv_cancel_right]
      have h3 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := mul_eq_right.mp h2
      have h4 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) h3
      simp only [coe_scalar_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one, Units.val_one] at h4
      exact Units.ext h4
    have hz12 : z₁ * z₂ ≠ z₂ * z₁ := by
      intro h
      apply hyy
      rw [hy₁z, hy₂z]
      have hc1 := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t₁ z₂
      have hc2 := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t₂ z₁
      have hc3 := CFSG.ClassicalGroups.UnitaryFlag.commute_scalar t₂
        (GeneralLinearGroup.scalar (Fin 3) t₁)
      calc z₁ * GeneralLinearGroup.scalar (Fin 3) t₁ * (z₂ * GeneralLinearGroup.scalar (Fin 3) t₂)
          = z₁ * (GeneralLinearGroup.scalar (Fin 3) t₁ * z₂) *
            GeneralLinearGroup.scalar (Fin 3) t₂ := by group
        _ = z₁ * z₂ * (GeneralLinearGroup.scalar (Fin 3) t₁ *
            GeneralLinearGroup.scalar (Fin 3) t₂) := by rw [← hc1.eq]; group
        _ = z₂ * z₁ * (GeneralLinearGroup.scalar (Fin 3) t₂ *
            GeneralLinearGroup.scalar (Fin 3) t₁) := by rw [h, hc3.eq]
        _ = z₂ * (z₁ * GeneralLinearGroup.scalar (Fin 3) t₂) *
            GeneralLinearGroup.scalar (Fin 3) t₁ := by group
        _ = z₂ * GeneralLinearGroup.scalar (Fin 3) t₂ *
            (z₁ * GeneralLinearGroup.scalar (Fin 3) t₁) := by rw [hc2.eq]; group
    obtain ⟨v₁, -, -, hv₁C⟩ := hdec a₁ ha₁m
    obtain ⟨v₂, -, -, hv₂C⟩ := hdec a₂ ha₂m
    have hu₁ : a₁ * (v₁ : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left ha₁m) (Subgroup.mem_sup_right (inv_mem v₁.2)), hv₁C⟩
    have hu₂ : a₂ * (v₂ : G)⁻¹ ∈ U :=
      ⟨mul_mem (Subgroup.mem_sup_left ha₂m) (Subgroup.mem_sup_right (inv_mem v₂.2)), hv₂C⟩
    have hcu := hUc _ hu₁ _ hu₂
    obtain ⟨u₁, hu₁d⟩ : ∃ u, u = a₁ * (v₁ : G)⁻¹ := ⟨_, rfl⟩
    obtain ⟨u₂, hu₂d⟩ : ∃ u, u = a₂ * (v₂ : G)⁻¹ := ⟨_, rfl⟩
    rw [← hu₁d, ← hu₂d] at hcu
    have hu₂v₁ : u₂ * v₁ = v₁ * u₂ := by
      rw [hu₂d]
      exact (Subgroup.mem_centralizer_iff.mp hv₂C v₁ v₁.2).symm
    have hu₁v₂ : u₁ * v₂ = v₂ * u₁ := by
      rw [hu₁d]
      exact (Subgroup.mem_centralizer_iff.mp hv₁C v₂ v₂.2).symm
    have ha₁ : a₁ = u₁ * v₁ := by rw [hu₁d]; group
    have ha₂ : a₂ = u₂ * v₂ := by rw [hu₂d]; group
    have hvv : (v₁ : G) * v₂ = v₂ * v₁ := by
      have h := hAcomm a₁ ha₁m a₂ ha₂m
      rw [ha₁, ha₂] at h
      have h' : u₁ * u₂ * (v₁ * v₂) = u₁ * u₂ * (v₂ * v₁) :=
        calc u₁ * u₂ * (v₁ * v₂) = u₁ * (u₂ * v₁) * v₂ := by group
          _ = u₁ * (v₁ * u₂) * v₂ := by rw [hu₂v₁]
          _ = u₁ * v₁ * (u₂ * v₂) := by group
          _ = u₂ * v₂ * (u₁ * v₁) := h
          _ = u₂ * (v₂ * u₁) * v₁ := by group
          _ = u₂ * (u₁ * v₂) * v₁ := by rw [hu₁v₂]
          _ = u₂ * u₁ * (v₂ * v₁) := by group
          _ = u₁ * u₂ * (v₂ * v₁) := by rw [hcu]
      exact mul_left_cancel h'
    have hl : ∀ {a : G} {v : L}, a * (v : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) →
        IsPGLAt e a ((e v : slPi π 3 (p ^ f) K) : GL (Fin 3) K) := by
      intro a v hav
      have h := isPGLAt_mul e (isPGLAt_of_mem_centralizer e hav) (isPGLAt_of_mem e hπ v.2)
      rw [one_mul, inv_mul_cancel_right] at h
      exact h
    obtain ⟨s₁, hs₁⟩ := isPGLAt_inv_mul_mem hK hq hz₁ (hl hv₁C)
    obtain ⟨s₂, hs₂⟩ := isPGLAt_inv_mul_mem hK hq hz₂ (hl hv₂C)
    have hev₁ : ((e v₁ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        z₁ * GeneralLinearGroup.scalar (Fin 3) s₁ := by rw [hs₁]; group
    have hev₂ : ((e v₂ : slPi π 3 (p ^ f) K) : GL (Fin 3) K) =
        z₂ * GeneralLinearGroup.scalar (Fin 3) s₂ := by rw [hs₂]; group
    apply hz12
    apply commute_of_commute_mul_scalar (s := s₁) (t := s₂)
    rw [← hev₁, ← hev₂, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext hvv
  refine ⟨hU27, hU3, hUinf, U.subgroupOf (A ⊔ L), L.subgroupOf (A ⊔ L), ?_, ?_, ?_,
    ⟨Subgroup.subgroupOfEquivOfLe le_sup_right⟩, ?_⟩
  · rw [← Subgroup.subgroupOf_sup inf_le_left le_sup_right, hUL, Subgroup.subgroupOf_self]
  · intro u hu v hv
    rw [Subgroup.mem_subgroupOf] at hu hv
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hu.2 _ hv).symm)
  · apply isHeisThree_of
    · rw [← hU27]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    · intro x
      apply Subtype.ext
      apply Subtype.ext
      have := hU3 _ (Subgroup.mem_subgroupOf.mp x.2)
      simpa using this
    · intro hcomm
      apply hUnc
      intro u hu u' hu'
      have h := hcomm.is_comm.comm ⟨⟨u, hu.1⟩, Subgroup.mem_subgroupOf.mpr hu⟩
        ⟨⟨u', hu'.1⟩, Subgroup.mem_subgroupOf.mpr hu'⟩
      exact congrArg (fun x : ↥(U.subgroupOf (A ⊔ L)) => ((x : ↥(A ⊔ L)) : G)) h
  · rw [← inf_subgroupOf, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((inf_le_right : U ⊓ L ≤ L).trans le_sup_right)).toEquiv.symm, hUinf, Nat.card_zpowers, hc3]

theorem alt411_two (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (e : L ≃* slPi π 3 (p ^ f) K) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAt e a y) (hAL : A ⊓ L ≤ Subgroup.zpowers c)
    {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHom hK hq A hpgl).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (h1 : ∀ a ∈ A, a ∉ Subgroup.centralizer (L : Set G) → ∀ y, IsPGLAt e a y →
      Type123 π (p ^ f) K y 1) :
    Nat.card A = 27 ∧ IsHeisCentral ↥(A ⊔ L) ↥L := by
  obtain ⟨hcL, hLC⟩ := mem_and_inf_centralizer_eq hK hq e hA hc3 hAc
  obtain ⟨hA27', -⟩ := card_eq_of_pgl hK hq hA hA27 hc3 hAc hpgl
  exact ⟨hA27', (heis_of_type1 hK hq e hA.1 hA27' hc3 hcL hLC hAc hpgl hAL hy₁ hy₂ hζ1 hζ
    h1).2.2.2⟩

end Heis

end CFSG.RankThree.PartTwo.Sec4
