module

public import CFSG.LocalAnalysis.SteinbergSFLinearThreeLargeElementaryExclusion
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelSelector
public import CFSG.LocalAnalysis.SteinbergCDEvenOrderFourTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryAutomorphismHermitian
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearInnerFixed
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace LinearUnitaryThree

open scoped MatrixGroups
open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section SL2

variable {k : Type*} [Field k]

theorem card_SL_two [Finite k] : Nat.card SL(2, k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite k
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := k)
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_units] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [← Nat.card_eq_fintype_card] at h
  set q := Nat.card k
  have hq : 2 ≤ q := Finite.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h, show q ^ 2 - q = q * (q - 1) by rw [Nat.mul_sub_one, ← pow_two]]
  ring

theorem exists_mul_ne_SL_two : ∃ a b : SL(2, k), a * b ≠ b * a := by
  set a : SL(2, k) := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩
  set b : SL(2, k) := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩
  refine ⟨a, b, fun h => ?_⟩
  have h00 := congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h
  change ((a : Matrix (Fin 2) (Fin 2) k) * b) 0 0 = ((b : Matrix (Fin 2) (Fin 2) k) * a) 0 0
    at h00
  simp [a, b, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem isSimpleGroup_SL_two [Finite k] [CharP k 2] (h4 : 4 ≤ Nat.card k) :
    IsSimpleGroup SL(2, k) := by
  have := Fintype.ofFinite k
  have hs : ∃ s : Finset k, s.card = 4 := by
    have hle : 4 ≤ (Finset.univ : Finset k).card := by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
    exact ⟨s, hs⟩
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := k) (n := 2) le_rfl (Or.inr hs)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := k)).symm.isSimpleGroup

end SL2

theorem eq_of_mul_sq_sub_one_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  have hle : ∀ {x y : ℕ}, 1 ≤ x → 1 ≤ y → x * (x ^ 2 - 1) ≤ y * (y ^ 2 - 1) → x ≤ y := by
    intro x y hx hy hxy
    by_contra hlt
    push Not at hlt
    have hsq : y ^ 2 < x ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
    have hy1 : 1 ≤ y ^ 2 := Nat.one_le_pow _ _ hy
    have : y * (y ^ 2 - 1) < x * (x ^ 2 - 1) :=
      Nat.mul_lt_mul_of_le_of_lt hlt.le (by omega) (by omega)
    omega
  exact le_antisymm (hle ha hb h.le) (hle hb ha h.ge)

theorem sixty_le_two_pow_mul {n : ℕ} (hn : 2 ≤ n) : 60 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
  calc 60 = 4 * (16 - 1) := by norm_num
    _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h4 (by omega)

theorem fixed_SL_two_root {D P : Type*} [Group D] [Group P] {K k : Type*} [Field K] [Field k]
    {n m : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hk : Nat.card k = 2 ^ m)
    {α : MulAut D} {β : MulAut P} (ψ : D ≃* P) (hψ : ∀ d, ψ (α d) = β (ψ d))
    (j : SL(2, k) →* P) (hj : Function.Injective j)
    (hjr : j.range = fixedSubgroup β) {S : Subgroup D} (hSα : S ≤ fixedSubgroup α)
    (hS : (S.subgroupOf (fixedSubgroup α)).Normal) (κ : S ≃* SL(2, K)) :
    m = n ∧ S = fixedSubgroup α ∧ S.map ψ.toMonoidHom = fixedSubgroup β := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : 2 ≤ Nat.card k := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [hk, h, pow_zero] at hk2
      omega
    · exact h
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hm hk
  have hmap : (fixedSubgroup α).map ψ.toMonoidHom = fixedSubgroup β :=
    TauCeti.map_fixedSubgroup_eq ψ (MonoidHom.ext hψ)
  let eF : fixedSubgroup α ≃* SL(2, k) :=
    (((fixedSubgroup α).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr (hmap.trans hjr.symm))).trans (MonoidHom.ofInjective hj).symm
  have hcardS : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr κ.toEquiv, card_SL_two, hK]
  have hcardF : Nat.card (fixedSubgroup α) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
    rw [Nat.card_congr eF.toEquiv, card_SL_two, hk]
  have : Finite (fixedSubgroup α) := Finite.of_equiv _ eF.symm.toEquiv
  have hle : Nat.card S ≤ Nat.card (fixedSubgroup α) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hSα)
  have h60 := sixty_le_two_pow_mul hn
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have h1 : m = 1 := by omega
    rw [hcardS, hcardF, h1] at hle
    norm_num at hle
    omega
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have := isSimpleGroup_SL_two (k := k) h4
  have : IsSimpleGroup (fixedSubgroup α) := eF.isSimpleGroup
  have hSeq : S = fixedSubgroup α := by
    rcases hS.eq_bot_or_eq_top with h | h
    · exfalso
      have h1 : S = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hSα hx⟩ : fixedSubgroup α) ∈ S.subgroupOf (fixedSubgroup α) := hx
        rw [h, Subgroup.mem_bot] at hx'
        exact (Subgroup.mem_bot).2 (congrArg Subtype.val hx')
      rw [h1, Subgroup.card_bot] at hcardS
      omega
    · exact le_antisymm hSα (Subgroup.subgroupOf_eq_top.1 h)
  have hmn : m = n := by
    have hc : 2 ^ m * ((2 ^ m) ^ 2 - 1) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [← hcardF, ← hcardS, hSeq]
    exact Nat.pow_right_injective le_rfl
      (eq_of_mul_sq_sub_one_eq (Nat.one_le_two_pow) (Nat.one_le_two_pow) hc)
  exact ⟨hmn, hSeq, by rw [hSeq, hmap]⟩

section LinearFixed

open LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_planeIsometryEquivSL)
open CFSG.ComponentClassification.OutcomeLocal (dotForm_restrict_isAlt
  dotForm_restrict_nondegenerate finrank_dotForm_ker oneRestrictEquiv)

variable (F : Type*) [Field F] [CharP F 2]

@[expose] def orthSL :
    matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →*
      SL(3, F) where
  toFun g := ⟨(g : GL (Fin 3) F), det_eq_one_of_mem (by simp) g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def orthProj :
    matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →* projectiveSL 3 F :=
  (proj 3 F).comp (orthSL F)

variable {F}

omit [CharP F 2] in
theorem slThree_ext {A B : SL(3, F)} (h : (A : Matrix (Fin 3) (Fin 3) F) = B) : A = B :=
  Subtype.ext h

theorem coe_orthSL (g : matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    ((orthSL F g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  rfl

omit [CharP F 2] in
theorem mem_orth_iff {g : GL (Fin 3) F} :
    g ∈ matrixIsometryGroup ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ↔
      (g : Matrix (Fin 3) (Fin 3) F)ᵀ * g = 1 := by
  rw [mem_matrixIsometryGroup, Units.val_one, Matrix.mul_one]

theorem orthProj_injective : Function.Injective (orthProj F) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [orthProj, MonoidHom.comp_apply, proj_eq_one_iff] at hg
  obtain ⟨c, hc3, hgc⟩ := mem_scalars.1 hg
  rw [coe_orthSL] at hgc
  have horth := mem_orth_iff.1 g.2
  rw [hgc, scalar_apply, diagonal_transpose, diagonal_mul_diagonal] at horth
  have hc2 : (c : F) * c = 1 := by
    have := congrFun (congrFun horth 0) 0
    simpa using this
  have hc1 : c = 1 := by
    have h2 : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, sq, hc2, Units.val_one])
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, h2, inv_one, one_mul]
  apply Subtype.ext
  apply Units.ext
  rw [hgc, hc1, Units.val_one, map_one]
  rfl

theorem range_orthProj : (orthProj F).range = fixedSubgroup (dualAut 3 F) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    change dualAut 3 F (proj 3 F (orthSL F g)) = proj 3 F (orthSL F g)
    rw [dualAut_proj]
    congr 1
    apply Subtype.ext
    have horth := mem_orth_iff.1 g.2
    rw [Matrix.SpecialLinearGroup.coe_transpose, coe_orthSL]
    have hinv : ((orthSL F g)⁻¹ : SL(3, F)) = (orthSL F g).transpose := by
      refine inv_eq_of_mul_eq_one_right (slThree_ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul (orthSL F g),
        Matrix.SpecialLinearGroup.coe_transpose, coe_orthSL, Matrix.SpecialLinearGroup.coe_one]
      exact mul_eq_one_comm.1 horth
    rw [hinv, Matrix.SpecialLinearGroup.coe_transpose, coe_orthSL, transpose_transpose]
  · intro hx
    obtain ⟨A, rfl⟩ := proj_surjective 3 F x
    change dualAut 3 F (proj 3 F A) = proj 3 F A at hx
    rw [dualAut_proj, proj_eq_proj_iff] at hx
    obtain ⟨c, hc3, hAc⟩ := mem_scalars.1 hx
    have hT : ((A⁻¹ : SL(3, F)).transpose)⁻¹ = A.transpose := by
      refine inv_eq_of_mul_eq_one_right (slThree_ext ?_)
      rw [Matrix.SpecialLinearGroup.coe_mul A⁻¹.transpose, Matrix.SpecialLinearGroup.coe_transpose,
        Matrix.SpecialLinearGroup.coe_transpose, ← transpose_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        transpose_one]
    have hAc' : (A : Matrix (Fin 3) (Fin 3) F)ᵀ * A = scalar (Fin 3) (c : F) := by
      rw [← hAc, hT, Matrix.SpecialLinearGroup.coe_mul A.transpose,
        Matrix.SpecialLinearGroup.coe_transpose]
    clear hAc
    set B : SL(3, F) := scalarElement c hc3 * A with hB
    have hBm : (B : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) (c : F) * A := rfl
    have hc3' : (c : F) * c * c = 1 := by
      have := congrArg Units.val hc3
      simpa [pow_succ] using this
    have hsc : scalar (Fin 3) (c : F) = (c : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [scalar_apply, smul_one_eq_diagonal]
    have hBorth : (B : Matrix (Fin 3) (Fin 3) F)ᵀ * B = 1 := by
      rw [hBm, hsc, smul_mul, Matrix.one_mul, transpose_smul, smul_mul, Matrix.mul_smul, hAc',
        hsc, smul_smul, smul_smul, hc3', one_smul]
    refine ⟨⟨Matrix.SpecialLinearGroup.toGL B, mem_orth_iff.2 hBorth⟩, ?_⟩
    change proj 3 F (orthSL F _) = proj 3 F A
    have hBB : orthSL F ⟨Matrix.SpecialLinearGroup.toGL B, mem_orth_iff.2 hBorth⟩ = B :=
      Subtype.ext rfl
    rw [hBB, hB, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars c hc3), one_mul]

theorem exists_SL_two_fixed_dualAut {F : Type} [Field F] [CharP F 2] :
    ∃ j : SL(2, F) →* projectiveSL 3 F,
      Function.Injective j ∧ j.range = fixedSubgroup (dualAut 3 F) := by
  have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
  obtain ⟨eSL⟩ := exists_planeIsometryEquivSL _ (dotForm_restrict_isAlt (k := F) (n := 3))
    (dotForm_restrict_nondegenerate h3) (finrank_dotForm_ker h3)
  set e := (oneRestrictEquiv (k := F) h3).trans eSL
  refine ⟨(orthProj F).comp e.symm.toMonoidHom, orthProj_injective.comp e.symm.injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.symm.surjective, Subgroup.map_top,
    range_orthProj]

end LinearFixed

section LinearCases

open LinearFlag CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.CatalogueBHigherLinearField CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (le_of_normal_of_centralizer_commute
  eq_of_le_of_normal ne_bot_of_isSimpleGroup conj_transport card_unitaryPSU_three)

variable {F : Type} [Field F]

theorem not_dvd_seventy_two {n : ℕ} (hn : 2 ≤ n) : ¬ 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 72 := by
  intro h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · obtain rfl : n = 2 := by omega
    norm_num at h
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 8 * 63 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.mul_le_mul h8 (by omega)
    have := Nat.le_of_dvd (by norm_num) h
    omega

theorem field_case_orderOf_four [Finite F] [CharP F 2] {τ : F ≃+* F}
    {T : Subgroup (MulAut (projectiveSL 3 F))}
    (hT : T ≤ inner (projectiveSL 3 F) ⊓ centralizer {fieldAut 3 F τ})
    (hTn : (T.subgroupOf (inner (projectiveSL 3 F) ⊓ centralizer {fieldAut 3 F τ})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) : ∃ x : T, orderOf x = 4 := by
  obtain ⟨-, ⟨e, -⟩, hNinn, -, hNC, hNnormal, hcentN⟩ :=
    linear_quadratic_field_full_centralizer_rigidity τ (n := 3) le_rfl
  have hNF := le_inf hNinn hNC
  have hle : T ≤ (subfieldConj 3 τ).range :=
    le_of_normal_of_centralizer_commute hT hTn hTnab hNF
      (fun t ht => (normal_subgroupOf_iff_le_normalizer hNC).1 hNnormal (hT ht).2)
      (fun x _ y _ hxN hyN => by
        rw [hcentN] at hxN hyN
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hxN
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyN
        exact (Commute.zpow_zpow_self _ i j).eq)
  have hsimp : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) (fixedField F τ)) :=
    (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl le_rfl)).2.1
  have : IsSimpleGroup (subfieldConj 3 τ).range :=
    (e.symm.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _).symm).isSimpleGroup
  have heq := eq_of_le_of_normal hle hNF hTn (ne_bot_of_isSimpleGroup T)
  have h2 : (2 : fixedField F τ) = 0 := Subtype.ext (by
    change (2 : F) = 0
    exact CharTwo.two_eq_zero)
  obtain ⟨y, -, hy⟩ := SteinbergCD.exists_orderOf_eq_four_projectiveSL h2 (le_refl 3)
  have hmem : (e (proj 3 (fixedField F τ) y) : MulAut (projectiveSL 3 F)) ∈ T := by
    rw [heq]
    exact (e (proj 3 (fixedField F τ) y)).2
  have ho : orderOf (e (proj 3 (fixedField F τ) y) : MulAut (projectiveSL 3 F)) = 4 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact ho

theorem graph_field_case_false {e : ℕ} (h : UnitaryFieldData 2 e F) {σ : F ≃+* F}
    (hσ : ∀ x, σ x = h.bar x) {T : Subgroup (MulAut (projectiveSL 3 F))}
    (hT : T ≤ inner (projectiveSL 3 F) ⊓ centralizer {fieldAut 3 F σ * dualAut 3 F})
    (hTn : (T.subgroupOf
      (inner (projectiveSL 3 F) ⊓ centralizer {fieldAut 3 F σ * dualAut 3 F})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) (h4 : ∀ x : T, orderOf x ≠ 4)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card T = 2 ^ n * ((2 ^ n) ^ 2 - 1)) : False := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ι, -⟩, hNinn, -, hNC, hNnormal, hcentN⟩ :=
    linear_graph_field_full_centralizer_rigidity h (n := 3) le_rfl σ hσ
  have hNF := le_inf hNinn hNC
  have hle : T ≤ (unitarySU 2 e F 3).map (conjAut 3 F) :=
    le_of_normal_of_centralizer_commute hT hTn hTnab hNF
      (fun t ht => (normal_subgroupOf_iff_le_normalizer hNC).1 hNnormal (hT ht).2)
      (fun x _ y _ hxN hyN => by
        rw [hcentN] at hxN hyN
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hxN
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hyN
        exact (Commute.zpow_zpow_self _ i j).eq)
  have hcardN : Nat.card ((unitarySU 2 e F 3).map (conjAut 3 F)) = Nat.card (unitaryPSU h 3) :=
    (Nat.card_congr ι.toEquiv).symm
  by_cases he : e = 1
  · subst he
    have hdvd : Nat.card T ∣ Nat.card (unitaryPSU h 3) := by
      rw [← hcardN]
      exact Subgroup.card_dvd_of_le hle
    rw [card_unitaryPSU_three h, hcard] at hdvd
    exact not_dvd_seventy_two hn hdvd
  · have hnq : ((3 : ℕ), 2 ^ e) ≠ (3, 2) := by
      intro h32
      simp only [Prod.mk.injEq, true_and] at h32
      exact he (Nat.pow_right_injective (le_refl 2) (by simpa using h32))
    have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 e h.card_eq_sq 3
      le_rfl hnq
    have : IsSimpleGroup ((unitarySU 2 e F 3).map (conjAut 3 F)) :=
      (ι.symm.trans (unitaryPSUEquiv h (by omega))).isSimpleGroup
    have heq := eq_of_le_of_normal hle hNF hTn (ne_bot_of_isSimpleGroup T)
    obtain ⟨y, -, hy⟩ := SteinbergCD.exists_orderOf_eq_four_unitaryPSU h (le_refl 3)
    have hmem : (ι (unitaryProj h 3 y) : MulAut (projectiveSL 3 F)) ∈ T := by
      rw [heq]
      exact (ι (unitaryProj h 3 y)).2
    have ho : orderOf (ι (unitaryProj h 3 y) : MulAut (projectiveSL 3 F)) = 4 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hy]
    refine h4 ⟨_, hmem⟩ ?_
    rw [← Subgroup.orderOf_coe]
    exact ho

theorem eq_conj_dualAut_of_cases {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {β : MulAut (projectiveSL 3 F)} (hβ2 : β ^ 2 = 1) (hβout : β ∉ inner (projectiveSL 3 F))
    {T : Subgroup (MulAut (projectiveSL 3 F))}
    (hT : T ≤ inner (projectiveSL 3 F) ⊓ centralizer {β})
    (hTn : (T.subgroupOf (inner (projectiveSL 3 F) ⊓ centralizer {β})).Normal)
    [IsSimpleGroup T] (hTnab : ∃ a b : T, a * b ≠ b * a) (h4 : ∀ x : T, orderOf x ≠ 4)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card T = 2 ^ n * ((2 ^ n) ^ 2 - 1)) :
    ∃ H : GL (Fin 3) F, β = conjAut 3 F H * dualAut 3 F * (conjAut 3 F H)⁻¹ := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hF
  have htrans : ∀ {γ g : MulAut (projectiveSL 3 F)}, β = g * γ * g⁻¹ →
      ∃ T' : Subgroup (MulAut (projectiveSL 3 F)),
        T' ≤ inner (projectiveSL 3 F) ⊓ centralizer {γ} ∧
        (T'.subgroupOf (inner (projectiveSL 3 F) ⊓ centralizer {γ})).Normal ∧
        IsSimpleGroup T' ∧ (∃ a b : T', a * b ≠ b * a) ∧ (∀ x : T', orderOf x ≠ 4) ∧
        Nat.card T' = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    intro γ g hβγ
    obtain ⟨h1, h2⟩ := conj_transport hβγ hT hTn
    set e := T.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    refine ⟨_, h1, h2, e.symm.isSimpleGroup, ?_, fun x hx => h4 (e.symm x) ?_,
      (Nat.card_congr e.toEquiv).symm.trans hcard⟩
    · obtain ⟨a, b, hab⟩ := hTnab
      exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩
    · rw [MulEquiv.orderOf_eq, hx]
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, τ, ε, hε, rfl⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exfalso
    rw [pow_zero, mul_one] at hβ2 hβout
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hβ2 hβout
      exact hβout (EvenLinearSL.conjAut_mem_inner_of_sq_eq_one hf hF A hβ2)
    obtain ⟨-, -, H, hβH⟩ := even_linear_field_involution_descent hf hF le_rfl A τ hτ hβ2
    obtain ⟨T', h1, h2, h3, h5, h6, -⟩ := htrans hβH
    obtain ⟨x, hx⟩ := field_case_orderOf_four h1 h2 h5
    exact h6 x hx
  · rw [pow_one] at hβ2 hβout ⊢
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hβ2 hβout ⊢
      obtain ⟨-, ⟨H₀, C, -, hβ, hC⟩, -⟩ :=
        UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hF le_rfl A hβ2
      rcases hC with ⟨h1C, -⟩ | ⟨r, hr, -, -⟩
      · refine ⟨H₀, ?_⟩
        rw [hβ, show C = 1 from Units.ext h1C, map_one, one_mul]
      · omega
    · exfalso
      obtain ⟨hfe, hτx, B, hβB⟩ :=
        UnitaryHigher.linear_graph_field_involution_descent Nat.prime_two hf hF le_rfl A τ hτ hβ2
      obtain ⟨m, hm⟩ := hfe
      have he : 1 ≤ f / 2 := by omega
      have hFe : Nat.card F = 2 ^ (2 * (f / 2)) := by rw [hF]; congr 1; omega
      have h : UnitaryFieldData 2 (f / 2) F := ⟨Nat.prime_two, he, hFe⟩
      obtain ⟨T', h1, h2, h3, h5, h6, h7⟩ := htrans (γ := fieldAut 3 F τ * dualAut 3 F)
        (g := conjAut 3 F B) hβB
      exact graph_field_case_false h (fun x => by rw [hτx, h.bar_apply]) h1 h2 h5 h6 hn h7

end LinearCases

section Tools

@[expose] def slTwoRingEquiv {K F : Type*} [CommRing K] [CommRing F] (e : K ≃+* F) :
    SL(2, K) ≃* SL(2, F) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' := map_mul _

theorem exists_sylow_eq_of_card {G : Type*} [Group G] [Finite G] {a : ℕ}
    (hG : ordProj[2] (Nat.card G) = a) (P : Subgroup G) (hP : Nat.card P = a) :
    ∃ Q : Sylow 2 G, (Q : Subgroup G) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨Sylow.ofCard P (by rw [hP, hG]), rfl⟩

theorem ordProj_eq_of_sylow {G : Type*} [Group G] [Finite G] (Q : Sylow 2 G) :
    ordProj[2] (Nat.card G) = Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (Sylow.card_eq_multiplicity Q).symm

theorem transport_data {D P : Type*} [Group D] [Group P] (η : D ≃* P) {α : MulAut D}
    (hα : orderOf α = 2) :
    orderOf (MulAut.congr η α) = 2 ∧ (MulAut.congr η α) ^ 2 = 1 ∧ MulAut.congr η α ≠ 1 ∧
      ∀ x, MulAut.congr η α x = η (α (η.symm x)) := by
  have hβ : orderOf (MulAut.congr η α) = 2 := by rw [MulEquiv.orderOf_eq]; exact hα
  refine ⟨hβ, by rw [← hβ]; exact pow_orderOf_eq_one _, fun h => ?_, fun x => rfl⟩
  rw [h, orderOf_one] at hβ
  exact absurd hβ (by norm_num)

end Tools

section LinearModel

open LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed map_fixed_transport
  conj_map_le_and_normal not_mem_inner_of_normal_simple_fixed conj_injective_of_center_eq_bot)

theorem linear_three_fixed_normal_SL_two {n m : ℕ} {K : Type*} {F : Type} [Field K] [Field F]
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ m) {D : Type*} [Group D]
    (η : D ≃* projectiveSL 3 F) (α : MulAut D) (hα : orderOf α = 2) (S : Subgroup D)
    (hSα : S ≤ fixedSubgroup α) (hSn : (S.subgroupOf (fixedSubgroup α)).Normal)
    (κ : S ≃* SL(2, K)) :
    m = n ∧ S = fixedSubgroup α ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      (∃ H : GL (Fin 3) F,
        (∀ d, conjAut 3 F H (η (α d)) = dualAut 3 F (conjAut 3 F H (η d))) ∧
        S.map (η.trans (conjAut 3 F H)).toMonoidHom = fixedSubgroup (dualAut 3 F)) ∧
      ordProj[2] (Nat.card D) = (2 ^ n) ^ 3 ∧
      (∀ U : Subgroup D, IsElementaryAbelian 2 U → Nat.card U = (2 ^ n) ^ 2 →
        ¬ U.map α.toMonoidHom ≤ U) ∧
      ∀ P : Subgroup D, Nat.card P = (2 ^ n) ^ 3 → ∃ Q : Sylow 2 D, (Q : Subgroup D) = P := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have hm : 1 ≤ m := by
    have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [hF, h, pow_zero] at h2
      omega
    · exact h
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hm hF
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := isSimpleGroup_SL_two (k := K) hK4
  have : IsSimpleGroup S := κ.isSimpleGroup
  have hSnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_SL_two (k := K)
    exact ⟨κ.symm a, κ.symm b, fun h => hab (κ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hS4 : ∀ x : S, orderOf x ≠ 4 := fun x hx =>
    SteinbergCD.SL_two_orderOf_ne_four CharTwo.two_eq_zero (κ x) (by rw [MulEquiv.orderOf_eq, hx])
  have hcardS : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr κ.toEquiv, card_SL_two, hK]
  obtain ⟨-, hα'2, hα'1, hα'⟩ := transport_data η hα
  set α' := MulAut.congr η α with hα'def
  obtain ⟨hS'fix, hS'n⟩ := map_fixed_transport η (α := α) hSα hSn hα'
  set eS := S.equivMapOfInjective η.toMonoidHom η.injective with heS
  have : IsSimpleGroup (S.map η.toMonoidHom) := eS.symm.isSimpleGroup
  have hS'nab : ∃ a b : S.map η.toMonoidHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eS a, eS b, fun h => hab (eS.injective (by rw [map_mul, map_mul, h]))⟩
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 3) F) :=
    (CFSG.LinearGroups.linear_projective_simple (by omega) (Or.inl le_rfl)).2.1
  have : IsSimpleGroup (projectiveSL 3 F) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.isSimpleGroup
  have hPnab : ∃ x y : projectiveSL 3 F, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hS'nab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hZ : Subgroup.center (projectiveSL 3 F) = ⊥ :=
    center_eq_bot_of_isSimpleGroup hPnab
  have hconj := conj_injective_of_center_eq_bot hZ
  have hout : α' ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (projectiveSL 3 F) :=
    not_mem_inner_of_normal_simple_fixed le_rfl hm hF hα'2 hα'1 hZ hS'fix hS'n hS'nab
  obtain ⟨hTF, hTn⟩ := conj_map_le_and_normal hconj hS'fix hS'n
  set eT := (S.map η.toMonoidHom).equivMapOfInjective _ hconj with heT
  have : IsSimpleGroup ((S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) := eT.symm.isSimpleGroup
  have hTnab : ∃ a b : (S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hS'nab
    exact ⟨eT a, eT b, fun h => hab (eT.injective (by rw [map_mul, map_mul, h]))⟩
  have hT4 : ∀ x : (S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)), orderOf x ≠ 4 :=
    fun x hx => hS4 (eS.symm (eT.symm x)) (by rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hx])
  have hcardT : Nat.card ((S.map η.toMonoidHom).map
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F))) =
        2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [← Nat.card_congr eT.toEquiv, ← Nat.card_congr eS.toEquiv, hcardS]
  obtain ⟨H₀, hH₀⟩ := eq_conj_dualAut_of_cases hm hF hα'2 hout hTF hTn hTnab hT4 hn hcardT
  have hψα : ∀ d, conjAut 3 F H₀⁻¹ (η (α d)) = dualAut 3 F (conjAut 3 F H₀⁻¹ (η d)) := by
    intro d
    have h1 : η (α d) = α' (η d) := by rw [hα', MulEquiv.symm_apply_apply]
    rw [h1, hH₀, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_dualAut (F := F)
  obtain ⟨hmn, hSeq, hSmap⟩ :=
    fixed_SL_two_root hK hn hF (η.trans (conjAut 3 F H₀⁻¹)) hψα j hj hjr hSα hSn κ
  have hαout : α ∉ (MulAut.conj : D →* MulAut D).range := by
    rintro ⟨d, hd⟩
    apply hout
    refine ⟨η d, ?_⟩
    ext x
    rw [hα', ← hd, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hord : ordProj[2] (Nat.card D) = (2 ^ n) ^ 3 := by
    obtain ⟨-, -, -, -, -, -, -, ⟨Q, hQ⟩, hQcard⟩ :=
      linear_order 2 (2 ^ m) hF (n := 3) (by norm_num)
    have hcardP : Nat.card (projectiveSL 3 F) = Nat.card D := (Nat.card_congr η.toEquiv).symm
    have h1 := ordProj_eq_of_sylow Q
    rw [hcardP, hQ, hQcard, hmn] at h1
    exact h1
  have : Finite D := Finite.of_equiv _ η.symm.toEquiv
  refine ⟨hmn, hSeq, hαout, ⟨H₀⁻¹, hψα, hSmap⟩, hord, fun U hU hUcard hUα => ?_,
    exists_sylow_eq_of_card hord⟩
  have := Fintype.ofFinite K
  have := Fintype.ofFinite F
  have eKF : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF, hmn])
  exact (linearThreeInvolution_isEmpty_mulEquiv_of_mulAut α hα S hSα
    ⟨κ.trans (slTwoRingEquiv eKF)⟩ U (by rw [hUcard, hF, hmn]) hUα).false η

end LinearModel

section UnitaryVocabulary

open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OutcomeLocal (primeFormOneEquiv primeFormOneEquiv_mk)

variable {p f : ℕ} {F : Type} [Field F]

@[expose] noncomputable def barEquiv (h : UnitaryFieldData p f F) : F ≃+* F :=
  RingEquiv.ofBijective h.bar (Function.Involutive.bijective h.bar_bar)

theorem mem_unitaryIsom3_of_mem (h : UnitaryFieldData p f F) {A : GL (Fin 3) F}
    (hA : A ∈ primeFormUnitary h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    A ∈ unitaryIsom3 h := by
  have h1 := mem_primeFormUnitary.1 hA
  rw [Units.val_one, Matrix.mul_one] at h1
  exact h1

theorem primeFormOneEquiv_primeFormConjAut (h : UnitaryFieldData p f F)
    (A : primeFormUnitary h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (x : primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    primeFormOneEquiv h 3 (primeFormConjAut h _ A x) =
      psuConj h ⟨A, mem_unitaryIsom3_of_mem h A.2⟩ (primeFormOneEquiv h 3 x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hg : (g : GL (Fin 3) F) ∈ unitarySU p f F 3 := by
      rw [← CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq]
      exact g.2
    rw [primeFormConjAut_mk, primeFormOneEquiv_mk h g ⟨g, hg⟩ rfl]
    have hAg : (A : GL (Fin 3) F) * g * (A : GL (Fin 3) F)⁻¹ ∈ unitarySU p f F 3 := by
      rw [← CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq]
      exact (primeFormConjSU h _ A g).2
    rw [primeFormOneEquiv_mk h _ ⟨_, hAg⟩ rfl]
    rfl

theorem primeFormOneEquiv_primeFormFieldAut (h : UnitaryFieldData p f F) (σ : F ≃+* F)
    (x : primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    primeFormOneEquiv h 3 (primeFormFieldAut h isPrimeFormGram_one σ x) =
      psuField h σ (primeFormOneEquiv h 3 x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>
    have hg : (g : GL (Fin 3) F) ∈ unitarySU p f F 3 := by
      rw [← CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq]
      exact g.2
    rw [primeFormFieldAut_mk, primeFormOneEquiv_mk h g ⟨g, hg⟩ rfl]
    have hσg : glAut σ (g : GL (Fin 3) F) ∈ unitarySU p f F 3 := by
      rw [← CFSG.ComponentClassification.OutcomeLocal.gramSU_one_eq]
      exact (primeFormFieldSU h isPrimeFormGram_one σ g).2
    rw [primeFormOneEquiv_mk h _ ⟨_, hσg⟩ rfl]
    rfl

end UnitaryVocabulary

section UnitaryCases

open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OutcomeLocal (primeFormOneEquiv mulAut_congr_conj)
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (autFixed mem_autFixed
  conj_injective_of_center_eq_bot)
open CFSG.ComponentClassification.UnbalancingLocal
  (even_unitary_involution_centralizers_component_free)

variable {e : ℕ} {F : Type} [Field F]

theorem unitary_not_mem_inner_of_normal_simple_fixed (h : UnitaryFieldData 2 e F) (he : 2 ≤ e)
    {α : MulAut (unitaryPSU h 3)} (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1)
    (hZ : Subgroup.center (unitaryPSU h 3) = ⊥) {S : Subgroup (unitaryPSU h 3)}
    (hS : S ≤ autFixed α) (hSn : (S.subgroupOf (autFixed α)).Normal) [IsSimpleGroup S]
    (hSnab : ∃ a b : S, a * b ≠ b * a) :
    α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3) := by
  rintro ⟨x, rfl⟩
  have hq : ¬((3 : ℕ) = 3 ∧ 2 ^ e = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  have hconj := conj_injective_of_center_eq_bot hZ
  have hx2 : x ^ 2 = 1 := hconj (by rw [map_pow, hα2, map_one])
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hα1 (map_one _)
  have hox : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hfix : autFixed (MulAut.conj x) = Subgroup.centralizer {x} := by
    ext y
    rw [mem_autFixed, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h'
      calc y * x = x * y * x⁻¹ * x := by rw [h']
        _ = x * y := by group
    · intro h'
      rw [← h']
      group
  rw [hfix] at hS hSn
  have : IsSimpleGroup (S.subgroupOf (Subgroup.centralizer {x})) :=
    (Subgroup.subgroupOfEquivOfLe hS).isSimpleGroup
  have hBnab : ∃ a b : S.subgroupOf (Subgroup.centralizer {x}), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    set e' := Subgroup.subgroupOfEquivOfLe hS
    exact ⟨e'.symm a, e'.symm b, fun h' => hab (e'.symm.injective (by rw [map_mul, map_mul, h']))⟩
  exact even_unitary_involution_centralizers_component_free h (le_refl 3) hq x hox _
    ⟨isQuasisimple_of_isSimpleGroup hBnab, hSn.isSubnormal⟩

theorem eq_conj_bar_of_not_mem_inner (h : UnitaryFieldData 2 e F) (he : 2 ≤ e)
    {β : MulAut (unitaryPSU h 3)} (hβ : orderOf β = 2)
    (hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 3)) :
    ∃ H : unitaryIsom3 h, β = psuConj h H * psuField h (barEquiv h) * (psuConj h H)⁻¹ := by
  have hq : ¬((3 : ℕ) = 3 ∧ 2 ^ e = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    omega
  set ε := primeFormOneEquiv h 3 with hεdef
  set β₁ := MulAut.congr ε.symm β with hβ₁def
  have hβ₁ : orderOf β₁ = 2 := by rw [hβ₁def, MulEquiv.orderOf_eq]; exact hβ
  have hββ₁ : β = MulAut.congr ε β₁ := by
    ext y
    simp [hβ₁def, MulAut.congr_apply]
  obtain ⟨hcases, hrefl, -, -⟩ :=
    even_unitary_involution_matrix_lifts h isPrimeFormGram_one (le_refl 3) hq β₁ hβ₁
  rcases hcases with hF | hF
  · exfalso
    obtain ⟨s, -, -, hs⟩ := hrefl hF
    apply hβout
    rw [hββ₁, hs, primeFormConjHom_eq_conj, mulAut_congr_conj]
    exact ⟨_, rfl⟩
  · obtain ⟨-, H, C₀, hC₀, hcase, -, -, hHgram, -, ⟨θ, hθmk, hθα⟩, -⟩ :=
      even_unitary_antiunitary_involution_descent h isPrimeFormGram_one (le_refl 3) hq β₁ hβ₁ hF
    have hC₀1 : (C₀ : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rcases hcase with h1 | ⟨r, hr, -⟩
      · exact h1
      · omega
    obtain rfl : C₀ = 1 := Units.ext hC₀1
    have hHU : H ∈ primeFormUnitary h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
      mem_primeFormUnitary.2 hHgram
    have hθ : ∀ x, θ x = primeFormConjAut h _ ⟨H, hHU⟩ x := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H g =>
        rw [primeFormConjAut_mk]
        exact hθmk g _ rfl
    have hφ : primeFormFieldFactor h isPrimeFormGram_one (le_refl 3) hq β₁ = barEquiv h :=
      RingEquiv.ext hF
    set H' : unitaryIsom3 h := ⟨H, mem_unitaryIsom3_of_mem h hHU⟩ with hH'
    have hεθ : ∀ x, ε (θ x) = psuConj h H' (ε x) := fun x => by
      rw [hθ, primeFormOneEquiv_primeFormConjAut]
    have hεθs : ∀ x, ε (θ.symm x) = (psuConj h H')⁻¹ (ε x) := fun x => by
      have h1 := hεθ (θ.symm x)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [h1, MulAut.inv_apply_self]
    refine ⟨H', ?_⟩
    ext y
    have hy : β y = ε (β₁ (ε.symm y)) := by
      rw [hββ₁]
      rfl
    rw [hy, hθα, hφ, hεθ, primeFormOneEquiv_primeFormFieldAut, hεθs, MulEquiv.apply_symm_apply,
      MulAut.mul_apply, MulAut.mul_apply]

end UnitaryCases

section UnitaryFixed

open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (fixedField_charP
  map_subtype_map_bar eq_one_of_map_eq_scalar descendGL map_descendGL map_subtype_injective)
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (exists_planeIsometryEquivSL)
open CFSG.ComponentClassification.OutcomeLocal (dotForm_restrict_isAlt
  dotForm_restrict_nondegenerate finrank_dotForm_ker oneRestrictEquiv)

variable {e : ℕ} {F : Type} [Field F]

theorem map_orth_mem_unitarySU (h : UnitaryFieldData 2 e F)
    (g : matrixIsometryGroup
      ((1 : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField)) :
    GeneralLinearGroup.map h.fixedField.subtype (g : GL (Fin 3) h.fixedField) ∈
      unitarySU 2 e F 3 := by
  have := fixedField_charP h
  have hdet := det_eq_one_of_mem (by simp) g.2
  have horth := mem_orth_iff.1 g.2
  rw [mem_unitarySU_iff h]
  change (((g : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).map
      h.fixedField.subtype).det = 1 ∧
    ((((g : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).map
      h.fixedField.subtype).map h.bar)ᵀ *
      ((g : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).map
        h.fixedField.subtype = 1
  refine ⟨?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · rw [map_subtype_map_bar, ← Matrix.transpose_map, ← Matrix.map_mul, horth,
      Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] noncomputable def orthToSU (h : UnitaryFieldData 2 e F) :
    matrixIsometryGroup ((1 : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) →*
      unitarySU 2 e F 3 where
  toFun g := ⟨GeneralLinearGroup.map h.fixedField.subtype g, map_orth_mem_unitarySU h g⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ (a : GL (Fin 3) h.fixedField) b)

@[expose] noncomputable def orthUProj (h : UnitaryFieldData 2 e F) :
    matrixIsometryGroup ((1 : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) →*
      unitaryPSU h 3 :=
  (unitaryProj h 3).comp (orthToSU h)

theorem orthUProj_injective (h : UnitaryFieldData 2 e F) : Function.Injective (orthUProj h) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [orthUProj, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_unitaryProj] at hg
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 hg
  exact eq_one_of_map_eq_scalar h (le_refl 3) hc

theorem range_orthUProj (h : UnitaryFieldData 2 e F) :
    (orthUProj h).range = fixedSubgroup (psuField h (barEquiv h)) := by
  have := fixedField_charP h
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    change psuField h (barEquiv h) (unitaryProj h 3 (orthToSU h g)) = unitaryProj h 3 (orthToSU h g)
    change psuField h (barEquiv h) ((orthToSU h g : unitarySU 2 e F 3) : unitaryPSU h 3) = _
    rw [psuField_mk]
    congr 1
    apply Subtype.ext
    rw [coe_suField]
    apply Units.ext
    rw [coe_glAut]
    exact map_subtype_map_bar h _
  · intro hx
    obtain ⟨A, rfl⟩ := unitaryProj_surjective h 3 x
    change psuField h (barEquiv h) ((A : unitarySU 2 e F 3) : unitaryPSU h 3) =
      ((A : unitarySU 2 e F 3) : unitaryPSU h 3) at hx
    rw [psuField_mk, QuotientGroup.eq] at hx
    obtain ⟨c, hcN, hc3, hcA⟩ := mem_unitaryScalars.1 hx
    have hA : (A : GL (Fin 3) F) = glAut (barEquiv h) A * GeneralLinearGroup.scalar (Fin 3) c := by
      rw [← hcA, Subgroup.coe_mul, Subgroup.coe_inv, coe_suField, mul_inv_cancel_left]
    have hcSU := scalar_mem_unitarySU h (n := 3) (by norm_num) hcN hc3
    set B : unitarySU 2 e F 3 := ⟨GeneralLinearGroup.scalar (Fin 3) c, hcSU⟩ * A with hB
    have hbarc : h.bar (c : F) * c = 1 := by
      rw [mul_comm]
      exact hcN
    have hc3' : (c : F) * c * c = 1 := by
      have := congrArg Units.val hc3
      simpa [pow_succ] using this
    have hbarc2 : h.bar (c : F) = c * c := by
      calc h.bar (c : F) = h.bar c * (c * c * c) := by rw [hc3', mul_one]
        _ = (h.bar c * c) * (c * c) := by ring
        _ = c * c := by rw [hbarc, one_mul]
    have hAij : ∀ i j, ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
        h.bar (((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) * c := by
      intro i j
      have h1 := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F) i j) hA
      simp only [Units.val_mul, coe_glAut, GeneralLinearGroup.coe_scalar, scalar_apply,
        mul_diagonal, Matrix.map_apply] at h1
      exact h1
    have hBij : ∀ i j, ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j =
        c * ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j := by
      intro i j
      change (((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i j = _
      rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_mul]
    have hBbar : ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar =
        ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      ext i j
      rw [Matrix.map_apply, hBij, map_mul, hbarc2]
      conv_rhs => rw [hAij]
      ring
    have hBorth : (descendGL h (B : GL (Fin 3) F) hBbar) ∈
        matrixIsometryGroup
          ((1 : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) := by
      rw [mem_orth_iff]
      apply map_subtype_injective h
      have hBu := ((mem_unitarySU_iff h).1 B.2).2
      rw [hBbar] at hBu
      change (((descendGL h (B : GL (Fin 3) F) hBbar : GL (Fin 3) h.fixedField) :
          Matrix (Fin 3) (Fin 3) h.fixedField)ᵀ *
        ((descendGL h (B : GL (Fin 3) F) hBbar : GL (Fin 3) h.fixedField) :
          Matrix (Fin 3) (Fin 3) h.fixedField)).map h.fixedField.subtype =
        (1 : Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.transpose_map]
      have hd := congrArg (fun M : GL (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F))
        (map_descendGL h (B : GL (Fin 3) F) hBbar)
      change ((descendGL h (B : GL (Fin 3) F) hBbar : GL (Fin 3) h.fixedField) :
        Matrix (Fin 3) (Fin 3) h.fixedField).map h.fixedField.subtype = _ at hd
      rw [hd]
      exact hBu
    refine ⟨⟨_, hBorth⟩, ?_⟩
    have hBB : orthToSU h ⟨_, hBorth⟩ = B :=
      Subtype.ext (map_descendGL h (B : GL (Fin 3) F) hBbar)
    change unitaryProj h 3 (orthToSU h ⟨_, hBorth⟩) = unitaryProj h 3 A
    rw [hBB, hB, map_mul]
    have hz : unitaryProj h 3 ⟨GeneralLinearGroup.scalar (Fin 3) c, hcSU⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_unitaryProj]
      exact ⟨c, hcN, hc3, rfl⟩
    rw [hz, one_mul]

theorem exists_SL_two_fixed_bar (h : UnitaryFieldData 2 e F) :
    ∃ j : SL(2, h.fixedField) →* unitaryPSU h 3,
      Function.Injective j ∧ j.range = fixedSubgroup (psuField h (barEquiv h)) := by
  have := fixedField_charP h
  have h3 : (3 : ℕ) = 2 * 1 + 1 := rfl
  obtain ⟨eSL⟩ := exists_planeIsometryEquivSL _
    (dotForm_restrict_isAlt (k := h.fixedField) (n := 3)) (dotForm_restrict_nondegenerate h3)
    (finrank_dotForm_ker h3)
  set e' := (oneRestrictEquiv (k := h.fixedField) h3).trans eSL
  refine ⟨(orthUProj h).comp e'.symm.toMonoidHom, (orthUProj_injective h).comp e'.symm.injective,
    ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e'.symm.surjective, Subgroup.map_top,
    range_orthUProj]

end UnitaryFixed

section UnitaryTwoPart

open CFSG.ClassicalGroups.UnitaryFlag CFSG.BenderSuzuki.MatrixGroups

variable {e : ℕ} {F : Type} [Field F]

theorem card_le_of_ncard_involutions {G : Type*} [Group G] [Finite G] {E B : Subgroup G}
    (hEB : E ≤ B) {m : ℕ} (hm : {g | g ∈ B ∧ orderOf g = 2}.ncard ≤ m)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ m + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsub : (E : Set G) \ {1} ⊆ {g | g ∈ B ∧ orderOf g = 2} := by
    intro s hs
    refine ⟨hEB hs.1, orderOf_eq_prime ?_ hs.2⟩
    exact elemPow_eq_one_of_isElementaryAbelian (A := E) s hs.1
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_sdiff_singleton_of_mem (one_mem E), ← Nat.card_coe_set_eq] at hle
  change Nat.card E - 1 ≤ _ at hle
  have : 1 ≤ Nat.card E := Nat.card_pos
  omega

theorem unitary_three_two_part_and_elementary (h : UnitaryFieldData 2 e F) (he : 2 ≤ e) :
    ordProj[2] (Nat.card (unitaryPSU h 3)) = (2 ^ e) ^ 3 ∧
      ∀ E : Subgroup (unitaryPSU h 3), IsElementaryAbelian 2 E → Nat.card E ≤ 2 ^ e := by
  classical
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h with hJdef
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have hfixed := ShultStronglyClosedTI.UnitaryRootAutomorphism.card_fixed_fieldDataHermitianForm h
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, -, -, hsup, -, -, -, ⟨S, hS⟩, hScard,
    -, -, -, hinvol, -, -, -⟩ :=
    ShultStronglyClosedTI.UnitaryModel.unitary_three_point_structure J e he h.card_eq_sq hfixed hJ
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  set θ : unitaryPSU h 3 ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (hypProjTransport h hR).symm.trans
      (ShultStronglyClosedTI.UnitaryAutomorphism.hypPSUEquivPSU (J := J) h (fun _ => rfl) rfl)
  have : Finite (unitaryPSU h 3) := inferInstance
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv _ θ.toEquiv
  set U := (CFSG.BenderSuzuki.External.hermitianUnipotentPSU J hJ).range
  set B := CFSG.ShultStronglyClosedTI.TwoCoreGrowth.unitaryCoordinateStabilizer J 0
  have hUB : U ≤ B := le_sup_left.trans hsup.le
  refine ⟨?_, fun E hE => ?_⟩
  · rw [Nat.card_congr θ.toEquiv, ordProj_eq_of_sylow S, hS, hScard]
  have hcount : {g | g ∈ B ∧ orderOf g = 2}.ncard ≤ 2 ^ e - 1 := by
    choose! β M hβ0 hβ1 hM hsM using fun g hg => (hinvol g).1 hg
    have hinj : Set.InjOn β {g | g ∈ B ∧ orderOf g = 2} := by
      intro s hs s' hs' hss'
      apply Subtype.ext
      rw [hsM s hs, hsM s' hs']
      congr 1
      exact Units.ext (by rw [hM s hs, hM s' hs', hss'])
    have hle := Set.ncard_le_ncard_of_injOn β
      (t := (h.traceZero : Set F) \ {0}) (fun s hs => ⟨hβ0 s hs, hβ1 s hs⟩) hinj
      (Set.toFinite _)
    rwa [Set.ncard_sdiff_singleton_of_mem (zero_mem h.traceZero), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, h.card_traceZero] at hle
  have : IsElementaryAbelian 2 (E.map θ.toMonoidHom) := IsElementaryAbelian.map _
  have hE2 : IsPGroup 2 (E.map θ.toMonoidHom) := IsElementaryAbelian.isPGroup 2 _
  obtain ⟨P, hP⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P S
  set E' := (E.map θ.toMonoidHom).map (MulAut.conj g).toMonoidHom
  have : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  have hE'U : E' ≤ U := by
    rw [← hS, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hP
  have hcardE : Nat.card E' = Nat.card E := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective θ.injective]
  have h4 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have := card_le_of_ncard_involutions (hE'U.trans hUB) hcount
  omega

end UnitaryTwoPart

section UnitaryModel

open UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel (map_fixed_transport
  conj_injective_of_center_eq_bot)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (fixedField_charP)

theorem unitary_three_fixed_normal_SL_two {n m : ℕ} {K : Type*} {F : Type} [Field K] [Field F]
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (h : UnitaryFieldData 2 m F) {D : Type*} [Group D]
    (η : D ≃* unitaryPSU h 3) (α : MulAut D) (hα : orderOf α = 2) (S : Subgroup D)
    (hSα : S ≤ fixedSubgroup α) (hSn : (S.subgroupOf (fixedSubgroup α)).Normal)
    (κ : S ≃* SL(2, K)) :
    m = n ∧ S = fixedSubgroup α ∧ α ∉ (MulAut.conj : D →* MulAut D).range ∧
      (∃ H : unitaryIsom3 h,
        (∀ d, psuConj h H (η (α d)) = psuField h (barEquiv h) (psuConj h H (η d))) ∧
        S.map (η.trans (psuConj h H)).toMonoidHom = fixedSubgroup (psuField h (barEquiv h))) ∧
      ordProj[2] (Nat.card D) = (2 ^ n) ^ 3 ∧
      (∀ U : Subgroup D, IsElementaryAbelian 2 U → Nat.card U ≤ 2 ^ n) ∧
      ∀ P : Subgroup D, Nat.card P = (2 ^ n) ^ 3 → ∃ Q : Sylow 2 D, (Q : Subgroup D) = P := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have := h.finite
  have : CharP F 2 := h.charP
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have : Finite D := Finite.of_equiv _ η.symm.toEquiv
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := isSimpleGroup_SL_two (k := K) hK4
  have : IsSimpleGroup S := κ.isSimpleGroup
  have hSnab : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_mul_ne_SL_two (k := K)
    exact ⟨κ.symm a, κ.symm b, fun h => hab (κ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hcardS : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr κ.toEquiv, card_SL_two, hK]
  have hm : 2 ≤ m := by
    by_contra hlt
    have h1 : m = 1 := by have := h.one_le; omega
    subst h1
    have hdvd : Nat.card S ∣ Nat.card D := Subgroup.card_subgroup_dvd_card S
    rw [Nat.card_congr η.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.card_unitaryPSU_three h, hcardS] at hdvd
    exact not_dvd_seventy_two hn hdvd
  have hq : ¬((3 : ℕ) = 3 ∧ 2 ^ m = 2) := by
    rintro ⟨-, h2⟩
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨hα'o, hα'2, hα'1, hα'⟩ := transport_data η hα
  set α' := MulAut.congr η α with hα'def
  obtain ⟨hS'fix, hS'n⟩ := map_fixed_transport η (α := α) hSα hSn hα'
  set eS := S.equivMapOfInjective η.toMonoidHom η.injective with heS
  have : IsSimpleGroup (S.map η.toMonoidHom) := eS.symm.isSimpleGroup
  have hS'nab : ∃ a b : S.map η.toMonoidHom, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eS a, eS b, fun h => hab (eS.injective (by rw [map_mul, map_mul, h]))⟩
  have hnq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := fun h32 => hq ⟨rfl, congrArg Prod.snd h32⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 m h.card_eq_sq 3
    le_rfl hnq
  have : IsSimpleGroup (unitaryPSU h 3) := (unitaryPSUEquiv h (by norm_num)).isSimpleGroup
  have hPnab : ∃ x y : unitaryPSU h 3, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hS'nab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  have hZ : Subgroup.center (unitaryPSU h 3) = ⊥ := center_eq_bot_of_isSimpleGroup hPnab
  have hout := unitary_not_mem_inner_of_normal_simple_fixed h hm hα'2 hα'1 hZ hS'fix hS'n hS'nab
  obtain ⟨H₀, hH₀⟩ := eq_conj_bar_of_not_mem_inner h hm hα'o hout
  have hψα : ∀ d, psuConj h H₀⁻¹ (η (α d)) =
      psuField h (barEquiv h) (psuConj h H₀⁻¹ (η d)) := by
    intro d
    have h1 : η (α d) = α' (η d) := by rw [hα', MulEquiv.symm_apply_apply]
    rw [h1, hH₀, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_bar h
  obtain ⟨hmn, hSeq, hSmap⟩ := fixed_SL_two_root hK hn h.card_fixedField
    (η.trans (psuConj h H₀⁻¹)) hψα j hj hjr hSα hSn κ
  have hαout : α ∉ (MulAut.conj : D →* MulAut D).range := by
    rintro ⟨d, hd⟩
    apply hout
    refine ⟨η d, ?_⟩
    ext x
    rw [hα', ← hd, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  obtain ⟨hordP, helemP⟩ := unitary_three_two_part_and_elementary h hm
  have hord : ordProj[2] (Nat.card D) = (2 ^ n) ^ 3 := by
    rw [Nat.card_congr η.toEquiv, hordP, hmn]
  refine ⟨hmn, hSeq, hαout, ⟨H₀⁻¹, hψα, hSmap⟩, hord, fun U hU => ?_,
    exists_sylow_eq_of_card hord⟩
  have : IsElementaryAbelian 2 (U.map η.toMonoidHom) := IsElementaryAbelian.map _
  have h1 := helemP _ this
  rwa [Subgroup.card_map_of_injective η.injective, hmn] at h1

end UnitaryModel

end LinearUnitaryThree

open scoped MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearUnitaryThree LinearFlag
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

end CFSG.LocalAnalysis.SymplecticFourStandard
