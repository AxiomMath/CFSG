module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLangRestField
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaModelMinus
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.Assembly.GL83StatedBridge
import CFSG.Adapters.LieModelSimple
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.StandardType

open CFSG.Assembly


private theorem l02qf1_noncomm_of_perfect {R : Type} [Group R] [Nontrivial R]
    [Group.IsPerfect R] : ∃ a b : R, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isMulCommutative R (IsMulCommutative.of_comm hcon)

private theorem l02qf1_recipeLinear_field_pow {d N e : ℕ} (he : 1 ≤ e) (hN : N = 2 ^ e)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ ∀ f ∈ F, f ^ e = 1 := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    NbrLangRest.pow_eq_one_of_mem_field_linear he (hK.trans hN) hf⟩

private theorem l02qf1_recipeSymplectic_field_pow {m N e : ℕ} (he : 1 ≤ e) (hN : N = 2 ^ e)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic m N false Q) :
    LargeEvenRecipeSymplectic m N false fun R _ I F => Q R I F ∧ ∀ f ∈ F, f ^ e = 1 := by
  dsimp only [LargeEvenRecipeSymplectic] at h ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  refine ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf => ?_⟩
  exact NbrLangRest.pow_eq_one_of_mem_field_symplectic he (hK.trans hN) hf

private theorem l02qf1_recipeOmegaPlus_field_pow {m N e : ℕ} (hm : 1 ≤ m) (he : 1 ≤ e)
    (hN : N = 2 ^ e) {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus m N Q) :
    LargeEvenRecipeOmegaPlus m N fun R _ I F => Q R I F ∧ ∀ f ∈ F, f ^ e = 1 := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    NbrLangRest.pow_eq_one_of_mem_field_omegaPlus hm he (hK.trans hN) hf⟩

private theorem l02qf1_pow_unitary {K : Type} [Field K] [Finite K] {d n : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K) (hd : 1 ≤ d) (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2)
    {f : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :
    f ^ (2 * n) = 1 := by
  obtain ⟨σ, hσ⟩ := RecipeFieldSU.congr_field_eq h hd hf
  have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK'
  have hσm : σ ^ (2 * n) = 1 := hcard ▸ pow_card_eq_one'
  apply (MulAut.congr (InndiagSU.projEquiv h hd)).injective
  rw [map_pow, hσ, ← map_pow, hσm, map_one, map_one]

private theorem l02qf1_recipeUnitary_field_pow {d n : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ ∀ f ∈ F, f ^ (2 * n) = 1 := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    unitaryFieldData_of_card hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, fun f hf =>
    l02qf1_pow_unitary (K := K) hUFD hd hn hK hf⟩

private theorem l02qf1_pow_phiQ {m n : ℕ} {K : Type} [Field K] [Finite K]
    (hm : 3 ≤ m) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hf : f ∈ LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))) :
    f ^ (2 * n) = 1 := by
  haveI : CharP K 2 := charP_two_of_card hK
  obtain ⟨k, hk⟩ :=
    RecipeFieldOmega.congr_minusEquiv_of_mem_phi (n := m + 1) (b := b) (c := c) (by omega) hirr hf
  have hfrob : AutOm.frobAut (K := K) (n := m + 1) (b := b) (c := c) (by omega) hirr ^
      (2 * n) = 1 :=
    AutOm.frobAut_pow_two_mul (K := K) (n := m + 1) (b := b) (c := c) (by omega) hirr hK
  apply (MulAut.congr
    (RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c) (by omega))).injective
  rw [map_pow, map_one, hk, ← pow_mul, mul_comm k (2 * n), pow_mul, hfrob, one_pow]

private theorem l02qf1_recipeOmegaMinus_field_pow {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧ ∀ f ∈ F, f ^ (2 * n) = 1 := by
  obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hirr, hQ, fun f hf =>
    l02qf1_pow_phiQ (m := m) (n := n) hm hn hK hirr hf⟩

private theorem l02qf1_raw_linear {d : ℕ} (K : Type) [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hd : 2 ≤ d)
    (hq4 : d = 2 → 4 ≤ p ^ f) (h22 : (d, p ^ f) ≠ (2, 2)) (h23 : (d, p ^ f) ≠ (2, 3)) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) ∧
      ∃ a b : LargeEvenProj (LargeEvenSLGroup (Fin d) K), a * b ≠ b * a := by
  have hs : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSL d K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel
      (t := .PSL) (n := d) (p := p) (f := f)
      ⟨⟨hp, hf, hd, h22, h23⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hperfSL : Group.IsPerfect (CFSG.Open.StatedSL d K) := by
    rcases (show d = 2 ∨ 3 ≤ d by omega) with h2 | h3
    · subst h2
      exact CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card
        (by rw [hK]; exact hq4 rfl)
    · exact CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le h3 K
  have hperfProj : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSL d K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact hs
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact hperfProj
  exact ⟨inferInstance, l02qf1_noncomm_of_perfect⟩

private theorem l02qf1_raw_unitary {d n : ℕ} (K : Type) [Field K] [Finite K]
    (hn : 1 ≤ n) (hd : 3 ≤ d) (hnq : (d, 2 ^ n) ≠ (3, 2))
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) ∧
      ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)), a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ n) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hK d hd hnq
  have hperfSU : Group.IsPerfect (CFSG.Open.StatedSU d (2 ^ n) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) hK hd hnq
  have hperfProj : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSU d (2 ^ n) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := hs
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := hperfProj
  exact ⟨inferInstance, l02qf1_noncomm_of_perfect⟩

private theorem l02qf1_raw_symplectic {m n : ℕ} (K : Type) [Field K] [Finite K]
    (hn : 1 ≤ n) (hm : 2 ≤ m) (hmn : m = 2 → 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m)) ∧
      ∃ a b : LargeEvenProj (LargeEvenSpGroup K m), a * b ≠ b * a := by
  have hcondSim : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ m) ∨
      (Nat.card K = 2 ∧ 3 ≤ m) := by
    rcases (show n = 1 ∨ 2 ≤ n by omega) with hn1 | hn2
    · right; right
      refine ⟨by rw [hK, hn1, pow_one], ?_⟩
      rcases (show m = 2 ∨ 3 ≤ m by omega) with hm2 | hm3
      · exact absurd (hmn hm2) (by omega)
      · exact hm3
    · left; right
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hs : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp m K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m (by omega) hcondSim
  have hcondPerf : (∃ s : Finset K, s.card = 4) ∨ (Nat.card K = 3 ∧ 2 ≤ m) ∨
      (Nat.card K = 2 ∧ 3 ≤ m) := by
    rcases (show n = 1 ∨ 2 ≤ n by omega) with hn1 | hn2
    · right; right
      refine ⟨by rw [hK, hn1, pow_one], ?_⟩
      rcases (show m = 2 ∨ 3 ≤ m by omega) with hm2 | hm3
      · exact absurd (hmn hm2) (by omega)
      · exact hm3
    · left
      haveI : Fintype K := Fintype.ofFinite K
      have h4 : 4 ≤ Nat.card K := by
        rw [hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      obtain ⟨s, -, hs4⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
      exact ⟨s, hs4⟩
  have hperfProj : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSp m K)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect (n := m) (K := K) hcondPerf
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenSpGroup K m)) := hs
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenSpGroup K m)) := hperfProj
  exact ⟨inferInstance, l02qf1_noncomm_of_perfect⟩

private theorem l02qf1_raw_omegaPlus {m n : ℕ} (K : Type) [Field K] [Finite K]
    (hn : 1 ≤ n) (hm : 4 ≤ m) (hK : Nat.card K = 2 ^ n) :
    IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) ∧
      ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)), a * b ≠ b * a := by
  have hs : IsSimpleGroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus
      (n := m) (K := K) (by omega)
  have hperfΩ : Group.IsPerfect (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (n := m) (K := K) (by omega)
  have hperfProj : Group.IsPerfect
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := hs
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := hperfProj
  exact ⟨inferInstance, l02qf1_noncomm_of_perfect⟩

private theorem l02qf1_raw_omegaMinus {m n : ℕ} (K : Type) [Field K] [Finite K]
    (hm : 3 ≤ m) (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) ∧
      ∃ a b' : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)), a * b' ≠ b' * a := by
  haveI hsS : IsSimpleGroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
      (n := m + 1) (K := K) (b := b) (c := c) (by omega) hirr
  haveI hperfΩ : Group.IsPerfect
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) K b c)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus
      (n := m + 1) (K := K) (b := b) (c := c) (by omega) hirr
  haveI hperfProj : Group.IsPerfect
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) K b c))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    (omegaMinusProjEquiv (K := K) (m + 1) b c).isSimpleGroup
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    Group.IsPerfect.ofSurjective
      (f := (omegaMinusProjEquiv (K := K) (m + 1) b c).symm.toMonoidHom)
      (omegaMinusProjEquiv (K := K) (m + 1) b c).symm.surjective
  exact ⟨inferInstance, l02qf1_noncomm_of_perfect⟩

private theorem l02qf1_recipeLinear_simple {d N p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hN : N = p ^ f) (hd : 2 ≤ d) (hq4 : d = 2 → 4 ≤ p ^ f)
    (h22 : (d, p ^ f) ≠ (2, 2)) (h23 : (d, p ^ f) ≠ (2, 3))
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    l02qf1_raw_linear (K := K) hp hf (hK.trans hN) hd hq4 h22 h23⟩

private theorem l02qf1_recipeUnitary_simple {d n : ℕ} (hn : 1 ≤ n) (hd : 3 ≤ d)
    (hnq : (d, 2 ^ n) ≠ (3, 2)) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    l02qf1_raw_unitary (n := n) K hn hd hnq hK⟩

private theorem l02qf1_recipeSymplectic_simple {m n : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hmn : m = 2 → 2 ≤ n) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F => Q R I F ∧
      (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) := by
  dsimp only [LargeEvenRecipeSymplectic] at h ⊢
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  exact l02qf1_raw_symplectic (m := m) (n := n) K hn hm hmn hK

private theorem l02qf1_recipeOmegaPlus_simple {m n : ℕ} (hn : 1 ≤ n) (hm : 4 ≤ m)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaPlus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaPlus m (2 ^ n) fun R _ I F => Q R I F ∧
      (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    l02qf1_raw_omegaPlus (m := m) (n := n) K hn hm hK⟩

private theorem l02qf1_recipeOmegaMinus_simple {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F => Q R I F ∧
      (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) := by
  obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ⟩ := h
  letI := hF
  haveI := hfin
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hirr, hQ,
    l02qf1_raw_omegaMinus (m := m) (n := n) K hm hn hK hirr⟩

theorem kgfni_fieldExponent_classical : KGFNIFieldExponentOn KGFNIClassicalLabel := by
  intro lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht | ht | ht | ht | ht
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [kgfniFieldDegree, one_mul]
    exact l02qf1_recipeLinear_field_pow (d := l + 1) (N := 2 ^ n) (e := n) hlab.1 rfl hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [kgfniFieldDegree]
    exact l02qf1_recipeUnitary_field_pow (d := l + 1) (n := n) hlab.1 (by omega) hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [kgfniFieldDegree, one_mul]
    exact l02qf1_recipeSymplectic_field_pow (m := l) (N := 2 ^ n) (e := n) hlab.1 rfl hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [kgfniFieldDegree, one_mul]
    exact l02qf1_recipeSymplectic_field_pow (m := l) (N := 2 ^ n) (e := n) hlab.1 rfl hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [kgfniFieldDegree, one_mul]
    split_ifs at hQ ⊢ with hl3
    · exact l02qf1_recipeLinear_field_pow (d := 4) (N := 2 ^ n) (e := n) hlab.1 rfl hQ
    · exact l02qf1_recipeOmegaPlus_field_pow (m := l) (N := 2 ^ n) (e := n)
        (by omega) hlab.1 rfl hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [kgfniFieldDegree]
    split_ifs at hQ ⊢ with h2 h3
    · exact l02qf1_recipeLinear_field_pow (d := 2) (N := (2 ^ n) ^ 2) (e := 2 * n)
        (by omega) (by rw [← pow_mul, mul_comm]) hQ
    · exact l02qf1_recipeUnitary_field_pow (d := 4) (n := n) hlab.1 (by omega) hQ
    · exact l02qf1_recipeOmegaMinus_field_pow (m := l - 1) (n := n)
        (by omega) hlab.1 hQ

theorem kgfni_rawSimple_classical : KGFNIRawSimpleOn KGFNIClassicalLabel := by
  intro lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht | ht | ht | ht | ht
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine l02qf1_recipeLinear_simple (d := l + 1) (N := 2 ^ n) (p := 2) (f := n)
      Nat.prime_two hlab.1 rfl (by omega) ?_ ?_ ?_ hQ
    · intro h2
      have hl1 : l = 1 := by omega
      have hn2 : 2 ≤ n := hlab.2.2 hl1
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    · intro h
      have h1 : l + 1 = 2 := congrArg Prod.fst h
      have hl1 : l = 1 := by omega
      have hn2 : 2 ≤ n := hlab.2.2 hl1
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have h2 : 2 ^ n = 2 := congrArg Prod.snd h
      omega
    · intro h
      have h1 : l + 1 = 2 := congrArg Prod.fst h
      have hl1 : l = 1 := by omega
      have hn2 : 2 ≤ n := hlab.2.2 hl1
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have h2 : 2 ^ n = 3 := congrArg Prod.snd h
      omega
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine l02qf1_recipeUnitary_simple (d := l + 1) (n := n) hlab.1 (by omega) ?_ hQ
    intro h
    have h1 : l + 1 = 3 := congrArg Prod.fst h
    have hl2 : l = 2 := by omega
    have hn2 : 2 ≤ n := hlab.2.2 hl2
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    omega
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact l02qf1_recipeSymplectic_simple (m := l) (n := n) hlab.1 hlab.2.1 hlab.2.2 hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact l02qf1_recipeSymplectic_simple (m := l) (n := n) hlab.1 hlab.2.1 hlab.2.2 hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with hl3
    · refine l02qf1_recipeLinear_simple (d := 4) (N := 2 ^ n) (p := 2) (f := n)
        Nat.prime_two hlab.1 rfl (by omega) (by intro h2; omega) ?_ ?_ hQ
      · intro h
        have h1 : (4 : ℕ) = 2 := congrArg Prod.fst h
        omega
      · intro h
        have h1 : (4 : ℕ) = 2 := congrArg Prod.fst h
        omega
    · exact l02qf1_recipeOmegaPlus_simple (m := l) (n := n) hlab.1 (by omega) hQ
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · have hq4 : 4 ≤ (2 : ℕ) ^ (2 * n) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine l02qf1_recipeLinear_simple (d := 2) (N := (2 ^ n) ^ 2) (p := 2) (f := 2 * n)
        Nat.prime_two (by omega) (by rw [← pow_mul, mul_comm]) (by omega)
        (by intro _; exact hq4) ?_ ?_ hQ
      · intro h
        have h2' : 2 ^ (2 * n) = 2 := congrArg Prod.snd h
        omega
      · intro h
        have h2' : 2 ^ (2 * n) = 3 := congrArg Prod.snd h
        omega
    · refine l02qf1_recipeUnitary_simple (d := 4) (n := n) hlab.1 (by omega) ?_ hQ
      intro h
      have h1 : (4 : ℕ) = 3 := congrArg Prod.fst h
      omega
    · exact l02qf1_recipeOmegaMinus_simple (m := l - 1) (n := n) (by omega) hlab.1 hQ

end CFSG.StandardType
