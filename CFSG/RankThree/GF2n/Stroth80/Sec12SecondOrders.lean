module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCfg
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.Literature.Stroth80ArtinOrders
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidPlusFacts
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier
import CFSG.LieType.Universal.SpinOmega.Center
import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.RankThree.GF2n.Stroth80.Sec12SubWidth
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec86Assembly
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviFields
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofRigidDefs
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidSetup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidTheta
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.ComponentClassification.RankTwoClassical.ORigid
  (isSimpleGroup_statedOmega_quadPlus_of_three_le isSimpleGroup_statedOmega_quadMinus_of_two_le)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
  (orthogonal_geometry_classical_model_Schreier)
open CFSG.Timmesfeld.ClassicalOrders
  (card_statedProj_statedOmega_quadPlus card_statedProj_statedOmega_quadMinus
    map_add_eq_one_of_hypPair)

private theorem prod_Icc_one_three {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 3, f i = f 1 * f 2 * f 3 := by
  rw [show (Finset.Icc 1 3 : Finset ℕ) = {1, 2, 3} by decide]
  simp [Finset.prod_insert, mul_assoc]

private theorem prod_Icc_one_four {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 4, f i = f 1 * f 2 * f 3 * f 4 := by
  rw [show (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} by decide]
  simp [Finset.prod_insert, mul_assoc]

private theorem prod_Icc_sub_four {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 (4 - 1), f i = f 1 * f 2 * f 3 :=
  prod_Icc_one_three f

private theorem prod_Icc_sub_five {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 1 (5 - 1), f i = f 1 * f 2 * f 3 * f 4 :=
  prod_Icc_one_four f

private theorem exists_quadPlus_ne_zero (n : ℕ) (hn : 4 ≤ n) (K : Type) [Field K] :
    ∃ v, CFSG.LieType.Universal.Spin.quadPlus n K v ≠ 0 := by
  let P := CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by omega⟩ : Fin n)
  exact ⟨P.e + P.f, by
    rw [map_add_eq_one_of_hypPair P]
    exact one_ne_zero⟩

private theorem exists_quadMinus_ne_zero (n : ℕ) (hn : 4 ≤ n) (K : Type) [Field K] (b c : K) :
    ∃ v, CFSG.LieType.Universal.Spin.quadMinus n K b c v ≠ 0 := by
  let P := CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by omega⟩ : Fin (n - 1))
  exact ⟨P.e + P.f, by
    rw [map_add_eq_one_of_hypPair P]
    exact one_ne_zero⟩

private theorem nonempty_omega_mulEquiv_proj {σ : Type} [Fintype σ] [DecidableEq σ] {K : Type}
    [Field K] [CharP K 2] {Q : QuadraticForm K (σ → K)} {Q₀ : (σ → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hv : ∃ v, Q v ≠ 0) :
    Nonempty (↥(CFSG.Open.StatedOmega Q₀) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega Q₀)) :=
  ⟨QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ₀ hv).symm)⟩

private theorem exists_noncomm_of_isPerfect (G : Type) [Group G] [Nontrivial G]
    [Group.IsPerfect G] : ∃ x y : G, x * y ≠ y * x := by
  by_contra hc
  exact Group.IsPerfect.not_isMulCommutative G ⟨⟨fun x y =>
    Classical.byContradiction fun hxy => hc ⟨x, y, hxy⟩⟩⟩

private theorem exists_noncomm_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ x y : Y, x * y ≠ y * x) : ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨e.symm x, e.symm y, fun h' => hxy ?_⟩
  simpa using congrArg e h'

private theorem card_plus_four {q : ℕ} (hq0 : 0 < q) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = q) {X : Type} [Group X]
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K))) :
    Nat.card X = q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  have hZ := card_statedProj_statedOmega_quadPlus (K := K) (n := 4) (by norm_num)
  rw [hK, prod_Icc_sub_four] at hZ
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq0
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq0
  have key : ((Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadPlus 4 K))) : ℕ) : ℤ) =
      ((q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) : ℕ) : ℤ) := by
    rw [hZ]
    push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4, Nat.cast_sub hq6]
    norm_num
  rw [Nat.card_congr e.toEquiv]
  exact Nat.cast_injective key

private theorem card_minus_four {q : ℕ} (hq0 : 0 < q) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = q) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {X : Type} [Group X]
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) :
    Nat.card X = q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  have hZ := card_statedProj_statedOmega_quadMinus (K := K) (n := 4) (by norm_num) hirr
  rw [hK, prod_Icc_sub_four] at hZ
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq0
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq0
  have key : ((Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadMinus 4 K b c))) : ℕ) : ℤ) =
      ((q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) : ℕ) : ℤ) := by
    rw [hZ]
    push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4, Nat.cast_sub hq6]
    norm_num
  rw [Nat.card_congr e.toEquiv]
  exact Nat.cast_injective key

private theorem card_plus_five {q : ℕ} (hq0 : 0 < q) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = q) {X : Type} [Group X]
    (e : X ≃* CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 5 K))) :
    Nat.card X =
      q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  have hZ := card_statedProj_statedOmega_quadPlus (K := K) (n := 5) (by norm_num)
  rw [hK, prod_Icc_sub_five] at hZ
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq0
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq0
  have hq5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq0
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq0
  have hq8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ hq0
  have key : ((Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
      (CFSG.Open.StatedQuadPlus 5 K))) : ℕ) : ℤ) =
      ((q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) *
        (q ^ 8 - 1)) : ℕ) : ℤ) := by
    rw [hZ]
    push_cast [Nat.cast_sub hq2, Nat.cast_sub hq4, Nat.cast_sub hq5, Nat.cast_sub hq6,
      Nat.cast_sub hq8]
    norm_num
  rw [Nat.card_congr e.toEquiv]
  exact Nat.cast_injective key

theorem isSpModel_three_card {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsSpModel 3 q X) :
    Nat.card X = q ^ 9 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hX : Nat.card X = CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.spOrder 3 (Nat.card K) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.RankThree.GF2n.stroth80_artin_sp_order 3 K)
  rw [hK] at hX
  rw [hX, CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.spOrder, prod_Icc_one_three]
  norm_num

theorem isSpModel_four_card {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsSpModel 4 q X) :
    Nat.card X = q ^ 16 * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hX : Nat.card X = CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.spOrder 4 (Nat.card K) :=
    (Nat.card_congr e.toEquiv).trans (CFSG.RankThree.GF2n.stroth80_artin_sp_order 4 K)
  rw [hK] at hX
  rw [hX, CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.spOrder, prod_Icc_one_four]
  norm_num

theorem isOmegaPlus_four_facts {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsOmegaPlus 4 q X) :
    IsSimpleGroup X ∧ (∃ x y : X, x * y ≠ y * x) ∧ Group.IsSolvable (Outer X) ∧
      Nat.card X = q ^ 12 * (q ^ 4 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨a, ha, hqa⟩ := hq
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hq0 : 0 < q := by rw [hqa]; positivity
  haveI hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two (hK.trans hqa)
  haveI hΩs : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K)) :=
    isSimpleGroup_statedOmega_quadPlus_of_three_le (K := K) (k := 4) (by norm_num)
  haveI hΩp : Group.IsPerfect ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 4 K)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 4) (by norm_num)
  obtain ⟨iso⟩ := nonempty_omega_mulEquiv_proj
    (CFSG.LieType.Universal.Spin.coe_quadPlus 4 K) (exists_quadPlus_ne_zero 4 (le_refl 4) K)
  refine ⟨e.isSimpleGroup, exists_noncomm_of_mulEquiv e (exists_noncomm_of_isPerfect _), ?_,
    card_plus_four hq0 hK (e.trans iso)⟩
  have hmodel : CFSG.Open.StatedClassicalModel X .POmegaPlus 4 2 a :=
    ⟨⟨Nat.prime_two, by omega, le_refl 4⟩, K, hF, hfin, hK.trans hqa, ⟨e.trans iso⟩⟩
  exact (orthogonal_geometry_classical_model_Schreier .POmegaPlus (Or.inr (Or.inl rfl)) hmodel).2.2

theorem isOmegaMinus_four_facts {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsOmegaMinus 4 q X) :
    IsSimpleGroup X ∧ (∃ x y : X, x * y ≠ y * x) ∧ Group.IsSolvable (Outer X) ∧
      Nat.card X = q ^ 12 * (q ^ 4 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1)) := by
  obtain ⟨a, ha, hqa⟩ := hq
  obtain ⟨K, hF, hfin, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hq0 : 0 < q := by rw [hqa]; positivity
  haveI hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two (hK.trans hqa)
  haveI hΩs : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) :=
    isSimpleGroup_statedOmega_quadMinus_of_two_le (m := 4) (by norm_num) hirr
  haveI hΩp : Group.IsPerfect ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus (n := 4) (by norm_num) hirr
  obtain ⟨iso⟩ := nonempty_omega_mulEquiv_proj
    (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c)
    (exists_quadMinus_ne_zero 4 (le_refl 4) K b c)
  refine ⟨e.isSimpleGroup, exists_noncomm_of_mulEquiv e (exists_noncomm_of_isPerfect _), ?_,
    card_minus_four hq0 hK hirr (e.trans iso)⟩
  have hmodel : CFSG.Open.StatedClassicalModel X .POmegaMinus 4 2 a :=
    ⟨⟨Nat.prime_two, by omega, le_refl 4⟩, K, hF, hfin, hK.trans hqa, b, c, hirr,
      ⟨e.trans iso⟩⟩
  exact (orthogonal_geometry_classical_model_Schreier .POmegaMinus (Or.inr (Or.inr rfl)) hmodel).2.2

theorem isOmegaPlus_five_card {q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (h : IsOmegaPlus 5 q X) :
    Nat.card X =
      q ^ 20 * (q ^ 5 - 1) * ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1)) := by
  obtain ⟨a, -, hqa⟩ := hq
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hq0 : 0 < q := by rw [hqa]; positivity
  haveI hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two (hK.trans hqa)
  obtain ⟨iso⟩ := nonempty_omega_mulEquiv_proj
    (CFSG.LieType.Universal.Spin.coe_quadPlus 5 K) (exists_quadPlus_ne_zero 5 (by norm_num) K)
  exact card_plus_five hq0 hK (e.trans iso)

end CFSG.RankThree.GF2n.Stroth80
