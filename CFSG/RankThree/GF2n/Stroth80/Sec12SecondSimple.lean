module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.RankThree.GF2n.Stroth80.Sec12SecondCfg
import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.LieType.Universal.Spin.Forms
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.RankThree.GF2n.Stroth80.Sec12SubWidth
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec86Assembly

public section

namespace CFSG.RankThree.GF2n.Stroth80

private theorem noncomm_of_perfect_nontrivial (G : Type) [Group G] [Nontrivial G]
    [Group.IsPerfect G] : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative G := ⟨⟨fun a b => hcon a b⟩⟩
  exact (Group.IsPerfect.not_isMulCommutative G) inferInstance

private theorem noncomm_of_mulEquiv_target {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ a b : Y, a * b ≠ b * a) : ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
  have h2 := congrArg e hc
  simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

private noncomputable def quotEquivOfEqBot {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    (h : N = ⊥) : G ⧸ N ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

theorem isSpModel_facts {m q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (hm : 2 ≤ m) (h : IsSpModel m q X) :
    IsSimpleGroup X ∧ ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨K, hf, hfin, hK, ⟨e⟩⟩ := h
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := m) (K := K)
  have hproj : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp m K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m (by omega)
      (Or.inl (Or.inr h4))
  have hS : IsSimpleGroup ↥(CFSG.Open.StatedSp m K) := (quotEquivOfEqBot hbot).symm.isSimpleGroup
  have hQ := CFSG.RankThree.GF2n.Stroth80.statedSp_quasisimple_of_card m K (by omega) h4
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedSp m K) := hQ.1
  exact ⟨e.isSimpleGroup, noncomm_of_mulEquiv_target e
    (noncomm_of_perfect_nontrivial ↥(CFSG.Open.StatedSp m K))⟩

theorem isOmegaPlus_facts {m q : ℕ} {X : Type} [Group X] (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a)
    (hm : 4 ≤ m) (h : IsOmegaPlus m q X) :
    IsSimpleGroup X ∧ ∃ x y : X, x * y ≠ y * x := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨K, hf, hfin, hK, ⟨e⟩⟩ := h
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have hv : ∃ v, CFSG.LieType.Universal.Spin.quadPlus m K v ≠ 0 := by
    let P := CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by omega⟩ : Fin m)
    exact ⟨P.e + P.f, by
      rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
      exact one_ne_zero⟩
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (Q := CFSG.LieType.Universal.Spin.quadPlus m K) (Q₀ := CFSG.Open.StatedQuadPlus m K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus m K) hv
  have hproj : IsSimpleGroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := K)
      (n := m) (by omega)
  have hW : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K)) :=
    (quotEquivOfEqBot hbot).symm.isSimpleGroup
  have hQ := CFSG.RankThree.GF2n.Stroth80.statedOmega_plus_quasisimple_of_three_le K m (by omega)
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K)) := hQ.1
  exact ⟨e.isSimpleGroup, noncomm_of_mulEquiv_target e
    (noncomm_of_perfect_nontrivial ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus m K)))⟩

open CFSG.ComponentClassification.RankTwoClassical in
theorem isOmegaMinus_three_facts {q : ℕ} {X : Type} [Group X]
    (hq : ∃ a : ℕ, 2 ≤ a ∧ q = 2 ^ a) (h : IsOmegaMinus 3 q X) :
    IsSimpleGroup X ∧ (∃ x y : X, x * y ≠ y * x) ∧
      Nat.card X = q ^ 6 * (q ^ 3 + 1) * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨K, hf, hfin, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hchar : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hK
  have hW : IsSimpleGroup ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)) :=
    ORigid.isSimpleGroup_statedOmega_quadMinus_of_two_le (m := 3) (by norm_num) hirr
  have hperf := ORigid.commutator_statedOmega_quadMinus_eq_top (m := 3) (by norm_num) hirr
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)) :=
    Group.isPerfect_def.mpr hperf
  obtain ⟨E, _, hU, ⟨θ⟩⟩ := nonempty_statedOmega_quadMinus_three_equiv hK hirr
  have hXE : Nat.card X = Nat.card ↥(CFSG.Open.StatedSU 4 (2 ^ a) E) :=
    Nat.card_congr (e.toEquiv.trans θ.toEquiv)
  have hSU := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hU (n := 4) (by norm_num)
  have hprod : ∏ i ∈ Finset.Icc 2 4, (((2 ^ a : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((2 ^ a : ℕ) : ℤ) ^ 2 - 1) * (((2 ^ a : ℕ) : ℤ) ^ 3 + 1) *
        (((2 ^ a : ℕ) : ℤ) ^ 4 - 1) := by
    rw [show Finset.Icc 2 4 = {2, 3, 4} from by decide, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    norm_num
    ring
  rw [hprod, show 4 * (4 - 1) / 2 = 6 from rfl] at hSU
  have hq2 : 1 ≤ (2 ^ a) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hq4 : 1 ≤ (2 ^ a) ^ 4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have key : ((Nat.card ↥(CFSG.Open.StatedSU 4 (2 ^ a) E) : ℕ) : ℤ) =
      (((2 ^ a) ^ 6 * ((2 ^ a) ^ 3 + 1) * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 4 - 1)) : ℕ) : ℤ) := by
    rw [hSU, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hq2, Nat.cast_sub hq4]
    push_cast
    ring
  refine ⟨e.isSimpleGroup, noncomm_of_mulEquiv_target e
    (noncomm_of_perfect_nontrivial ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c))),
    ?_⟩
  rw [hXE]
  exact Nat.cast_injective key

end CFSG.RankThree.GF2n.Stroth80
