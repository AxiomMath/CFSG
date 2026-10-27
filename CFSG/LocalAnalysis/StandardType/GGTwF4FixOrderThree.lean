module

public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Comp
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeMark
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.LieType.Ree.LargeReeCenterTrivial
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem twF4_ggAutFixedSubgroup_mulEquiv_unitarySU
    (a : ℕ) (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (τ : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)))
    (hτI : τ ∈ LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    Nonempty (↥(ggAutFixedSubgroup τ) ≃*
      ↥(CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 (2 * a + 1)
        (GaloisField 2 (2 * (2 * a + 1))) 3)) := by
  classical
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨s, hs⟩ := chevIDImage_subset_inn_twF4 ha K hK hτI
  obtain ⟨e0⟩ := gff_nonempty_centerQuot_equiv_reeGamma ha hK
  let y : CFSG.LieType.Ree.ReeTag.F4.reeGamma K a := e0 s
  have hZR : Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H a K)) = ⊥ := by
    rw [← Subgroup.map_center_eq e0.symm,
      CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial a K hK, Subgroup.map_bot]
  have hs3 : s ^ 3 = 1 := by
    have h1 : (MulAut.conj (s ^ 3) :
        MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K))) = 1 := by
      rw [map_pow, hs, hτ3]
    have hmem : s ^ 3 ∈ Subgroup.center (LargeEvenCenterQuot (LargeEvenTwF4H a K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun f : MulAut (LargeEvenCenterQuot (LargeEvenTwF4H a K)) => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * s ^ 3 = (s ^ 3 * g * (s ^ 3)⁻¹) * s ^ 3 := by rw [hg]
        _ = s ^ 3 * g := by group
    rw [hZR] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hy3 : y ^ 3 = 1 := by
    change (e0 s) ^ 3 = 1
    rw [← map_pow, hs3, map_one]
  have hy1 : y ≠ 1 := by
    intro h
    apply hτ1
    rw [← hs]
    have hs1 : s = 1 := e0.injective (by
      have h' : e0 s = 1 := h
      rw [h', map_one])
    rw [hs1, map_one]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hconj : ∀ x : LargeEvenCenterQuot (LargeEvenTwF4H a K),
      MulAut.conj y (e0 x) = e0 (MulAut.conj s x) := by
    intro x
    change e0 s * e0 x * (e0 s)⁻¹ = e0 (s * x * s⁻¹)
    rw [← map_mul, ← map_inv, ← map_mul]
  obtain ⟨eA⟩ := gffa2_fixedEquiv_of_congr e0 (MulAut.conj s) (MulAut.conj y) hconj
  obtain ⟨eSU⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU
    a K hK y hy
  have hcy : ggAutFixedSubgroup (MulAut.conj y) = Subgroup.centralizer ({y} : Set _) := by
    ext x
    rw [mem_ggAutFixedSubgroup, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc x * y = y * x * y⁻¹ * y := by rw [h]
        _ = y * x := by group
    · intro h
      rw [← h]
      group
  have hcs : ggAutFixedSubgroup (MulAut.conj s) = ggAutFixedSubgroup τ := by rw [hs]
  exact ⟨(MulEquiv.subgroupCongr hcs).symm.trans
    (eA.symm.trans ((MulEquiv.subgroupCongr hcy).trans eSU))⟩

end CFSG.StandardType

end
