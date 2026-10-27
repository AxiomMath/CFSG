module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeCalW

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem normalizer_wClos_le_of_bBar_add_lt (D : Data G) {V U : Subgroup G}
    (hVV : InCalV D.M V) (hV : IsElemAbelian 2 V) (hU : IsElemAbelian 2 U)
    (hMU : D.M ≤ normalizer (U : Set G)) (hPU : pCoreOf 2 D.M ≤ centralizer (U : Set G))
    {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hL1 : barSub ⊥ U hU L ≠ ⊥)
    (hUM : UniqueMax D.M (UC22.conjClosure D.M L ⊔ D.T)) {i : ℕ} (hi : i < rk ↥V)
    (hb : i + bBar (UC22.conjClosure D.M L) D.M ⊥ U hU < E3.sParam hV) :
    (∀ j : ℕ, j < rk ↥V → normalizer (E3.wClos V j D.T : Set G) ≤ D.M) ∧
      ∀ j : ℕ, j ≤ i → centralizer (E3.cClos V (i - j) D.T : Set G) ≤ D.M := by
  have hcomm := commutator_conjClosure_le_centralizer_of_add_lt hV hU hMU hLM hb
  set X := UC22.conjClosure D.M L
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTS : IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D hTM
  have hT2 : IsPGroup 2 D.T := hTS.isPGroup
  have hXM : X ≤ D.M := TwelveTwentyThree.conjClosure_le hLM.le
  have hKn : D.M ≤ normalizer ((D.M ⊓ centralizer (U : Set G) : Subgroup G) : Set G) :=
    A1a.le_normalizer_inf Subgroup.le_normalizer (A1a.le_normalizer_centralizer hMU)
  have hPK : pCoreOf 2 D.M ≤ D.M ⊓ centralizer (U : Set G) :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M) hPU
  have hLK : ¬ L ≤ D.M ⊓ centralizer (U : Set G) := by
    intro hle
    apply hL1
    refine le_bot_iff.1 fun φ hφ => ?_
    obtain ⟨g, hgL, rfl⟩ := (mem_barSub ⊥ U _ L φ).1 hφ
    rw [Subgroup.mem_bot, TwelveTwentyThree.actTil_bot_eq_one_iff]
    exact (hle hgL).2
  have hPT : pCoreOf 2 D.M ≤ D.T := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hTS.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  have hN : X ≤ normalizer (E3.wClos V i D.T : Set G) := by
    refine TwelveTwentyThree.le_normalizer_wClos fun x hxX A hA a ha => hPT ?_
    exact TwelveTwentyThree.commutator_mem_pCoreOf hLM hLq inf_le_left hKn hPK hLK
      (hA.1.trans hTM) (hcomm A hA) x hxX a ha
  have hTNW : D.T ≤ normalizer (E3.wClos V i D.T : Set G) :=
    Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos (V := V) (i := i) D.T)
  have hUN : InCalU D.M (D.M ⊓ normalizer (E3.wClos V i D.T : Set G)) :=
    InCalU.mono D.maxLocal hUM (le_inf (sup_le hXM hTM) (sup_le hN hTNW)) inf_le_left
  exact six_fifteen_three hV D.maxLocal hT2 (TwelveShort.wClos_zero_ne_bot D hVV) hi hUN

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
