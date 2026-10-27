module

public import CFSG.RankThree.PartOne.K133X.CharTwo
public import CFSG.RankThree.PartOne.K133X.Cent
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore

public section

namespace CFSG.RankThree.PartOne.K133X

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification TauCeti CFSG.RankThree.PartOne.K133 CFSG.RankThree.PartOne.OutStructure
  CFSG.RankThree.PartOne.S13K
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem chevalleyExceptionalModel_trialityD4_of_isoLie {X : Type} [Group X] {q : PrimePower}
    (hq : q.p = 2) (hiso : IsoLie X (.trialityD4 q)) :
    ChevalleyExceptionalModel X .trialityD4 2 q.exponent := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have h : ChevalleyExceptionalModel X .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e0⟩
  rwa [hq] at h

theorem charTwoCent_trialityD4 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {f : ℕ} (hmodel : ChevalleyExceptionalModel X .trialityD4 2 f) :
    CharTwoCent X := by
  intro u hu2
  have hf1 : 1 ≤ f := hmodel.1.2.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨θ⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf1 hmodel.2
  have hcomp : CatLeaf.InvolutionCentralizersComponentFree X :=
    CatLeaf.involutionCentralizersComponentFree_exceptional (t := .trialityD4)
      (by simp [chevalleyExceptionalTags]) hmodel
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_eq_bot_of_mulEquiv θ (center_eq_bot_of_simple_of_nonabelian hne)
  have hcore := oddCore_centralizer_eq_bot_of_innerModel θ hZ
    (fun H hH α hα hα2 => (even_exceptional_inner_involution_full_centralizer_odd_core.2 TwistTag.D4
      f K σ hf1 hK hσ H hH α hα hα2)) hu2
  exact isCharacteristicP_two_of_oddCore_noComponent hcore (hcomp u hu2)

theorem goodResV_trialityD4 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {q : PrimePower} (hq : q.p = 2)
    (hiso : IsoLie X (.trialityD4 q)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : GoodResV p X := by
  have hmodel := chevalleyExceptionalModel_trialityD4_of_isoLie hq hiso
  exact goodResV_of_charTwoCent hp hp2 (center_eq_bot_of_simple_of_nonabelian hne)
    (outPNice_trialityD4 hp hmodel).toChain (charTwoCent_trialityD4 hne hmodel)

theorem kf133ResMaxAt_leaf7_eight (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 8) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hiso⟩ := hX
  exact goodResV_trialityD4 hne hq2 hiso hp (by omega)

end CFSG.RankThree.PartOne.K133X
