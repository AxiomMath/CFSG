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

theorem chevalleyExceptionalModel_G2_of_isoLie {X : Type} [Group X] {q : PrimePower} (hq : q.p = 2)
    (hiso : IsoLie X (.G2 q)) : ChevalleyExceptionalModel X .G2 2 q.exponent := by
  obtain ⟨hv, ⟨e0⟩⟩ := hiso
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e0
  have hrange := ((LieTypeIndex.valid_iff _).1 hv).1
  have h : ChevalleyExceptionalModel X .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, by
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using hrange⟩, hmodel⟩
  rwa [hq] at h

theorem charTwoCent_G2 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {f : ℕ} (hmodel : ChevalleyExceptionalModel X .G2 2 f) :
    CharTwoCent X := by
  intro u hu2
  have hf1 : 1 ≤ f := hmodel.1.2.1
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have h3 : 3 ≤ 2 ^ f := hmodel.1.2.2.2
    have : f = 1 := by omega
    subst this
    norm_num at h3
  obtain ⟨K, _, _, hK, ⟨θ⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 hmodel.2
  have hcomp : CatLeaf.InvolutionCentralizersComponentFree X :=
    CatLeaf.involutionCentralizersComponentFree_exceptional (t := .G2)
      (by simp [chevalleyExceptionalTags]) hmodel
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
    center_eq_bot_of_mulEquiv θ (center_eq_bot_of_simple_of_nonabelian hne)
  have hcore := oddCore_centralizer_eq_bot_of_innerModel θ hZ
    (fun H hH α hα hα2 => (even_exceptional_inner_involution_full_centralizer_odd_core.1 .G2 f K hf1
      hK (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hf2⟩)))) H hH α hα hα2)) hu2
  exact isCharacteristicP_two_of_oddCore_noComponent hcore (hcomp u hu2)

theorem goodResV_G2 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hne : ∃ a b : X, a * b ≠ b * a) {q : PrimePower} (hq : q.p = 2) (hiso : IsoLie X (.G2 q))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : GoodResV p X := by
  have hmodel := chevalleyExceptionalModel_G2_of_isoLie hq hiso
  exact goodResV_of_charTwoCent hp hp2 (center_eq_bot_of_simple_of_nonabelian hne)
    (outPNice_G2 hp hmodel).toChain (charTwoCent_G2 hne hmodel)

theorem kf133ResMaxAt_leaf7_five (hTypes : ∀ r, 9 ≤ r → r ≤ 12 → KF132Types r) :
    KF133ResMaxAt (leaf7 5) := by
  refine KF133ResMaxAt.of_goodResV hTypes fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hiso⟩ := hX
  exact goodResV_G2 hne hq2 hiso hp (by omega)

end CFSG.RankThree.PartOne.K133X
