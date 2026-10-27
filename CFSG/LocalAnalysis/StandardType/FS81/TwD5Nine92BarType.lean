module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Nine92Bar
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
public import CFSG.HardMathSupport.Dickson.Sec6.UpD42Aux.Descent
public import Mathlib.Algebra.Group.Subgroup.Ker
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.Quasithin.Background.A3Structure314
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F6CatRecogL2
public import CFSG.Quasithin.Background.F6CatRecogTools2
public import CFSG.Quasithin.Background.F918C6
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.T1515Der
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.A5S136c
public import CFSG.Quasithin.H13.A5Y1367c
public import CFSG.Quasithin.Vol2.Ch10SecA1011
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecB6C27
public import CFSG.Quasithin.Vol2.Ch10SecB6Lt
public import CFSG.Quasithin.Vol2.Ch10SecB6Prep
public import CFSG.Quasithin.Vol2.Ch10SecB6Rank
public import CFSG.Quasithin.Vol2.Ch10SecB6S21
public import CFSG.Quasithin.Vol2.Ch10SecB6Syl
public import CFSG.Quasithin.Vol2.Ch10SecKGC27b
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
public import CFSG.Quasithin.Vol2.Ch11SecSFacts2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3
public import CFSG.Quasithin.Vol2.Ch11SecSG2Sp4
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch9KGFFQR
public import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
public import CFSG.Walter.J1Props
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open
open CFSG.HardMathSupport.Dickson.Sec6
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

attribute [local instance] gLAPPrimeCoreOf_normal

theorem isCatalogLieIso_isD42_of_statedClassicalModel {G : Type} [Group G]
    (h : StatedClassicalModel G .POmegaPlus 4 2 1) :
    IsCatalogLieIso G IsD42Index := by
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ :=
    KSExact.exists_D_of_statedClassicalModel_POmegaPlus h
  exact ⟨⟨.D 4 q, hv⟩, ⟨rfl, hqp, hqf⟩, ⟨e⟩⟩

theorem twD5BarSub_mulEquiv_of_inf_eq_bot {G : Type} [Group G] {b₂ : G}
    {J : Subgroup G} (hJH : J ≤ centralizerBTwo b₂)
    (h : J ⊓ primeCoreCentralizerBTwo b₂ = ⊥) :
    Nonempty (twD5BarSub b₂ (J.subgroupOf (centralizerBTwo b₂)) ≃* ↥J) := by
  let H := centralizerBTwo b₂
  let O := (primeCoreCentralizerBTwo b₂).subgroupOf H
  have hker : (twD5BarMap b₂).ker.subgroupOf (J.subgroupOf H) = ⊥ := by
    rw [QuotientGroup.ker_mk', Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_comm]
    ext x
    constructor
    · rintro ⟨hxJ, hxO⟩
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subgroup.mem_bot.1 (h ▸ (show ((x : H) : G) ∈ J ⊓
        primeCoreCentralizerBTwo b₂ from ⟨hxJ, hxO⟩)))
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      exact ⟨J.one_mem, O.one_mem⟩
  let φ : ↥(J.subgroupOf H) →* twD5BarSub b₂ (J.subgroupOf H) :=
    (twD5BarMap b₂).subgroupMap (J.subgroupOf H)
  have hsurj : Function.Surjective φ := (twD5BarMap b₂).subgroupMap_surjective _
  have hk : φ.ker = ⊥ := by
    change ((twD5BarMap b₂).subgroupMap (J.subgroupOf H)).ker = ⊥
    rw [(J.subgroupOf H).ker_subgroupMap (twD5BarMap b₂)]
    exact hker
  have e : twD5BarSub b₂ (J.subgroupOf H) ≃* ↥(J.subgroupOf H) :=
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans QuotientGroup.quotientBot)
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe hJH)⟩

theorem isCatalogLieIso_twD5BarSub_of_inf_eq_bot {G : Type} [Group G] {b₂ : G}
    {J : Subgroup G} (hJH : J ≤ centralizerBTwo b₂)
    (h : J ⊓ primeCoreCentralizerBTwo b₂ = ⊥)
    (hcat : IsCatalogLieIso ↥J IsD42Index) :
    IsCatalogLieIso
      ↥(twD5BarSub b₂ (J.subgroupOf (centralizerBTwo b₂))) IsD42Index := by
  obtain ⟨e⟩ := twD5BarSub_mulEquiv_of_inf_eq_bot hJH h
  exact IsCatalogLieIso.of_mulEquiv e.symm hcat

end CFSG.StandardType.FrameRoute.FS81

end
