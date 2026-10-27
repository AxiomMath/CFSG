module

public import CFSG.LocalAnalysis.StandardType.GGF4N2E6NativeSetup
public import CFSG.Assembly.E6FourCentFineD
public import CFSG.Assembly.E6FourCentFineA
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RationalComponentEq
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.Adapters.LieModelSimple
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusFrame
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcAssemblyFG
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S5Defs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate10050
public import Certificates.Certificate16005
public import Certificates.Certificate16041
public import Certificates.Certificate17002
public import Certificates.Certificate17951
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2323
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8117
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType.N2E6Native

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section Generic


variable {L : Type} [Field L] [IsAlgClosed L]

theorem lang_isComponentOf_unique (S : LangSetup Tag.E6 L 5) {b : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 b ∈ S.D.torus) (hb : ∀ j, b j ^ 5 = 1)
    (h1 : rootDiagUnit Tag.E6 b ≠ 1) (c : KernelComponent (rootCharHom b)) (hc : ∀ c', c' = c)
    (hsimp : IsSimpleGroup (↥(rationalComponent S.ρ S.Γ (rootCharHom b) c) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom b) c))) :
    CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom b) c)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) ∧
      ∀ J, CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) →
        J = rationalComponent S.ρ S.Γ (rootCharHom b) c := by
  classical
  have hℓp : ringChar L ≠ 5 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one Nat.prime_five hb h1
  have hpL : ((5 : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne
      Nat.prime_five hℓp
  have hTame := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.langSetup_hTame_of_prime
    S Nat.prime_five hpL (fun h => by cases h) hT hb h1
  have hq : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom b) c) := by
    refine (hTame c).resolve_right fun hs => ?_
    set R := rationalComponent S.ρ S.Γ (rootCharHom b) c
    haveI := hsimp
    have hsQ : Group.IsSolvable (↥R ⧸ Subgroup.center ↥R) := inferInstance
    have hcomm : ∀ x y : ↥R ⧸ Subgroup.center ↥R, x * y = y * x :=
      IsSimpleGroup.comm_iff_isSolvable.mpr hsQ
    haveI : IsMulCommutative (↥R ⧸ Subgroup.center ↥R) := ⟨⟨hcomm⟩⟩
    letI : CommGroup (↥R ⧸ Subgroup.center ↥R) := IsMulCommutative.instCommGroup
    haveI : IsCyclic (↥R ⧸ Subgroup.center ↥R) := IsSimpleGroup.isCyclic
    have hRcomm : ∀ x y : ↥R, x * y = y * x :=
      commutative_of_cyclic_center_quotient (QuotientGroup.mk' (Subgroup.center ↥R))
        (by rw [QuotientGroup.ker_mk'])
    haveI : IsMulCommutative ↥R := ⟨⟨hRcomm⟩⟩
    have htop : Subgroup.center ↥R = ⊤ := Subgroup.center_eq_top
    exact not_subsingleton (↥R ⧸ Subgroup.center ↥R) (QuotientGroup.subsingleton_iff.mpr htop)
  refine ⟨?_, fun J hJ => ?_⟩
  · obtain ⟨hle, hsub⟩ := langSubnormal_of_mem_torus S hT c
    obtain ⟨hperf, hsimpR, -⟩ := hq
    exact ⟨hle, (CFSG.Open.IsSubnormal.iff_subgroupOf hle).2 hsub,
      ⟨hperf.commutator_eq_top, hsimpR⟩⟩
  · obtain ⟨i, hJi, -⟩ :=
      exists_eq_rationalComponent_of_isComponentOf S Nat.prime_five hT hb h1 hTame hJ
    rw [hJi, hc i]

end Generic

section Types


variable {L : Type} [Field L] [IsAlgClosed L]

theorem lang_D4_component (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    (hρ2 : ∀ γ, IsRoot Tag.E6 γ → S.ρ (S.ρ γ) = γ)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr))
    {b : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 b ∈ S.D.torus) (hb : ∀ j, b j ^ 5 = 1)
    (h1 : rootDiagUnit Tag.E6 b ≠ 1) (c : KernelComponent (rootCharHom b)) (hc : ∀ c', c' = c)
    (hr : compRank (componentRoots (rootCharHom b) c) = 4)
    (hn : (componentRoots (rootCharHom b) c).ncard = 24)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom b) c) = 1)
    (hout : ¬ twistInner (componentRoots (rootCharHom b) c)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _))) :
    CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom b) c)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) →
        J = rationalComponent S.ρ S.Γ (rootCharHom b) c) ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom b) c) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom b) c)) .POmegaMinus 4 2 2 := by
  have hL := CFSG.Assembly.e6Four_D4_fine S hq hρ2 hΦ hT hb h1 c hr hn hs hout
  exact ⟨(lang_isComponentOf_unique S hT hb h1 c hc
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL)).1,
    (lang_isComponentOf_unique S hT hb h1 c hc
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL)).2, hL⟩

theorem lang_A5_component (S : LangSetup Tag.E6 L 5) (hq : S.D.q = 4)
    {b : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 b ∈ S.D.torus) (hb : ∀ j, b j ^ 5 = 1)
    (h1 : rootDiagUnit Tag.E6 b ≠ 1) (c : KernelComponent (rootCharHom b)) (hc : ∀ c', c' = c)
    (hr : compRank (componentRoots (rootCharHom b) c) = 5)
    (hn : (componentRoots (rootCharHom b) c).ncard = 30)
    (hs : componentOrbitLength S.ρ (componentRoots (rootCharHom b) c) = 1)
    (hin : twistInner (componentRoots (rootCharHom b) c)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _))) :
    CFSG.Open.IsComponentOf (rationalComponent S.ρ S.Γ (rootCharHom b) c)
        (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) ∧
      (∀ J, CFSG.Open.IsComponentOf J (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit Tag.E6 b}) →
        J = rationalComponent S.ρ S.Γ (rootCharHom b) c) ∧
      LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom b) c) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom b) c)) .PSL 6 2 2 := by
  have hL := CFSG.Assembly.e6Four_A5_fine S hq hT hb h1 c hr hn hs hin
  exact ⟨(lang_isComponentOf_unique S hT hb h1 c hc
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL)).1,
    (lang_isComponentOf_unique S hT hb h1 c hc
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL)).2, hL⟩

end Types

end CFSG.StandardType.N2E6Native

end
