module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Rational
public import Certificates.Certificate13657
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428CensusFamExcTL
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreStab
import CFSG.HardMathSupport.Timmesfeld.Steinberg.ToralCentralizerGenerated
import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619CoverDescentHolds
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResComplete
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.KeyAbstract
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.LiftShell
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthAux.Field
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsExcAux.TwoDHigh
import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcD4Class

public section
namespace S2MathAs3_1619Final
open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

set_option synthInstance.maxSize 1024 in
private theorem e6_kac_two_root_kernel_count :
    ∀ m0 m1 m2 m3 m4 m5 : Fin 4,
      m0.val + 2 * m1.val + 2 * m2.val + 3 * m3.val + 2 * m4.val + m5.val ≤ 3 →
      ∀ x ∈ zlC m0 m1 m2 m3 m4 m5, szF (zlC m0 m1 m2 m3 m4 m5) x = 2 →
        cntB m0 m1 m2 m3 m4 m5 = 22 := by
  decide +kernel

theorem e6_kernel_ncard_eq_twentyTwo_of_component_ncard_eq_two
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hi : (componentRoots (rootCharHom a) i).ncard = 2) :
    (kernelRoots (rootCharHom a)).ncard = 22 := by
  have h3 : ((3 : ℕ) : L) ≠ 0 := by
    change (3 : L) ≠ 0
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have heq : (3 : L) = 1 := by
      calc (3 : L) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [heq]
    exact one_ne_zero
  obtain ⟨ζ, w, m0, m1, m2, m3, m4, m5, hζ, hsum, hchar, hdata⟩ :=
    kac_class_data h3 hap
  obtain ⟨x, hx, _, hcard, _, _⟩ := hdata i
  have h2 : szF (zlC m0 m1 m2 m3 m4 m5) x = 2 := hcard.symm.trans hi
  rw [ncard_kernelRoots_eq_cntB hζ w hchar]
  exact e6_kac_two_root_kernel_count m0 m1 m2 m3 m4 m5 hsum x hx h2

theorem isTypeL2_eight_of_hasLabel {Y : Type} [Group Y]
    (h : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (Y ⧸ Subgroup.center Y)) :
    IsTypeL2 8 Y := by
  have hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 2 3 :=
    statedClassicalModel_of_hasLabel_typeA (by simp [LargeEvenInLambda2]) h
  simpa only [StatedClassicalModel, IsTypeL2, Nat.reducePow] using hm.2


theorem e6_centralizer_le_torus_rootSpan_of_component_ncard_eq_two
    {τ : Tag} (hτ : τ = .E6) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin τ.rank → Lˣ} (hap : ∀ j, a j ^ 3 = 1)
    (i : KernelComponent (rootCharHom a)) (hi : (componentRoots (rootCharHom a) i).ncard = 2) :
    adjointGroup τ L ⊓ Subgroup.centralizer {rootDiagUnit τ a} ≤
      torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) := by
  subst τ
  have hc := e6_kernel_ncard_eq_twentyTwo_of_component_ncard_eq_two hap i hi
  have hstab := e6_stab_le_kernelReflectionGroup_of_conn a hap (by simp [hc])
  change toralCentralizer Tag.E6 L a ≤ _
  rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_of_stabilizer_le
    Tag.E6 L a hstab]
  exact le_rfl

theorem e6_component_ncard_eq_two_of_hasLabel
    {τ : Tag} (hτ : τ = .E6)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hlabel : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (rationalComponent S.ρ S.Γ (rootCharHom a) i ⧸
        Subgroup.center (rationalComponent S.ρ S.Γ (rootCharHom a) i))) :
    (componentRoots (rootCharHom a) i).ncard = 2 := by
  subst τ
  exact CFSG.LocalAnalysis.GLTheoremA.T1428.excres_class_rankOne_of_typeL2
    (Or.inr (Or.inl rfl)) CFSG.HardMathSupport.Dickson.Sec6.I1431.excKac_e6
    S hT hap h1 i hQS (by norm_num : 8 ≤ 8) (isTypeL2_eight_of_hasLabel hlabel)

theorem exists_rationalComponent_position_with_hasLabel
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    {C : Subgroup R} (hC : CFSG.Assembly.IsComponentOf C (ggFixSub phi))
    (hlabel : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (C ⧸ Subgroup.center C)) :
    ∃ j : Fin M.row.D.orbits.length, M.row.D.orbits[j].qs = true ∧
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
        (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j) ⧸
          Subgroup.center (rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j))) := by
  have hτ : M.tau ≠ .G2 := by
    rw [← M.tau_eq]
    cases M.row.T <;> simp [GGK0MarkedKacIface1587.absTag]
  obtain ⟨j, hqs, hCpos⟩ := GGK0MarkedComponents.exists_component_position_of_realization
    Nat.prime_three (by norm_num) M hτ hC
  let Q : Subgroup (ModGL M.tau Omega) :=
    rationalComponent M.setup.ρ M.setup.Γ (rootCharHom M.a) (M.repr j)
  have hCeq : C = E6Centralizer1585.component M j := hCpos
  have hmap : C.map M.iota = Q := by
    rw [hCpos]
    exact (GGK0MarkedComponents.component_of_realization M j hqs).2
  let e : C ≃* Q :=
    (C.equivMapOfInjective M.iota M.iota_inj).trans (MulEquiv.subgroupCongr hmap)
  exact ⟨j, hqs, ggHasLabel_quotCenter_of_mulEquiv e hlabel⟩

theorem e6_rawQuotientInner_of_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi) (hτ : M.tau = .E6)
    {C : Subgroup R} (hC : CFSG.Assembly.IsComponentOf C (ggFixSub phi))
    (hlabel : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (C ⧸ Subgroup.center C))
    {beta : MulAut R} (hbI : beta ∈ I) (hcomm : beta * phi = phi * beta)
    (hpres : ∀ c ∈ C, beta c ∈ C) : QuotientInner C beta := by
  obtain ⟨j, hqs, hjlabel⟩ := exists_rationalComponent_position_with_hasLabel M hC hlabel
  have htwo : (componentRoots (rootCharHom M.a) (M.repr j)).ncard = 2 := by
    exact e6_component_ncard_eq_two_of_hasLabel hτ M.setup M.a_torus M.a_pow M.a_ne
      (M.repr j) (M.qs j hqs) hjlabel
  obtain ⟨g, hg, hgeom⟩ := exists_modelActor_of_commute M hbI hcomm
  have hconn : (g : ModGL M.tau Omega) ∈ E6Centralizer1585.connectedCentralizer M := by
    have hle := e6_centralizer_le_torus_rootSpan_of_component_ncard_eq_two hτ M.a_pow (M.repr j) htwo
    have htorus : torusGroup M.tau Omega ≤ Subgroup.closure
        (Set.range (fun b : Fin M.tau.rank → Omegaˣ => rootDiagUnit M.tau b)) := by
      intro t ht
      obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
      exact Subgroup.subset_closure ⟨b, rfl⟩
    exact (sup_le_sup_right htorus _) (hle hgeom)
  exact rawQuotientInner_of_connected_modelActor M hC hlabel hpres g hg hconn

theorem e6_rawAction_labelAll_of_producer
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {tag : LargeEvenLieTag} (hp : RationalProducerOn Omega tag)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab 3)
    (htag : lab.tag = tag) (he : lab.tag = .E6 ∨ lab.tag = .twE6) :
    LargeEvenLabelAll lab (fun R _ I _ => RawActionAt R I) := by
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hp 3 lab hlab hpair htag)
  intro phi hphiI hphi1 hphi3 C hC hlabel beta hbetaI hcomm hpres
  have horder : orderOf phi = 3 := orderOf_eq_prime hphi3 hphi1
  obtain ⟨M⟩ := h phi hphiI horder
  have hτ : M.tau = .E6 := by
    have ht := M.row.type_eq
    rcases he with he | he
    all_goals
      rw [ggKacTypeOfLabel, he] at ht
      have hT : M.row.T = .E6 := (congrArg Prod.fst (Option.some.inj ht)).symm
      rw [← M.tau_eq, hT]
      rfl
  exact e6_rawQuotientInner_of_realization M hτ hC hlabel hbetaI hcomm hpres

theorem noSetupAt_E6_labelAll
    {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E6 ∨ lab.tag = .twE6) :
    LargeEvenLabelAll lab (fun R _ I _ => NoSetupAt R I) := by
  have hpair : GGKacExcPair lab 3 :=
    ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add lab.n, by tauto⟩
  have ha : LargeEvenLabelAll lab (fun R _ I _ => RawActionAt R I) := by
    rcases htag with he | he
    · exact e6_rawAction_labelAll_of_producer (Omega := AlgebraicClosure (ZMod 2))
        e6Producer_holds hlab hpair he (Or.inl he)
    · exact e6_rawAction_labelAll_of_producer (Omega := AlgebraicClosure (ZMod 2))
        twE6Producer_holds hlab hpair he (Or.inr he)
  exact LargeEvenLabelAll.mono (fun R _ I _ h => coverDescent_holds R I h) ha

end S2MathAs3_1619Final
