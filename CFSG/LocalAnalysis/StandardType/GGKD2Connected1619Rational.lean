module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587
public import CFSG.LocalAnalysis.StandardType.GGK0RationalProducerHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585
public import Certificates.Certificate1952
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGK0MarkedComponents
import CFSG.LocalAnalysis.StandardType.GGKD2ConnectedNativeHolds
import CFSG.LocalAnalysis.StandardType.GGKD2A1EightHolds
import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619CoverDescentHolds
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover

public section

namespace S2MathAs3_1619Final
open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.GGK0MarkedKacIface1587



theorem exists_modelActor_of_commute
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab p R I phi)
    {beta : MulAut R} (hbI : beta ∈ I) (hcomm : beta * phi = phi * beta) :
    ∃ g : M.setup.D.model, M.modelAction g = beta ∧
      (g : ModGL M.tau Omega) ∈ adjointGroup M.tau Omega ⊓
        Subgroup.centralizer {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit M.tau M.a} := by
  rw [← M.modelAction_range] at hbI
  obtain ⟨g, hg⟩ := hbI
  change M.modelAction g = beta at hg
  let a : M.setup.D.model :=
    ⟨CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit M.tau M.a, M.a_model⟩
  have hag : g * a = a * g := by
    apply M.modelAction_inj
    simp only [map_mul, a, M.action_eq, hg]
    exact hcomm
  refine ⟨g, hg, ((CFSG.HardMathSupport.Timmesfeld.LangTorus.LangDatum.mem_model
    (D := M.setup.D)).mp g.2).1, ?_⟩
  change (g : ModGL M.tau Omega) ∈ Subgroup.centralizer
    {CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit M.tau M.a}
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hag

theorem rawQuotientInner_of_connected_modelActor
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi)
    {C : Subgroup R} (hC : IsComponentOf C (ggFixSub phi))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (C ⧸ Subgroup.center C))
    {beta : MulAut R} (hpres : ∀ c ∈ C, beta c ∈ C)
    (g : M.setup.D.model) (hg : M.modelAction g = beta)
    (hconn : (g : ModGL M.tau Omega) ∈ E6Centralizer1585.connectedCentralizer M) :
    QuotientInner C beta := by
  have hτ : M.tau ≠ .G2 := by
    rw [← M.tau_eq]
    cases M.row.T <;> simp [GGK0MarkedKacIface1587.absTag]
  obtain ⟨j, hqs, hCpos⟩ := CFSG.StandardType.GGK0MarkedComponents.exists_component_position_of_realization
    Nat.prime_three (by norm_num) M hτ hC
  have hCeq : C = E6Centralizer1585.component M j := hCpos
  have hpres' : ∀ c ∈ E6Centralizer1585.component M j,
      M.modelAction g c ∈ E6Centralizer1585.component M j := by
    intro c hc
    rw [← hCeq] at hc ⊢
    rw [hg]
    exact hpres c hc
  have hlab' : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
      (E6Centralizer1585.component M j ⧸ Subgroup.center (E6Centralizer1585.component M j)) :=
    hCeq ▸ hlab
  have hinner : QuotientInner (E6Centralizer1585.component M j) (M.modelAction g) :=
    KD2Pieces1615.corner1584_connected_of_pieces KD2Pieces1615.connectedNativeAction_holds
      KD2Pieces1615.a1EightInnAutDerived_holds Omega lab R I phi M j hqs g hconn hpres' hlab'
  rw [hg] at hinner
  exact hCeq.symm ▸ hinner


theorem rawQuotientInner_of_centred_realization
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (M : MarkedRationalKacRealization Omega lab 3 R I phi) (hc : GGKacCentred lab 3)
    {C : Subgroup R} (hC : IsComponentOf C (ggFixSub phi))
    (hlab : GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥C ⧸ Subgroup.center ↥C))
    {beta : MulAut R} (hbI : beta ∈ I) (hcomm : beta * phi = phi * beta)
    (hpres : ∀ c ∈ C, beta c ∈ C) : QuotientInner C beta := by
  obtain ⟨g, hg, hgeom⟩ := exists_modelActor_of_commute M hbI hcomm
  exact rawQuotientInner_of_connected_modelActor M hC hlab hpres g hg
    (M.centred_centralizer_generated hc hgeom)

theorem rawAction_labelAll_of_centred_producer
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {tag : LargeEvenLieTag} (hp : RationalProducerOn Omega tag)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hpair : GGKacExcPair lab 3)
    (htag : lab.tag = tag) (hc : GGKacCentred lab 3) :
    LargeEvenLabelAll lab (fun R _ I _ => RawActionAt R I) := by
  refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hp 3 lab hlab hpair htag)
  intro phi hphiI hphi1 hphi3 C hC hlabel beta hbetaI hcomm hpres
  have horder : orderOf phi = 3 := orderOf_eq_prime hphi3 hphi1
  obtain ⟨M⟩ := h phi hphiI horder
  exact rawQuotientInner_of_centred_realization M hc hC hlabel hbetaI hcomm hpres

theorem noSetupAt_F4E7E8_labelAll
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8) :
    LargeEvenLabelAll lab (fun R _ I _ => NoSetupAt R I) := by
  have hpair : GGKacExcPair lab 3 :=
    ⟨Nat.prime_three, by norm_num, ggThree_dvd_two_pow_sub_or_add lab.n, by tauto⟩
  have hc : GGKacCentred lab 3 := by
    rcases htag with h | h | h <;> simp [GGKacCentred, h]
  have ha : LargeEvenLabelAll lab (fun R _ I _ => RawActionAt R I) := by
    rcases htag with h | h | h
    · exact rawAction_labelAll_of_centred_producer (Omega := AlgebraicClosure (ZMod 2))
        f4Producer_holds hlab hpair h hc
    · exact rawAction_labelAll_of_centred_producer (Omega := AlgebraicClosure (ZMod 2))
        e7Producer_holds hlab hpair h hc
    · exact rawAction_labelAll_of_centred_producer (Omega := AlgebraicClosure (ZMod 2))
        e8Producer_holds hlab hpair h hc
  exact LargeEvenLabelAll.mono (fun R _ I _ h => coverDescent_holds R I h) ha

end S2MathAs3_1619Final
