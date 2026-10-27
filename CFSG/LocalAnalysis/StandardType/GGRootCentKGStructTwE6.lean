module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructND
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcTwE6Root
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
import CFSG.LieType.Steinberg.Isogeny.E6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  RootCentExc

private theorem exists_model_frobQ {G : Type} [Group G] {f : ℕ} (hf : 1 ≤ f)
    {ψ : twistedE6Group 2 f →* G}
    (hker : ψ.ker ≤ Subgroup.center (twistedE6Group 2 f))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    ∃ (ψbar : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G)
      (π : twistedE6Group 2 f →*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      Function.Injective ψbar ∧ ψbar.range = ψ.range ∧ Function.Surjective π ∧
      π.ker = ψ.ker ∧ (∀ x, ψbar (π x) = ψ x) ∧
      (∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f))
          (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) := by
  obtain ⟨π, hπ, hπker, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hπker' : π.ker = ψ.ker :=
    hπker.trans (AutSt.ker_eq_center hker hC).symm
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  let eC : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≃*
      twistedE6Group 2 f ⧸ ψ.ker :=
    (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hπker')
  let ψbar : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G :=
    (QuotientGroup.kerLift ψ).comp eC.toMonoidHom
  have hcomp : ∀ x, ψbar (π x) = ψ x := by
    intro x
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π x) =
        (QuotientGroup.mk x : twistedE6Group 2 f ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ψbar, eC, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp,
      Function.comp_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]
  refine ⟨ψbar, π, (QuotientGroup.kerLift_injective ψ).comp eC.injective, ?_, hπ, hπker',
    hcomp, hπval⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := hπ x
    rw [hcomp]
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨π a, hcomp a⟩

private theorem pi_conj_xm_eq_pinnedX {f : ℕ}
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hπval : ∀ z, ((π z : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      ((e6IsogenyT (GaloisField 2 (2 * f))
        (z : e6Data_valid.minGroup (GaloisField 2 (2 * f))) :
        adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
          ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))))
    {x z : twistedE6Group 2 f} {c : GaloisField 2 (2 * f)}
    (hc : ((x⁻¹ * z * x : twistedE6Group 2 f) :
      e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
        e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
    ((π (x⁻¹ * z * x) : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c := by
  have h2 : (2 : GaloisField 2 (2 * f)) = 0 := CharTwo.two_eq_zero
  rw [hπval, hc]
  change ((e6Isogeny (GaloisField 2 (2 * f))
      (e6Data_valid.xm _ RootCentExc.e6HighRoot c) :
      adjointGroup .E6 (GaloisField 2 (2 * f))) :
        ModGL .E6 (GaloisField 2 (2 * f))) =
    pinnedX .E6 (GaloisField 2 (2 * f)) RootCentExc.e6HighRoot c
  rw [e6Isogeny_xm _ RootCentExc.isRoot_e6HighRoot, yPar,
    RootCentExc.coe_xPar_eq_pinnedX h2 _ RootCentExc.isRoot_e6HighRoot]
  have hδ : (relSignOr (rootOperatorFamily .E6) e6AdjData_valid RootCentExc.e6HighRoot :
      GaloisField 2 (2 * f)) = 1 := by
    have hm := relSignOr_mul_self (F := rootOperatorFamily .E6) (hD := e6AdjData_valid)
      (k := GaloisField 2 (2 * f)) RootCentExc.e6HighRoot
    set ε := (relSignOr (rootOperatorFamily .E6) e6AdjData_valid RootCentExc.e6HighRoot :
      GaloisField 2 (2 * f))
    have h' : (ε - 1) ^ 2 = 0 := by linear_combination hm + (1 - ε) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
  rw [hδ, one_mul]

private theorem exists_conj_pinnedX_one_torus {f : ℕ} {c : GaloisField 2 (2 * f)}
    (hc : c ≠ 0) (hcσ : frobQ 2 f c = c) :
    ∃ s ∈ graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f),
      s * pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c * s⁻¹ =
        pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot 1 := by
  obtain ⟨h, hh, -, hconj⟩ := exists_twistedE6_torus_conj_frame_prod (frobQ 2 f)
    (F := [e6HighestRoot]) (fun γ hγ => by
      rw [List.mem_singleton] at hγ
      subst hγ
      exact ⟨isRoot_e6HighestRoot, permLattice_e6HighestRoot⟩)
    (List.pairwise_singleton _ _) (fun _ => c) (fun γ _ => ⟨hc, hcσ⟩)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hconj
  exact ⟨h, hh, hconj⟩

private theorem exists_conj_pinnedX_one_of_model {f : ℕ} (hf : 1 ≤ f)
    {c : GaloisField 2 (2 * f)}
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    {x z : twistedE6Group 2 f}
    (hπz : ((π (x⁻¹ * z * x) : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f))) : ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
      pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot c)
    (hc0 : c ≠ 0) (hcσ : frobQ 2 f c = c) :
    ∃ s' : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      s' * π (x⁻¹ * z * x) * s'⁻¹ = stdRepC (frobQ_frobQ 2 f hf) 0 := by
  obtain ⟨s, hs, hconj⟩ := exists_conj_pinnedX_one_torus hc0 hcσ
  refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hπz, hconj]
  rfl

private theorem psi_conj_eq_model {G : Type} [Group G] {f : ℕ}
    {ψ : twistedE6Group 2 f →* G}
    {ψbar : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →* G}
    {π : twistedE6Group 2 f →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (hcomp : ∀ y, ψbar (π y) = ψ y) {u x z : twistedE6Group 2 f}
    {s' t : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (ht : s' * π (x⁻¹ * z * x) * s'⁻¹ = t) :
    ψ (u * z * u⁻¹) = ψbar (MulAut.conj (π (u * x) * s'⁻¹) t) := by
  rw [← ht, MulAut.conj_apply, ← hcomp]
  congr 1
  have h1 : π (u * x) * s'⁻¹ * (s' * π (x⁻¹ * z * x) * s'⁻¹) * (π (u * x) * s'⁻¹)⁻¹ =
      π (u * x) * π (x⁻¹ * z * x) * (π (u * x))⁻¹ := by group
  have h2 : π ((u * x) * (x⁻¹ * z * x) * (u * x)⁻¹) =
      π (u * x) * π (x⁻¹ * z * x) * (π (u * x))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [h1, ← h2]
  congr 1
  group

theorem ggRootCentKGStructTag_twistedE6_of
    (hpieces : ∀ (f : ℕ) (hf : 1 ≤ f),
      KGND.KGPiecesD (LayerSixE.twInndiagAut f) (stdRepC (frobQ_frobQ 2 f hf) 0)) :
    GGRootCentKGStructTag .twistedE6 := by
  intro G _ _ p n f ψ _ _ hadm _ hker _ _ hC _ _ r hr _ E hEN hEC _ hEinn
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨hr2, γ, ⟨hγ, hlong⟩, u, hru⟩ := hr
  obtain ⟨_, ⟨z, hz, rfl⟩, rfl⟩ := hru
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hr2 hEC ⊢
  obtain ⟨w, γ₀, hγ₀, hmax, hγw⟩ := hlong (Or.inr (Or.inr rfl))
  have hγ₀' : IsRoot .F4 γ₀ := isRoot_of_mem_twistedDatum_roots _ hγ₀
  have hγ₀eq : γ₀ = RootCentExc.f4HighRoot := RootCentExc.eq_f4HighRoot_of_le hγ₀'
    (hmax RootCentExc.f4HighRoot (by
      change RootCentExc.f4HighRoot ∈ (twistedDatum (GaloisField 2 (2 * f)) (frobQ 2 f)).roots
      rw [twistedDatum_roots]
      exact RootCentExc.isRoot_f4HighRoot))
  subst hγ₀eq
  subst hγw
  have hz1 : ψ (u * z * u⁻¹) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr2
    exact absurd hr2 (by norm_num)
  obtain ⟨x, c, hcθ, hc⟩ := RootCentExc.exists_conj_xm_highRoot_twE6 hf w hz
  obtain ⟨ψbar, π, hψbar_inj, hψbar_range, hπ, hπker, hcomp, hπval⟩ :=
    exists_model_frobQ (G := G) hf hker hC
  have hπz := pi_conj_xm_eq_pinnedX (f := f) hπval hc
  have hc0 : c ≠ 0 := by
    let z' : twistedE6Group 2 f := z
    have hc' : ((x⁻¹ * z' * x : twistedE6Group 2 f) :
        e6Data_valid.minGroup (GaloisField 2 (2 * f))) =
          e6Data_valid.xm _ RootCentExc.e6HighRoot c := hc
    rintro rfl
    have h1 : x⁻¹ * z' * x = 1 := Subtype.ext (by
      rw [hc', MinData.Valid.xm_zero]
      rfl)
    have hz1' : z' = 1 := by
      calc z' = x * (x⁻¹ * z' * x) * x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hzold : z = 1 := hz1'
    rw [hzold, mul_one, mul_inv_cancel, map_one] at hz1
    exact hz1 rfl
  obtain ⟨s', ht⟩ := exists_conj_pinnedX_one_of_model hf hπz hc0 hcθ
  let u' : twistedE6Group 2 f := u
  let β : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :=
    MulAut.conj (π (u' * x) * s'⁻¹)
  have hβ : β ∈ LayerSixE.twInndiagAut f := Subgroup.mem_sup_left ⟨_, rfl⟩
  have hDz : KGND.KGPiecesD (LayerSixE.twInndiagAut f)
      (β (stdRepC (frobQ_frobQ 2 f hf) 0)) :=
    KGND.KGPiecesD.map_of_mem (hpieces f hf) hβ
  have hval : ψ (u * z * u⁻¹) = ψbar (β (stdRepC (frobQ_frobQ 2 f hf) 0)) :=
    psi_conj_eq_model hcomp ht
  have hE : E ≤ Subgroup.centralizer
      ({ψbar (β (stdRepC (frobQ_frobQ 2 f hf) 0))} : Set G) := by
    rw [← hval]
    exact hEC
  have hact : ∀ ε ∈ E, ∃ δ ∈ LayerSixE.twInndiagAut f,
      ∀ y : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        ε⁻¹ * ψbar y * ε = ψbar (δ y) := by
    intro ε hε
    obtain ⟨δ, hδ, hδind⟩ := LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hπker.symm.le
      (c := ε⁻¹) (inv_mem (hEN hε)) (hEinn ε⁻¹ (inv_mem hε))
    refine ⟨δ, hδ, fun y => ?_⟩
    obtain ⟨ŷ, rfl⟩ := hπ y
    obtain ⟨y', hy'⟩ := LayerSixE.exists_conj_eq (inv_mem (hEN hε)) ŷ
    have hδy : π y' = δ (π ŷ) := hδind ŷ y' hy'
    calc ε⁻¹ * ψbar (π ŷ) * ε
        = ε⁻¹ * ψ ŷ * ε := congrArg (fun z => ε⁻¹ * z * ε) (hcomp ŷ)
      _ = ε⁻¹ * ψ ŷ * (ε⁻¹)⁻¹ := congrArg (fun z => ε⁻¹ * ψ ŷ * z) (inv_inv ε).symm
      _ = ψ y' := hy'.symm
      _ = ψbar (π y') := (hcomp y').symm
      _ = ψbar (δ (π ŷ)) := congrArg ψbar hδy
  obtain ⟨𝒥, hcover, hpiece⟩ := hDz G ψbar hψbar_inj E hE hact
  have hC₀ : ψbar.range ⊓
      Subgroup.centralizer ({ψbar (β (stdRepC (frobQ_frobQ 2 f hf) 0))} : Set G) =
      ψ.range ⊓ Subgroup.centralizer ({ψ (u * z * u⁻¹)} : Set G) := by
    rw [hψbar_range]
    exact congrArg (fun x : G => ψ.range ⊓ Subgroup.centralizer ({x} : Set G)) hval.symm
  refine ⟨𝒥, ?_, ?_⟩
  · intro P hP hPperf
    rw [← hC₀] at hP
    exact hcover P hP hPperf
  · intro J hJ
    rw [← hC₀]
    exact hpiece J hJ

end CFSG.StandardType

end
