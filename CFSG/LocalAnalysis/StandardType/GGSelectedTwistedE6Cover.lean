module

public import CFSG.LieType.Steinberg.Minuscule.E6TorusLang
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourModel
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6
public import CFSG.LocalAnalysis.StandardType.PhanEMinDescent
public import CFSG.ClassicalInvolution.WeakCT.TwistedE6MinusculeFixedField
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddLemmas
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLang
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcOrbit
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCStdEnvelope
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusExcOrbit

public section

namespace CFSG.StandardType.TwistedE6SourceCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.Steinberg.Exceptional


variable {Ω : Type} [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
  [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem exists_minuscule_lift_of_twisted_fixed (Fr : Ω →+* Ω)
    {r : ModGL Tag.E6 Ω} (hr : r ∈ TwistedDiag.Rgrp Ω Fr) (hr3 : r ^ 3 = 1) :
    ∃ t : e6Data_valid.minGroup Ω,
      e6IsogenyAlgebraic t = r ∧ t ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup Ω) ∧
      CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr t * t⁻¹ ∈
        Subgroup.center (e6Data_valid.minGroup Ω) := by
  have hrange : r ∈ (e6IsogenyAlgebraic (Ω := Ω)).range := by
    rw [range_e6IsogenyAlgebraic]
    exact hr.1
  obtain ⟨t, ht⟩ := hrange
  refine ⟨t, ht, ?_, ?_⟩
  · rw [← ker_e6IsogenyAlgebraic_eq_center, MonoidHom.mem_ker, map_pow, ht, hr3]
  · rw [← ker_e6IsogenyAlgebraic_eq_center, MonoidHom.mem_ker, map_mul, map_inv,
      e6IsogenyAlgebraic_sigma, ht]
    rw [show twistHom TwistTag.E6 Ω Fr r = r from hr.2, mul_inv_cancel]


theorem exists_minuscule_lift_of_twInndiag {f : ℕ} (hf : 1 ≤ f)
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    {alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (halpha : alpha ∈ LayerSixE.twInndiagAut f) (halpha3 : alpha ^ 3 = 1) :
    ∃ t : e6Data_valid.minGroup Ω,
      t ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup Ω) ∧
      CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr t * t⁻¹ ∈
        Subgroup.center (e6Data_valid.minGroup Ω) ∧
      e6IsogenyAlgebraic t ∈ TwistedDiag.Rgrp Ω Fr ∧
      e6IsogenyAlgebraic t ^ 3 = 1 ∧ t ^ 9 = 1 ∧
      (t ∈ Subgroup.center (e6Data_valid.minGroup Ω) ↔ alpha = 1) ∧
      ∀ c : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        baseChangeGL (τ := Tag.E6) (algebraMap (GaloisField 2 (2 * f)) Ω) (alpha c).1 =
          e6IsogenyAlgebraic t *
            baseChangeGL (τ := Tag.E6) (algebraMap (GaloisField 2 (2 * f)) Ω) c.1 *
              (e6IsogenyAlgebraic t)⁻¹ := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : GaloisField 2 (2 * f), frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  let Phi := NoOffTwE6Three.rgrpConjAut hf hK (frobQEquiv hf) hσ Fr hFr
  have hPhi : Phi.range = LayerSixE.twInndiagAut f := by
    refine (NoOffTwE6Three.rgrpConjAut_range hf hK (frobQEquiv hf) hσ Fr hFr).trans ?_
    rw [LayerSixE.twInndiagAut]
    exact (inn_sup_compatParamAut_eq_range_twConj
      (K := GaloisField 2 (2 * f)) (σ := frobQEquiv hf)).symm
  have hmem : alpha ∈ Phi.range := by rwa [hPhi]
  obtain ⟨r, hr⟩ := hmem
  have hr3 : r ^ 3 = 1 := by
    apply NoOffTwE6Three.rgrpConjAut_injective hf hK (frobQEquiv hf) hσ Fr hFr
    change Phi (r ^ 3) = Phi 1
    rw [map_pow, hr, map_one]
    with_unfolding_all exact halpha3
  have hr3val : r.1 ^ 3 = 1 := congrArg Subtype.val hr3
  obtain ⟨t, ht, ht3, htF⟩ := exists_minuscule_lift_of_twisted_fixed Fr r.2 hr3val
  have ht9 : t ^ 9 = 1 := by
    have hz : e6IsogenyAlgebraic (t ^ 3) = 1 := by rw [map_pow, ht, hr3val]
    simpa only [← pow_mul] using
      (e6IsogenyAlgebraic_centralThree (Ω := Ω)).exp_three (t ^ 3) hz
  have hrone : r = 1 ↔ alpha = 1 := by
    constructor
    · intro h
      have hr' := hr
      rw [h, map_one] at hr'
      with_unfolding_all exact hr'.symm
    · intro h
      apply NoOffTwE6Three.rgrpConjAut_injective hf hK (frobQEquiv hf) hσ Fr hFr
      change Phi r = Phi 1
      rw [hr, map_one]
      with_unfolding_all exact h
  have htcentral : t ∈ Subgroup.center (e6Data_valid.minGroup Ω) ↔ alpha = 1 := by
    rw [← ker_e6IsogenyAlgebraic_eq_center, MonoidHom.mem_ker, ht]
    exact ⟨fun h => hrone.mp (Subtype.ext h), fun h => congrArg Subtype.val (hrone.mpr h)⟩
  refine ⟨t, ht3, htF, ht.symm ▸ r.2, ht.symm ▸ hr3val, ht9, htcentral, ?_⟩
  intro c
  rw [ht]
  have h := SCFourCover.baseChange_rgrpConjAut hf hK (frobQEquiv hf) hσ Fr hFr r c
  change baseChangeGL (τ := Tag.E6) (algebraMap (GaloisField 2 (2 * f)) Ω) (Phi r c).1 =
    r.1 * baseChangeGL (τ := Tag.E6) (algebraMap (GaloisField 2 (2 * f)) Ω) c.1 * r.1⁻¹ at h
  rwa [hr] at h

end CFSG.StandardType.TwistedE6SourceCover

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar


theorem GGConfig.exists_marked_source_centralizer_of_twistedE6_qTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x)
    (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω]
    [Algebra.IsAlgebraic (ZMod 2) Ω] [Algebra (GaloisField 2 (2 * f)) Ω]
    [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f) :
    f = 1 ∧ ∃ (lab : LargeEvenLabel) (M : Subgroup (ggU .twistedE6 0 f).K)
      (rho : ↥M →* ↥L) (e : ↥M ⧸ Subgroup.center ↥M ≃* ↥L ⧸ Subgroup.center ↥L)
      (eta : (ggU .twistedE6 0 f).K →* e6Data_valid.minGroup Ω)
      (t : e6Data_valid.minGroup Ω),
      LargeEvenInLambda2 lab ∧ lab.n = 1 ∧ lab ≠ ⟨.twD, 2, 1⟩ ∧ lab.tag ≠ .B2der ∧
      IsComponentOf M ((Subgroup.centralizer {x}).comap psi) ∧ M.map psi = L ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center ↥M ∧
      rho.ker = psi.ker.comap M.subtype ∧ L.subtype.comp rho = psi.comp M.subtype ∧
      (∀ m : ↥M, e (QuotientGroup.mk m) = QuotientGroup.mk (rho m)) ∧
      MarkedModel lab (↥M ⧸ Subgroup.center ↥M) ∧ MarkedModel lab (↥L ⧸ Subgroup.center ↥L) ∧
      Function.Injective eta ∧
      (∀ u, eta u = minBC e6Data_valid (algebraMap (GaloisField 2 (2 * f)) Ω)
        (Subtype.val (show twistedE6Group 2 f from u))) ∧
      (∀ u, CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr (eta u) = eta u) ∧
      t ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup Ω) ∧
      CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr t * t⁻¹ ∈
        Subgroup.center (e6Data_valid.minGroup Ω) ∧
      t ^ 9 = 1 ∧
      (t ∈ Subgroup.center (e6Data_valid.minGroup Ω) ↔
        x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) ∧
      (∀ u u', psi u' = x * psi u * x⁻¹ →
        e6IsogenyAlgebraic (eta u') = e6IsogenyAlgebraic t *
          e6IsogenyAlgebraic (eta u) * (e6IsogenyAlgebraic t)⁻¹) ∧
      IsComponentOf (M.map eta) (eta.range ⊓ Subgroup.centralizer {t}) := by
  obtain ⟨hfield, lab, M, rho, e, hlab, hn, htwD, hB2, hM, hmap,
    hrho, hrhoker, hrhokerEq, hrhoEq, he, hmodelM, hmodelL⟩ :=
    hC.exists_marked_source_component_of_twistedE6_qTwo hq psi hpsi hdiag
  obtain ⟨pi, alpha, _, hpiker, hpival, halpha, halpha3, hind, htrivial⟩ :=
    hC.exists_native_action_of_twistedE6 psi hpsi hdiag
  have hf : 1 ≤ f := hpsi.1.1.2.1
  obtain ⟨t, ht3, htF, _, _, ht9, htcentral, htact⟩ :=
    TwistedE6SourceCover.exists_minuscule_lift_of_twInndiag hf Fr hFr halpha halpha3
  let eta : (ggU .twistedE6 0 f).K →* e6Data_valid.minGroup Ω :=
    (minBC e6Data_valid (algebraMap (GaloisField 2 (2 * f)) Ω)).comp
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup
        (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype
  have heta : Function.Injective eta :=
    (CFSG.ClassicalInvolution.Phan.PhanE.minBC_injective' e6Data_valid
      (algebraMap (GaloisField 2 (2 * f)) Ω)).comp Subtype.val_injective
  let bc : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      ModGL Tag.E6 Ω :=
    (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype
  have hbc : Function.Injective bc :=
    (baseChangeGL_injective (algebraMap (GaloisField 2 (2 * f)) Ω)).comp Subtype.val_injective
  have hval (u : (ggU .twistedE6 0 f).K) : e6IsogenyAlgebraic (eta u) = bc (pi u) := by
    change e6IsogenyAlgebraic (minBC e6Data_valid
      (algebraMap (GaloisField 2 (2 * f)) Ω) (Subtype.val (show twistedE6Group 2 f from u))) = _
    rw [e6IsogenyAlgebraic_minBC]
    change baseChangeGL (τ := Tag.E6) (algebraMap (GaloisField 2 (2 * f)) Ω)
      ((e6Isogeny (GaloisField 2 (2 * f))
        (Subtype.val (show twistedE6Group 2 f from u))).1) = bc (pi u)
    change _ = baseChangeGL (τ := Tag.E6) (algebraMap (GaloisField 2 (2 * f)) Ω) (pi u).1
    congr 1
    with_unfolding_all exact (hpival u).symm
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hnativeFixed :
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)).map
        (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)) ≤ TwistedDiag.Rgrp Ω Fr :=
    (exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 Nat.prime_two hf
      (GaloisField 2 (2 * f)) hK (frobQ 2 f)
      (fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c) Ω Fr hFr).2.1
  have hperfect : Group.IsPerfect (ggU .twistedE6 0 f).K :=
    (CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hf).1
  have hetaFixed : ∀ u, CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr (eta u) = eta u :=
    CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq e6IsogenyAlgebraic
      ker_e6IsogenyAlgebraic_eq_center.le hperfect
      ((CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr).comp eta) eta (fun u => by
        change e6IsogenyAlgebraic (CFSG.LieType.Steinberg.TwistedE6.sigma Ω Fr (eta u)) =
          e6IsogenyAlgebraic (eta u)
        rw [e6IsogenyAlgebraic_sigma, hval u]
        exact (hnativeFixed (Subgroup.mem_map_of_mem _ (pi u).2)).2)
  have hcomp : e6IsogenyAlgebraic.comp eta = bc.comp pi := by
    apply MonoidHom.ext
    intro u
    exact hval u
  have hk : (e6IsogenyAlgebraic.comp eta).ker ≤ Subgroup.center (ggU .twistedE6 0 f).K := by
    rw [hcomp, MonoidHom.ker_comp_of_injective pi bc hbc, hpiker]
  have hreal : LayerSixE.GGInduces (e6IsogenyAlgebraic.comp eta) psi x
      (MulAut.conj (e6IsogenyAlgebraic t)) := by
    intro u u' hu
    change e6IsogenyAlgebraic (eta u') =
      e6IsogenyAlgebraic t * e6IsogenyAlgebraic (eta u) * (e6IsogenyAlgebraic t)⁻¹
    calc
      _ = bc (pi u') := hval u'
      _ = bc (alpha (pi u)) := congrArg bc (hind u u' hu)
      _ = e6IsogenyAlgebraic t * bc (pi u) * (e6IsogenyAlgebraic t)⁻¹ := htact (pi u)
      _ = _ := by rw [hval u]
  have hx : x ∈ Subgroup.normalizer (psi.range : Set G) := by
    simpa only [hpsi.2.1.1] using ggPsiInnerDiag_mem_normalizer_twistedE6 hpsi hdiag
  have hgeom : IsComponentOf (M.map eta) (eta.range ⊓ Subgroup.centralizer {t}) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr
      (LayerSixE.GGInduces.isComponentOf_map_centralizer_lift eta heta e6IsogenyAlgebraic
        ker_e6IsogenyAlgebraic_eq_center.le t hreal hk hx
        (CFSG.Assembly.isComponentOf_iff_open.mp hM))
  exact ⟨hfield, lab, M, rho, e, eta, t, hlab, hn, htwD, hB2, hM, hmap,
    hrho, hrhoker, hrhokerEq, hrhoEq, he, hmodelM, hmodelL, heta, fun _ => rfl,
    hetaFixed, ht3, htF, ht9, htcentral.trans htrivial, hreal, hgeom⟩

open CFSG.LieType.Universal

theorem GGConfig.exists_source_centralizer_of_twistedE6_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x)
    {M : Subgroup (ggU .twistedE6 0 f).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L)
    (Omega : Type) [Field Omega] [CharP Omega 2] [Algebra (ZMod 2) Omega]
    [Algebra.IsAlgebraic (ZMod 2) Omega] [Algebra (GaloisField 2 (2 * f)) Omega]
    [IsAlgClosure (GaloisField 2 (2 * f)) Omega]
    (Fr : Omega →+* Omega) (hFr : ∀ c, Fr c = c ^ 2 ^ f) :
    f = 1 ∧ ∃ (eta : (ggU .twistedE6 0 f).K →* e6Data_valid.minGroup Omega)
      (t : e6Data_valid.minGroup Omega),
      Function.Injective eta ∧
      (∀ u, eta u = minBC e6Data_valid (algebraMap (GaloisField 2 (2 * f)) Omega)
        (Subtype.val (show twistedE6Group 2 f from u))) ∧
      (∀ u, CFSG.LieType.Steinberg.TwistedE6.sigma Omega Fr (eta u) = eta u) ∧
      t ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup Omega) ∧
      CFSG.LieType.Steinberg.TwistedE6.sigma Omega Fr t * t⁻¹ ∈
        Subgroup.center (e6Data_valid.minGroup Omega) ∧
      t ^ 9 = 1 ∧
      (t ∈ Subgroup.center (e6Data_valid.minGroup Omega) ↔
        x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) ∧
      (∀ u u', psi u' = x * psi u * x⁻¹ →
        e6IsogenyAlgebraic (eta u') = e6IsogenyAlgebraic t *
          e6IsogenyAlgebraic (eta u) * (e6IsogenyAlgebraic t)⁻¹) ∧
      CFSG.Assembly.IsComponentOf (M.map eta) (eta.range ⊓ Subgroup.centralizer {t}) := by
  obtain ⟨hf, lab, M0, rho0, e0, eta, t, hl, hn, hne, hB2, hM0, hM0map,
      hrho0, hrho0ker, hrho0kerEq, hrho0Eq, he0, hmodelM0, hmodelL,
      heta, hval, hfixed, ht3, htFr, ht9, htcentral, hact, hcomponent⟩ :=
    hC.exists_marked_source_centralizer_of_twistedE6_qTwo hq psi hpsi hdiag Omega Fr hFr
  have hsame : M0 = M := SCFourCover.eq_of_map_eq hpsi.2.1.2
    (SCFourCover.commutator_eq_self_of_isComponentOf hM0)
    (SCFourCover.commutator_eq_self_of_isComponentOf hM) (hM0map.trans hML.symm)
  subst M0
  exact ⟨hf, eta, t, heta, hval, hfixed, ht3, htFr, ht9, htcentral, hact, hcomponent⟩

open CFSG.StandardType.GGFinModel

theorem GGConfig.exists_fixed_source_centralizer_of_twistedE6_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x)
    {M : Subgroup (ggU .twistedE6 0 f).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L) :
    f = 1 ∧ ∃ (eta : (ggU .twistedE6 0 f).K →* e6Data_valid.minGroup GGL)
      (t : e6Data_valid.minGroup GGL),
      Function.Injective eta ∧
      (∀ u, eta u = minBC e6Data_valid (ggRatEmb (2 * f))
        (Subtype.val (show twistedE6Group 2 f from u))) ∧
      eta.range = CFSG.LieType.Steinberg.TwistedE6.fixedGroup GGL (ggFrobT f) ∧
      t ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup GGL) ∧
      CFSG.LieType.Steinberg.TwistedE6.sigma GGL (ggFrobT f) t * t⁻¹ ∈
        Subgroup.center (e6Data_valid.minGroup GGL) ∧
      t ^ 9 = 1 ∧
      (t ∈ Subgroup.center (e6Data_valid.minGroup GGL) ↔
        x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) ∧
      (∀ u u', psi u' = x * psi u * x⁻¹ →
        e6IsogenyAlgebraic (eta u') = e6IsogenyAlgebraic t *
          e6IsogenyAlgebraic (eta u) * (e6IsogenyAlgebraic t)⁻¹) ∧
      CFSG.Assembly.IsComponentOf (M.map eta)
        (CFSG.LieType.Steinberg.TwistedE6.fixedGroup GGL (ggFrobT f) ⊓
          Subgroup.centralizer {t}) := by
  letI : Algebra (GaloisField 2 (2 * f)) GGL := (ggRatEmb (2 * f)).toAlgebra
  letI : IsScalarTower (ZMod 2) (GaloisField 2 (2 * f)) GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : IsAlgClosure (GaloisField 2 (2 * f)) GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2)
        (L := GaloisField 2 (2 * f)) }
  obtain ⟨hf, eta, t, heta, hval, hfixed, ht3, htFr, ht9, htcentral, hact, hcomponent⟩ :=
    GGConfig.exists_source_centralizer_of_twistedE6_component hC hq psi hpsi hdiag hM hML
      GGL (ggFrobT f) (ggFrobT_apply f)
  have hrange : eta.range = CFSG.LieType.Steinberg.TwistedE6.fixedGroup GGL (ggFrobT f) := by
    apply le_antisymm
    · rintro g ⟨u, rfl⟩
      rw [CFSG.LieType.Steinberg.TwistedE6.mem_fixedGroup]
      exact hfixed u
    · intro g hg
      rw [CFSG.LieType.Steinberg.TwistedE6.mem_fixedGroup] at hg
      have hdesc := GGFinModel.twisted_fixed_mem_minBC_range hpsi.1.1.2.1 hg
      obtain ⟨u, hu, hu_eq⟩ := Subgroup.mem_map.mp hdesc
      let v : (ggU .twistedE6 0 f).K := (⟨u, hu⟩ : twistedE6Group 2 f)
      refine ⟨v, (hval v).trans ?_⟩
      simpa only [v, RingHom.algebraMap_toAlgebra] using hu_eq
  refine ⟨hf, eta, t, heta, ?_, hrange, ht3, htFr, ht9, htcentral, hact, ?_⟩
  · intro u
    simpa only [RingHom.algebraMap_toAlgebra] using hval u
  · simpa only [hrange] using hcomponent


open CFSG.LieType.Steinberg CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem TwistedE6SourceCover.exists_native_langSetup
    (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (halpha : alpha ∈ LayerSixE.twInndiagAut 1) (halpha3 : alpha ^ 3 = 1)
    (halpha_ne : alpha ≠ 1) :
    ∃ (S : LangSetup TwistTag.E6.tag GGL 5) (a : Fin TwistTag.E6.tag.rank → GGLˣ)
      (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
        ModGL TwistTag.E6.tag GGL),
      S.D.q = 2 ^ 1 ∧ S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT 1) ∧
      rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit TwistTag.E6.tag a ≠ 1 ∧
      Function.Injective iota ∧ iota.range = S.Γ ∧
      (∀ c, iota (alpha c) = rootDiagUnit TwistTag.E6.tag a * iota c * (rootDiagUnit TwistTag.E6.tag a)⁻¹) ∧
      (∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
        baseChangeGL (ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1)))) := by
  letI : Algebra (GaloisField 2 (2 * 1)) GGL := (ggRatEmb (2 * 1)).toAlgebra
  letI : IsScalarTower (ZMod 2) (GaloisField 2 (2 * 1)) GGL :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  letI : IsAlgClosure (GaloisField 2 (2 * 1)) GGL :=
    { isAlgClosed := inferInstance
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := ZMod 2)
        (L := GaloisField 2 (2 * 1)) }
  obtain ⟨t, ht3, htFr, hr, hr3, ht9, htcentral, hact⟩ :=
    TwistedE6SourceCover.exists_minuscule_lift_of_twInndiag le_rfl
      (ggFrobT 1) (ggFrobT_apply 1) halpha halpha3
  let r : ModGL TwistTag.E6.tag GGL := e6IsogenyAlgebraic t
  have hr1 : r ≠ 1 := by
    intro h
    have hc : t ∈ Subgroup.center (e6Data_valid.minGroup GGL) := by
      rw [← ker_e6IsogenyAlgebraic_eq_center, MonoidHom.mem_ker]
      exact h
    exact halpha_ne (htcentral.mp hc)
  have hconj : ∃ g ∈ adjointGroup TwistTag.E6.tag GGL, g⁻¹ * r * g ∈ torusGroup TwistTag.E6.tag GGL :=
    exists_conj_torusGroup_of_prime_order
      (isAlgebraic_zmod_algebraicClosure_of_finite (ZMod 2) 2)
      Nat.prime_three (by decide) hr.1 hr3
  obtain ⟨D, hPhi, hDq, hmem⟩ := exists_langDatum_of_toral_twisted
    TwistTag.E6 1 le_rfl hr.2 hconj
  let iota0 : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL :=
    (baseChangeGL (ggRatEmb (2 * 1))).comp
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)).subtype
  have hiota0 : Function.Injective iota0 :=
    (baseChangeGL_injective _).comp Subtype.val_injective
  have hGamma : D.Γ = iota0.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := by
    rw [show iota0.range = (graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * 1)) (frobQ 2 1)).map (baseChangeGL (ggRatEmb (2 * 1))) by
      dsimp only [iota0]
      rw [MonoidHom.range_comp, Subgroup.range_subtype]]
    exact Γ_eq_map_twistedE6RootGroup (K := GaloisField 2 (2 * 1)) (L := GGL)
      (ℓ := 2) (f := 1) (σ := frobQEquiv (show 1 ≤ (1 : ℕ) from le_rfl))
      (Fr := ggFrobT 1) Nat.prime_two le_rfl
      (card_galoisField_two_mul 2 1 le_rfl) (frobQ_apply 2 1) (ggFrobT_apply 1) D hPhi
  have hfin : Finite D.model := finite_model_twistedE6 (K := GaloisField 2 (2 * 1)) (L := GGL)
    (ℓ := 2) (f := 1) (σ := frobQEquiv (show 1 ≤ (1 : ℕ) from le_rfl))
    (Fr := ggFrobT 1) Nat.prime_two le_rfl
    (card_galoisField_two_mul 2 1 le_rfl) (frobQ_apply 2 1) (ggFrobT_apply 1) D hPhi
  have hact0 : ∀ c, iota0 (alpha c) = r * iota0 c * r⁻¹ := by
    intro c
    change baseChangeGL (τ := Tag.E6) (ggRatEmb (2 * 1)) (alpha c).1 =
      e6IsogenyAlgebraic t * baseChangeGL (τ := Tag.E6) (ggRatEmb (2 * 1)) c.1 *
        (e6IsogenyAlgebraic t)⁻¹
    with_unfolding_all
      simpa only [RingHom.algebraMap_toAlgebra] using hact c
  obtain ⟨S, a, iota, hSD, hT, hap, h1, hinj, hrange, hcompat, hg0⟩ :=
    exists_langSetup_conj_of_toral_datum Nat.prime_two le_rfl D hDq
      Nat.prime_five (by decide) (Or.inl le_rfl) hfin iota0 hiota0 hGamma alpha hact0 hmem hr3 hr1
  subst hSD
  let iota' := (MulAut.conj S.D.g0⁻¹).toMonoidHom.comp iota0
  refine ⟨S, a, iota', hDq, hPhi, hT, hap, h1,
    (MulAut.conj S.D.g0⁻¹).injective.comp hiota0, ?_, ?_, ?_⟩
  · show _ = S.D.Γ
    rw [hGamma]
    exact MonoidHom.range_comp _ _
  · intro c
    change S.D.g0⁻¹ * iota0 (alpha c) * S.D.g0 =
      rootDiagUnit TwistTag.E6.tag a * (S.D.g0⁻¹ * iota0 c * S.D.g0) * (rootDiagUnit TwistTag.E6.tag a)⁻¹
    rw [hact0 c, ← hg0]
    group
  · intro c
    change S.D.g0 * (S.D.g0⁻¹ * iota0 c * S.D.g0) * S.D.g0⁻¹ = iota0 c
    group

theorem TwistedE6SourceCover.exists_native_rationalComponent
    (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (halpha : alpha ∈ LayerSixE.twInndiagAut 1) (halpha3 : alpha ^ 3 = 1)
    (halpha_ne : alpha ≠ 1)
    (N : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hN : CFSG.Assembly.IsComponentOf N
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup alpha)) :
    ∃ (S : LangSetup TwistTag.E6.tag GGL 5) (a : Fin TwistTag.E6.tag.rank → GGLˣ)
      (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
        ModGL TwistTag.E6.tag GGL),
      S.D.q = 2 ^ 1 ∧ S.D.Φ = twistHom TwistTag.E6 GGL (ggFrobT 1) ∧
      rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
      rootDiagUnit TwistTag.E6.tag a ≠ 1 ∧ Function.Injective iota ∧ iota.range = S.Γ ∧
      (∀ c, iota (alpha c) = rootDiagUnit TwistTag.E6.tag a * iota c *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹) ∧
      (∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
        baseChangeGL (ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1)))) ∧
      ∃ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
        N.map iota = rationalComponent S.ρ S.Γ (rootCharHom a) i := by
  obtain ⟨S, a, iota, hq, hPhi, hT, hap, h1, hinj, hrange, hcompat, hval⟩ :=
    TwistedE6SourceCover.exists_native_langSetup alpha halpha halpha3 halpha_ne
  have hmap : CFSG.Open.IsComponentOf (N.map iota)
      ((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup alpha).map iota) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map iota
      (fun c hc => by
        have hc1 : c = 1 := hinj (hc.trans (map_one iota).symm)
        rw [hc1]
        exact Subgroup.one_mem _) (CFSG.Assembly.isComponentOf_iff_open.mp hN)
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.map_fixSubgroup_eq_of_conj
    iota hinj alpha (rootDiagUnit TwistTag.E6.tag a) hcompat
  rw [hrange] at hfix
  rw [hfix] at hmap
  obtain ⟨i, hqs, hEq⟩ := LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2
    S (by decide) Nat.prime_three
      (by
        intro hzero
        have hdiv : 2 ∣ 3 := (CharP.cast_eq_zero_iff GGL 2 3).mp hzero
        norm_num at hdiv) hT hap h1 hmap
  exact ⟨S, a, iota, hq, hPhi, hT, hap, h1, hinj, hrange, hcompat, hval, i, hqs, hEq⟩


theorem TwistedE6SourceCover.componentOrbitLength_eq_one_of_marked_native
    (N : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (hmodel : MarkedModel lab (↥N ⧸ Subgroup.center ↥N))
    (S : LangSetup TwistTag.E6.tag GGL 5) (a : Fin TwistTag.E6.tag.rank → GGLˣ)
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hiota : Function.Injective iota) (hq : S.D.q = 2)
    (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit TwistTag.E6.tag a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hposition : N.map iota = rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  classical
  have hstd : RCKRP.RCKADEShape S.ρ (rootCharHom a) i :=
    RCKRP.rckStdEnvelope_holds TwistTag.E6.tag (Or.inr (Or.inl rfl)) S 3
      Nat.prime_three (by decide) a hT h1 hap i hqs
  have hsr := LangRat.componentOrbitLength_mul_compRank_le S hT i
  have hs0 := (outer_componentOrbitLength_spec S hT i).1
  by_cases hr4 : 4 ≤ compRank (componentRoots (rootCharHom a) i)
  · change componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) *
      compRank (componentRoots (rootCharHom a) i) ≤ 6 at hsr
    by_contra hne
    have h2 : 2 ≤ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) := by omega
    have h8 : 8 ≤ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) *
        compRank (componentRoots (rootCharHom a) i) :=
      (Nat.mul_le_mul_left 2 hr4).trans
        (Nat.mul_le_mul_right (compRank (componentRoots (rootCharHom a) i)) h2)
    omega
  have hr3 : compRank (componentRoots (rootCharHom a) i) ≤ 3 := by omega
  have hA := FieldTwoExc.typeA_of_compRank_le_three (Or.inr (Or.inl rfl)) hstd hr3
  obtain ⟨b, hdeg, hrank, hinn, hsu, hRL⟩ :=
    TablePThreeKG.rationalLabel_typeA S Nat.prime_three hT hap h1 i hA hqs
  let R : Subgroup (ModGL TwistTag.E6.tag GGL) := rationalComponent S.ρ S.Γ (rootCharHom a) i
  let etaN : ↥N →* ModGL TwistTag.E6.tag GGL := iota.comp N.subtype
  have hNinj : Function.Injective etaN := hiota.comp Subtype.val_injective
  have hNrange : etaN.range = R := by
    dsimp only [etaN, R]
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hposition]
  let e : ↥N ≃* ↥R := (MonoidHom.ofInjective hNinj).trans (MulEquiv.subgroupCongr hNrange)
  let eZ := QuotientGroup.congr (Subgroup.center ↥N) (Subgroup.center ↥R) e
    (Subgroup.map_center_eq e)
  have hMarkR : MarkedModel lab (↥R ⧸ Subgroup.center ↥R) := MarkedModel.of_mulEquiv eZ hmodel
  have hna : ∃ u v : ↥R ⧸ Subgroup.center ↥R, u * v ≠ v * u := hqs.2.2
  have hMarkB : MarkedModel b (↥R ⧸ Subgroup.center ↥R) := by
    apply largeEvenRawDatum_elim_const
    refine largeEvenRawDatum_imp hRL.1 ?_ ?_ hRL.2
    · rintro Q _ I F ⟨e0⟩
      obtain ⟨u, v, huv⟩ := hna
      refine ⟨e0 u, e0 v, ?_⟩
      intro h
      apply huv
      apply e0.injective
      simpa only [map_mul] using h
    · rintro Q _ I F ⟨e0⟩ hM
      exact MarkedModel.of_mulEquiv e0.symm hM
  have hbtag : b.tag = .A ∨ b.tag = .twA := by
    rcases hstd with h | ⟨hk, -, -⟩ | hk | ⟨-, h4, -⟩ | hk | ⟨-, hE⟩ | hk
    · exact Or.inl (hinn (CFSG.LocalAnalysis.GLTheoremA.RationalModel.twistKind_eq_inner_of_compRank_eq_one S i h))
    · exact Or.inl (hinn hk)
    · exact Or.inr (hsu hk)
    · omega
    · have := FieldTwoExc.four_le_compRank_of_twoD hk
      omega
    · rcases hE with ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ <;> omega
    · rcases FieldTwoExc.exc_cases hk with ⟨h6, -⟩ | ⟨h4, -⟩ <;> omega
  have hbchar : markChar b = 2 := by
    rcases hbtag with h | h <;> simp [markChar, h]
  have hbcls : markTag b = .PSL ∨ markTag b = .PSU ∨ markTag b = .PSp ∨
      markTag b = .POmegaPlus ∨ markTag b = .POmegaMinus := by
    rcases hbtag with h | h
    · exact Or.inl (by simp [markTag, h])
    · exact Or.inr (Or.inl (by simp [markTag, h]))
  have hLieB : CFSG.Blueprint.LieModel (↥R ⧸ Subgroup.center ↥R) (markTag b) (markRank b) 2 (markDeg b) := by
    simpa only [MarkedModel, hbchar] using hMarkB
  have hd1 := (fieldTwo_typeDet hl hn hne hMarkR hbcls hLieB).1
  have hbn : b.n = 1 := by
    rcases hbtag with h | h <;> simpa [markDeg, h] using hd1
  rw [hbn, hq] at hdeg
  exact Nat.pow_right_injective (le_refl 2) (hdeg.symm)


end CFSG.StandardType
