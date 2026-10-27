module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Cover
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExcMember
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCStdEnvelope
import CFSG.LocalAnalysis.StandardType.GGLangComponentLabel
import CFSG.LocalAnalysis.StandardType.GGCSRBasic
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTableBTwDThree

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.GGFinModel CFSG.LieType.Universal


theorem TwistedE6SourceCover.not_triality_label_of_qTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) : lab.tag ≠ .triD4 := by
  intro ht
  obtain ⟨hperf, c, hc, hraw⟩ := hq
  have hhasc : GGHasLabel c (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, theta, -⟩
    exact ⟨theta⟩
  have hi := ggLabelRigidInput_holds c lab (↥L ⧸ Subgroup.center ↥L) hc hl hhasc hhas
  have heq : c = lab := by
    cases lab with
    | mk t r f =>
      dsimp only at ht hi ⊢
      subst t
      exact eq_of_ggLabelIso_triD4 hi
  subst c
  have hM : LargeEvenMarking L (fun lab' _ _ I _ theta =>
      (3 = 3 ∧ lab'.tag = .triD4) ∧ LargeEvenSplit 3 lab' ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ phi ∈ I, LargeEvenInduces theta
          (fun l l' => (l' : G) = b⁻¹ * l * b) phi) := by
    refine ⟨hperf, lab, hl, ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, theta, hq0, hBsN, h3⟩
    have hn : lab.n = 1 := by
      have hn0 := hl.1
      have hn2 : lab.n < 2 := hq0
      omega
    exact ⟨hs, hna, theta, ⟨⟨rfl, ht⟩,
      Or.inr (Or.inr (Or.inr ⟨hn, rfl⟩)), hC.2.1.1.trans hBsN,
      fun b hb => h3 b (hC.2.1.1 hb)⟩⟩
  exact ggThmIHyp_false_of_labelAll (S := fun p lab' => p = 3 ∧ lab'.tag = .triD4)
    (fun p lab' _ hlab' hs _ => by
      obtain ⟨rfl, ht'⟩ := hs
      exact ggCSR_triD4 hlab' ht') hC.1 hM

theorem TwistedE6SourceCover.exists_longModel_of_native_carrier
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 1).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 1).D .twistedE6 0 1 psi)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpiker : pi.ker = Subgroup.center (ggU .twistedE6 0 1).K)
    {M : Subgroup (ggU .twistedE6 0 1).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L)
    (S : LangSetup TwistTag.E6.tag GGL 5) (a : Fin TwistTag.E6.tag.rank → GGLˣ)
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1)
    (hiota : Function.Injective iota) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hposition : (M.map pi).map iota = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    {V : LieUniversal} (hV : LieKnownR2.ExcPos.CarrierModel S a i V 1)
    (φ : V.K →* ModGL TwistTag.E6.tag GGL) (hφ : φ.range = (M.map pi).map iota) :
    ∃ (t' : CFSG.Open.StatedLieTag) (n' : ℕ), V = ggU t' n' 1 ∧
      CFSG.Open.StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
      ∃ δ, GGLongRoot (ggU t' n' 1).D δ ∧
        Nonempty (SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ) := by
  have hq' := hq
  obtain ⟨-, c, hc, hraw⟩ := hq'
  have hhasc : GGHasLabel c (↥L ⧸ Subgroup.center ↥L) :=
    largeEvenRawDatum_mono (fun _ _ _ _ h => by obtain ⟨-, -, θ, -⟩ := h; exact ⟨θ⟩) hraw
  have htri := TwistedE6SourceCover.not_triality_label_of_qTwo hC hq hc hhasc
  have h6 := LangComponentLabel.compRank_eq_six_of_exc_of_member (Or.inl rfl) S
    Nat.prime_three (by decide) hT hap i hqs hc hhasc htri psi hpsi.2.1.2 pi hpiker.le iota hiota
    hM.2.2.1 hML hposition
  have hsolv : ¬ Group.IsSolvable V.K := by
    intro hs
    have hR : Group.IsSolvable ↥((M.map pi).map iota) := by
      rw [← hφ]
      exact solvable_of_surjective φ.rangeRestrict_surjective
    rw [hposition] at hR
    obtain ⟨-, hsimple, u, v, huv⟩ := hqs
    exact huv (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance u v)
  refine FieldTwoExc.exists_longModel_of_carrierModel_of_not_triD4 hV hsolv ?_
  rintro ⟨hk, hr4, -⟩
  exact absurd ((h6 hk).symm.trans hr4) (by decide)

namespace TwistedE6SourceCover

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.Open CFSG.StandardType.SelectedRoot

section NativeCarrier


theorem exists_native_carrier
    (N : Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (S : LangSetup TwistTag.E6.tag GGL 5) (a : Fin TwistTag.E6.tag.rank → GGLˣ)
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hq : S.D.q = 2) (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit TwistTag.E6.tag a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hposition : N.map iota = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (horbit : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
  ∃ (V : LieUniversal) (φ : V.K →* ModGL TwistTag.E6.tag GGL),
    LieKnownR2.ExcPos.CarrierModel S a i V 1 ∧
    RCKRP.RCKADEModel V 1 ∧
    φ.range = N.map iota ∧
    φ.ker ≤ Subgroup.center V.K ∧
    Finite V.K ∧ Group.IsPerfect V.K ∧ CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit V.K ∧
    (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 →
      ∀ β ∈ V.D.roots, GGLongRoot V.D β → ∃ γ ∈ componentRoots (rootCharHom a) i,
        ∃ z ∈ torusGroup TwistTag.E6.tag GGL ⊔ rootSpan TwistTag.E6.tag GGL (kernelRoots (rootCharHom a)),
        ((rootSubgroup TwistTag.E6.tag GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
            (rootSubgroup TwistTag.E6.tag GGL γ).map (MulAut.conj z).toMonoidHom ∧
        ((rootSubgroup TwistTag.E6.tag GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
            (rootSubgroup TwistTag.E6.tag GGL (-γ)).map (MulAut.conj z).toMonoidHom ∧
        (V.D.rootGroup β).map φ = (rootSubgroup TwistTag.E6.tag GGL γ).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) ∧
        (V.D.rootGroup (-β)).map φ = (rootSubgroup TwistTag.E6.tag GGL (-γ)).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _)) := by
  have hcube : rootDiagUnit TwistTag.E6.tag a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have ha : a ^ 3 = 1 := funext fun j => by simpa using hap j
    rw [ha, rootDiagUnit_one]
  have hstd : RCKRP.RCKADEShape S.ρ (rootCharHom a) i :=
    RCKRP.rckStdEnvelope_holds TwistTag.E6.tag (Or.inr (Or.inl rfl)) S 3
      Nat.prime_three (by decide) a hT h1 hap i hqs
  have hC : RCKRP.RCKFrameCoverPair S a i 1 (fun V g => LieKnownR2.ExcPos.CarrierModel S a i V g) :=
    LieKnownR2.ExcPos.rckCarrierPairADE_holds TwistTag.E6.tag 5 S a hT 3 Nat.prime_three
      (by decide) hcube i 1 (by simpa only [pow_one] using hq) hstd hqs
  obtain ⟨V, phi, hCM, hADE, hrange, hker, hfin, hperf, hsplit, hpair⟩ := hC
  refine ⟨V, phi, ?_, ?_, hrange.trans hposition.symm, hker, hfin, hperf, hsplit, hpair⟩
  · simpa only [horbit, mul_one] using hCM
  · simpa only [horbit, mul_one] using hADE

theorem exists_native_ordinary_root_cover
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hmark : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 1).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 1).D .twistedE6 0 1 psi)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpiker : pi.ker = Subgroup.center (ggU .twistedE6 0 1).K)
    {M : Subgroup (ggU .twistedE6 0 1).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L)
    (S : LangSetup TwistTag.E6.tag GGL 5) (a : Fin TwistTag.E6.tag.rank → GGLˣ)
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGL)
    (hq : S.D.q = 2) (hT : rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit TwistTag.E6.tag a ≠ 1)
    (hiota : Function.Injective iota) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hposition : (M.map pi).map iota = rationalComponent S.ρ S.Γ (rootCharHom a) i)
    (horbit : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1) :
    ∃ (t : StatedLieTag) (n : ℕ) (rho : (ggU t n 1).K →* ↥(M.map pi)),
      StatedLieAdmissible t n 2 1 ∧ 2 ≤ (ggU t n 1).D.rank ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center (ggU t n 1).K ∧
      ∃ delta, GGLongRoot (ggU t n 1).D delta ∧
        Nonempty (SelectedSL2Model (ggU t n 1).D (GaloisField 2 1) delta) ∧
        ∃ gamma ∈ componentRoots (rootCharHom a) i,
          ∃ z ∈ torusGroup TwistTag.E6.tag GGL ⊔ rootSpan TwistTag.E6.tag GGL (kernelRoots (rootCharHom a)),
            ((rootSubgroup TwistTag.E6.tag GGL gamma).map (MulAut.conj z).toMonoidHom).map S.D.step =
              (rootSubgroup TwistTag.E6.tag GGL gamma).map (MulAut.conj z).toMonoidHom ∧
            ((rootSubgroup TwistTag.E6.tag GGL (-gamma)).map (MulAut.conj z).toMonoidHom).map S.D.step =
              (rootSubgroup TwistTag.E6.tag GGL (-gamma)).map (MulAut.conj z).toMonoidHom ∧
            ((ggU t n 1).D.rootGroup delta).map (iota.comp ((M.map pi).subtype.comp rho)) =
              (rootSubgroup TwistTag.E6.tag GGL gamma).map (MulAut.conj z).toMonoidHom ⊓
                S.D.step.eqLocus (MonoidHom.id _) ∧
            ((ggU t n 1).D.rootGroup (-delta)).map (iota.comp ((M.map pi).subtype.comp rho)) =
              (rootSubgroup TwistTag.E6.tag GGL (-gamma)).map (MulAut.conj z).toMonoidHom ⊓
                S.D.step.eqLocus (MonoidHom.id _) := by
  classical
  obtain ⟨V, phi, hCM, -, hrange, hker, -, -, -, hpair⟩ :=
    exists_native_carrier (M.map pi) S a iota hq hT hap h1 i hqs hposition horbit
  obtain ⟨t, n, hV, hadm, hrank, delta, hlong, hmodel⟩ :=
    TwistedE6SourceCover.exists_longModel_of_native_carrier hC hmark psi hpsi pi hpiker
      hM hML S a iota hT hap hiota i hqs hposition hCM phi hrange
  subst V
  let phiR : (ggU t n 1).K →* ↥((M.map pi).map iota) :=
    phi.codRestrict _ (fun z => hrange ▸ MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  have hphiR : Function.Surjective phiR := by
    intro r
    have hr : (r : ModGL TwistTag.E6.tag GGL) ∈ phi.range := by
      rw [hrange]
      exact r.property
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hr
    exact ⟨z, Subtype.ext hz⟩
  let e : ↥(M.map pi) ≃* ↥((M.map pi).map iota) :=
    (M.map pi).equivMapOfInjective iota hiota
  let rho : (ggU t n 1).K →* ↥(M.map pi) := e.symm.toMonoidHom.comp phiR
  have hcomm : iota.comp ((M.map pi).subtype.comp rho) = phi := by
    refine MonoidHom.ext fun z => ?_
    have he : e (rho z) = phiR z := e.apply_symm_apply _
    exact congrArg Subtype.val he
  have hrho : Function.Surjective rho := e.symm.surjective.comp hphiR
  have hrhoker : rho.ker ≤ Subgroup.center (ggU t n 1).K := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker, ← hcomm]
    change iota (rho z) = 1
    rw [show rho z = 1 from hz]
    exact iota.map_one
  obtain ⟨gamma, hgamma, z, hz, hpos, hneg, himage, himagem⟩ :=
    hpair horbit delta ((Classical.choice hmodel).root_mem) hlong
  refine ⟨t, n, rho, hadm, hrank, hrho, hrhoker, delta, hlong, hmodel,
    gamma, hgamma, z, hz, hpos, hneg, ?_, ?_⟩
  · rw [hcomm]
    exact himage
  · rw [hcomm]
    exact himagem

end NativeCarrier

end TwistedE6SourceCover

end CFSG.StandardType

end
