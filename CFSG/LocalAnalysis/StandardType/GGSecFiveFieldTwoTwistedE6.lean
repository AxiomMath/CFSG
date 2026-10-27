module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Cover
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6CarrierModel
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6RootPosition
public import CFSG.LocalAnalysis.StandardType.GGSelectedMemberCover

public section

namespace CFSG.StandardType.FieldTwoTwistedE6

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.StandardType.S2MathFi1035Pos
  CFSG.StandardType.RankOneXfer CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieKnownR2.ExcPos CFSG.LieType.AlgebraicGroups


theorem exists_native_member_root_cover_of_rational_component
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 1).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 1).D .twistedE6 0 1 psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 1).D psi x)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpi : Function.Surjective pi)
    (hpiker : pi.ker = Subgroup.center (ggU .twistedE6 0 1).K)
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (halpha : alpha ∈ LayerSixE.twInndiagAut 1) (halpha3 : alpha ^ 3 = 1)
    (halpha_ne : alpha ≠ 1) (hind : LayerSixE.GGInduces pi psi x alpha)
    {M : Subgroup (ggU .twistedE6 0 1).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L)
    (hN : CFSG.Assembly.IsComponentOf (M.map pi) (fixSubgroup alpha))
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) (hB2 : lab.tag ≠ .B2der)
    (hmodel : MarkedModel lab (↥(M.map pi) ⧸ Subgroup.center ↥(M.map pi)))
    (eta : (ggU .twistedE6 0 1).K →* e6Data_valid.minGroup GGFinModel.GGL)
    (tLift : e6Data_valid.minGroup GGFinModel.GGL) (heta : Function.Injective eta)
    (hetaval : ∀ u, eta u = minBC e6Data_valid (GGFinModel.ggRatEmb (2 * 1))
      (Subtype.val (show twistedE6Group 2 1 from u)))
    (hetarange : eta.range = CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      GGFinModel.GGL (GGFinModel.ggFrobT 1))
    (ht3 : tLift ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup GGFinModel.GGL))
    (htFr : CFSG.LieType.Steinberg.TwistedE6.sigma GGFinModel.GGL
        (GGFinModel.ggFrobT 1) tLift * tLift⁻¹ ∈
      Subgroup.center (e6Data_valid.minGroup GGFinModel.GGL))
    (ht9 : tLift ^ 9 = 1)
    (htcentral : tLift ∈ Subgroup.center (e6Data_valid.minGroup GGFinModel.GGL) ↔
      x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G))
    (hact : ∀ u u', psi u' = x * psi u * x⁻¹ →
      e6IsogenyAlgebraic (eta u') = e6IsogenyAlgebraic tLift *
        e6IsogenyAlgebraic (eta u) * (e6IsogenyAlgebraic tLift)⁻¹)
    (hcomponent : CFSG.Assembly.IsComponentOf (M.map eta)
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup GGFinModel.GGL
        (GGFinModel.ggFrobT 1) ⊓ Subgroup.centralizer {tLift}))
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup TwistTag.E6.tag GGFinModel.GGL 5)
    (a : Fin TwistTag.E6.tag.rank → GGFinModel.GGLˣ)
    (iota : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)) →*
      ModGL TwistTag.E6.tag GGFinModel.GGL)
    (hq : S.D.q = 2 ^ 1) (hPhi : S.D.Φ = twistHom TwistTag.E6 GGFinModel.GGL (GGFinModel.ggFrobT 1))
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a ≠ 1)
    (hiota : Function.Injective iota) (hrange : iota.range = S.Γ)
    (hcompat : ∀ c, iota (alpha c) =
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a * iota c *
        (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.E6.tag a)⁻¹)
    (hival : ∀ c, S.D.g0 * iota c * S.D.g0⁻¹ =
      baseChangeGL (GGFinModel.ggRatEmb (2 * 1)) (c : ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (i : CFSG.LieType.Chevalley.KernelComponent (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hqs : CFSG.IsQuasisimple ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent
      S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i))
    (hposition : (M.map pi).map iota = CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent
      S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
    (horbit : CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
      (componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) = 1) :
    ∃ (t : StatedLieTag) (n : ℕ) (rho : (ggU t n 1).K →* ↥(M.map pi)),
      StatedLieAdmissible t n 2 1 ∧ 2 ≤ (ggU t n 1).D.rank ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center (ggU t n 1).K ∧
      ∃ (delta : Fin (ggU t n 1).D.rank → ℤ), delta ∈ (ggU t n 1).D.roots ∧
        ∃ phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* (ggU t n 1).K,
          Function.Injective phi ∧
          (sl2UpperUniSub (GaloisField 2 1)).map phi = (ggU t n 1).D.rootGroup delta ∧
          ∃ u0 : (ggU .twistedE6 0 1).K,
            ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
                (pi.comp (MulAut.conj u0).toMonoidHom) =
              ((ggU t n 1).D.rootGroup delta).map ((M.map pi).subtype.comp rho) := by
  have hmark : GGInnerDiagOnLabel GGLabQTwo 3 Bs L := by assumption
  have hS_q : S.D.q = 2 := by simpa only [pow_one] using hq
  obtain ⟨t, n, rho, hadm, hrank, hrho, hker, delta, hlong, hmodel,
    gamma, hgamma, z, hz, hpos, hneg, himage, himagem⟩ :=
    TwistedE6SourceCover.exists_native_ordinary_root_cover hC hmark psi hpsi pi hpiker
      hM hML S a iota hS_q hT hap h1 hiota i hqs hposition horbit
  have hgammaRoot : IsRoot TwistTag.E6.tag gamma := isRoot_of_mem_componentRoots hgamma
  have hzAdj : z ∈ adjointGroup TwistTag.E6.tag GGL :=
    torus_sup_rootSpan_le_adjointGroup (kernelRoots (rootCharHom a)) hz
  have hcurve : ∀ r, excCurve (τ := TwistTag.E6.tag) r z ≤ adjointGroup TwistTag.E6.tag GGL :=
    fun r => (Subgroup.map_mono (rootSubgroup_le_adjointGroup r)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.1
        ((adjointGroup TwistTag.E6.tag GGL).le_normalizer hzAdj)).le
  have hinter : ∀ r, excCurve (τ := TwistTag.E6.tag) r z ⊓ S.D.step.eqLocus (MonoidHom.id _) =
      excCurve (τ := TwistTag.E6.tag) r z ⊓ S.D.model := by
    intro r
    change _ = excCurve (τ := TwistTag.E6.tag) r z ⊓
      (adjointGroup TwistTag.E6.tag GGL ⊓ S.D.step.eqLocus (MonoidHom.id _))
    rw [← inf_assoc, inf_eq_left.mpr (hcurve r)]
  have himage' : ((ggU t n 1).D.rootGroup delta).map
      (iota.comp ((M.map pi).subtype.comp rho)) = excCurve (τ := TwistTag.E6.tag) gamma z ⊓ S.D.model :=
    himage.trans (hinter gamma)
  have hpos' : (excCurve (τ := TwistTag.E6.tag) gamma z).map S.D.step = excCurve (τ := TwistTag.E6.tag) gamma z := hpos
  have hneg' : (excCurve (τ := TwistTag.E6.tag) (-gamma) z).map S.D.step = excCurve (τ := TwistTag.E6.tag) (-gamma) z := hneg
  obtain ⟨k, hcan, -⟩ := TwistedE6SourceCover.canonical_root_pair_position
    S pi hpival iota hival hrange hq hPhi hgammaRoot hzAdj hpos' hneg'
  have hroot : ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
      (pi.comp (MulAut.conj k).toMonoidHom) =
      ((ggU t n 1).D.rootGroup delta).map ((M.map pi).subtype.comp rho) := by
    apply Subgroup.map_injective hiota
    have hleft :
        (((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
          (pi.comp (MulAut.conj k).toMonoidHom)).map iota =
        ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
          ((iota.comp pi).comp (MulAut.conj k).toMonoidHom) :=
      (Subgroup.map_map _ _ _).trans (by rfl)
    have hright : (((ggU t n 1).D.rootGroup delta).map ((M.map pi).subtype.comp rho)).map iota =
        ((ggU t n 1).D.rootGroup delta).map (iota.comp ((M.map pi).subtype.comp rho)) :=
      Subgroup.map_map _ _ _
    exact hleft.trans (hcan.trans (himage'.symm.trans hright.symm))
  let model := Classical.choice hmodel
  exact ⟨t, n, rho, hadm, hrank, hrho, hker, delta, model.root_mem,
    model.phi, model.injective, model.upper_eq, k, hroot⟩

theorem exists_native_member_root_cover_of_fixed_source_centralizer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hq_2 : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 1).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 1).D .twistedE6 0 1 psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 1).D psi x)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpi : Function.Surjective pi)
    (hpiker : pi.ker = Subgroup.center (ggU .twistedE6 0 1).K)
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (halpha : alpha ∈ LayerSixE.twInndiagAut 1) (halpha3 : alpha ^ 3 = 1)
    (halpha_ne : alpha ≠ 1) (hind : LayerSixE.GGInduces pi psi x alpha)
    {M : Subgroup (ggU .twistedE6 0 1).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L)
    (hN : CFSG.Assembly.IsComponentOf (M.map pi) (fixSubgroup alpha))
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) (hB2 : lab.tag ≠ .B2der)
    (hmodel : MarkedModel lab (↥(M.map pi) ⧸ Subgroup.center ↥(M.map pi)))
    (eta : (ggU .twistedE6 0 1).K →* e6Data_valid.minGroup GGFinModel.GGL)
    (tLift : e6Data_valid.minGroup GGFinModel.GGL) (heta : Function.Injective eta)
    (hetaval : ∀ u, eta u = minBC e6Data_valid (GGFinModel.ggRatEmb (2 * 1))
      (Subtype.val (show twistedE6Group 2 1 from u)))
    (hetarange : eta.range = CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      GGFinModel.GGL (GGFinModel.ggFrobT 1))
    (ht3 : tLift ^ 3 ∈ Subgroup.center (e6Data_valid.minGroup GGFinModel.GGL))
    (htFr : CFSG.LieType.Steinberg.TwistedE6.sigma GGFinModel.GGL
        (GGFinModel.ggFrobT 1) tLift * tLift⁻¹ ∈
      Subgroup.center (e6Data_valid.minGroup GGFinModel.GGL))
    (ht9 : tLift ^ 9 = 1)
    (htcentral : tLift ∈ Subgroup.center (e6Data_valid.minGroup GGFinModel.GGL) ↔
      x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G))
    (hact : ∀ u u', psi u' = x * psi u * x⁻¹ →
      e6IsogenyAlgebraic (eta u') = e6IsogenyAlgebraic tLift *
        e6IsogenyAlgebraic (eta u) * (e6IsogenyAlgebraic tLift)⁻¹)
    (hcomponent : CFSG.Assembly.IsComponentOf (M.map eta)
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup GGFinModel.GGL
        (GGFinModel.ggFrobT 1) ⊓ Subgroup.centralizer {tLift})) :
    ∃ (t : StatedLieTag) (n : ℕ) (rho : (ggU t n 1).K →* ↥(M.map pi)),
      StatedLieAdmissible t n 2 1 ∧ 2 ≤ (ggU t n 1).D.rank ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center (ggU t n 1).K ∧
      ∃ (delta : Fin (ggU t n 1).D.rank → ℤ), delta ∈ (ggU t n 1).D.roots ∧
        ∃ phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* (ggU t n 1).K,
          Function.Injective phi ∧
          (sl2UpperUniSub (GaloisField 2 1)).map phi = (ggU t n 1).D.rootGroup delta ∧
          ∃ u0 : (ggU .twistedE6 0 1).K,
            ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
                (pi.comp (MulAut.conj u0).toMonoidHom) =
              ((ggU t n 1).D.rootGroup delta).map ((M.map pi).subtype.comp rho) := by
  obtain ⟨S, a, iota, hq, hPhi, hT, hap, h1, hiota, hrange, hcompat, hival, i, hqs, hposition⟩ :=
    TwistedE6SourceCover.exists_native_rationalComponent alpha halpha halpha3 halpha_ne (M.map pi) hN
  have horbit := TwistedE6SourceCover.componentOrbitLength_eq_one_of_marked_native
    (M.map pi) hl hn hne hmodel S a iota hiota (by simpa only [pow_one] using hq)
    hT hap h1 i hqs hposition
  exact exists_native_member_root_cover_of_rational_component
    hC hq_2 psi hpsi hdiag pi hpi hpiker hpival alpha halpha halpha3 halpha_ne hind hM hML hN
    hl hn hne hB2 hmodel eta tLift heta hetaval hetarange ht3 htFr ht9 htcentral hact hcomponent
    S a iota hq hPhi hT hap h1 hiota hrange hcompat hival i hqs hposition horbit

theorem exists_native_member_root_cover
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 1).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 1).D .twistedE6 0 1 psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 1).D psi x)
    (pi : (ggU .twistedE6 0 1).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (hpi : Function.Surjective pi)
    (hpiker : pi.ker = Subgroup.center (ggU .twistedE6 0 1).K)
    (hpival : ∀ z, ((pi z : graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * 1)) (frobQ 2 1)) : ModGL TwistTag.E6.tag
          (GaloisField 2 (2 * 1))) =
      ((e6IsogenyT (GaloisField 2 (2 * 1))
        (Subtype.val (show twistedE6Group 2 1 from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * 1))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * 1))))
    (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6
      (GaloisField 2 (2 * 1)) (frobQ 2 1)))
    (halpha : alpha ∈ LayerSixE.twInndiagAut 1) (halpha3 : alpha ^ 3 = 1)
    (halpha_ne : alpha ≠ 1) (hind : LayerSixE.GGInduces pi psi x alpha)
    {M : Subgroup (ggU .twistedE6 0 1).K}
    (hM : CFSG.Assembly.IsComponentOf M ((Subgroup.centralizer {x}).comap psi))
    (hML : M.map psi = L)
    (hN : CFSG.Assembly.IsComponentOf (M.map pi) (fixSubgroup alpha))
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) (hB2 : lab.tag ≠ .B2der)
    (hmodel : MarkedModel lab (↥(M.map pi) ⧸ Subgroup.center ↥(M.map pi))) :
    ∃ (t : StatedLieTag) (n : ℕ) (rho : (ggU t n 1).K →* ↥(M.map pi)),
      StatedLieAdmissible t n 2 1 ∧ 2 ≤ (ggU t n 1).D.rank ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center (ggU t n 1).K ∧
      ∃ (delta : Fin (ggU t n 1).D.rank → ℤ), delta ∈ (ggU t n 1).D.roots ∧
        ∃ phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* (ggU t n 1).K,
          Function.Injective phi ∧
          (sl2UpperUniSub (GaloisField 2 1)).map phi = (ggU t n 1).D.rootGroup delta ∧
          ∃ u0 : (ggU .twistedE6 0 1).K,
            ((ggU .twistedE6 0 1).D.rootGroup (Pi.single (1 : Fin 4) 1)).map
                (pi.comp (MulAut.conj u0).toMonoidHom) =
              ((ggU t n 1).D.rootGroup delta).map ((M.map pi).subtype.comp rho) := by
  obtain ⟨_, eta, tLift, heta, hetaval, hetarange, ht3, htFr, ht9,
      htcentral, hact, hcomponent⟩ :=
    hC.exists_fixed_source_centralizer_of_twistedE6_component hq psi hpsi hdiag hM hML
  exact exists_native_member_root_cover_of_fixed_source_centralizer
    hC hq psi hpsi hdiag pi hpi hpiker hpival alpha halpha halpha3 halpha_ne hind
    hM hML hN hl hn hne hB2 hmodel eta tLift heta hetaval hetarange
    ht3 htFr ht9 htcentral hact hcomponent

theorem ggSecFiveQTwoFieldTwoSelectedAt_twistedE6 :
    GGSecFiveQTwoFieldTwoSelectedAt .twistedE6 := by
  intro G _ _ B Bs x L D J hC hq n f psi hpres hdiag
  have hn : n = 0 := hpres.1.1.2.2
  subst n
  by_cases hcentral : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)
  · exact ggSecFiveQTwoFieldTwoSelected_twistedE6_of_central_all_fields
      hC hq psi hpres hdiag hcentral
  · obtain ⟨hf, pi, alpha, lab, M, rho0, eML, hpi, hpiker, hpival,
        halpha, halpha3, hind, htrivial, hM, hML, hN,
        hrho0, hrho0ker, hrho0kerEq, hrho0Eq, heML,
        hl, hnLab, hne, hB2, hmodelM, hMN, hmodelN, hmodelL⟩ :=
      hC.exists_marked_native_component_of_twistedE6_qTwo hq psi hpres hdiag
    subst f
    have halpha_ne : alpha ≠ 1 := fun h => hcentral (htrivial.mp h)
    obtain ⟨t', n', rho, hadm, hrk, hrho, hrhoker, delta, hdelta,
        phi, hinj, hupper, u0, hmap⟩ :=
      exists_native_member_root_cover hC hq psi hpres hdiag pi hpi hpiker hpival
        alpha halpha halpha3 halpha_ne hind hM hML hN hl hnLab hne hB2 hmodelN
    have ht : GGPosTag t' := by
      simpa only [GGPosTag, RCKRP.RCKClassicalTag, GGExcFive, or_assoc] using
        RCKRP.rckRPG_tag_trichotomy t' n' 1 hadm hrk
    letI : Finite (ggU .twistedE6 0 1).K :=
      LieKnownR2.OddCenter.finite_ggU (t := .twistedE6) (by simp [GGPosTag]) hpres.1.1
    letI : Group.IsPerfect ↥M := ⟨hM.2.2.1⟩
    have hpiodd : Odd (Nat.card pi.ker) := by
      rw [hpiker]
      change Odd (Nat.card (Subgroup.center (twistedE6Group 2 1)))
      exact (by decide : Odd (3 : ℕ)).of_dvd_nat (TwE6DD2.card_center_dvd_three le_rfl)
    have hpiKerCentral : pi.ker ≤ Subgroup.center (ggU .twistedE6 0 1).K := by
      rw [hpiker]
    obtain ⟨_, source, _⟩ := exists_selectedSL2Model_twistedE6_long
    obtain ⟨Phi, psiPrime, model, member, hPhiRange, hPhiKer, hPhiComm,
        hpsiPrime, hpsiRange, hpsiKer, hphi, hwhole⟩ :=
      SelectedMemberCover.selected_of_native_member (ggU .twistedE6 0 1).D pi
        hpiKerCentral hpiodd psi hpres.2.1.2 hML ht hadm rho hrho hrhoker
        source hdelta phi hinj hupper u0 hmap
    exact ⟨t', n', psiPrime, hadm, hrk, hpsiKer, hpsiRange,
      _, delta, model, member, u0, hwhole⟩

end CFSG.StandardType.FieldTwoTwistedE6
