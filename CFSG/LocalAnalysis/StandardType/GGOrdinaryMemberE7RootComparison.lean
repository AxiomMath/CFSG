module

public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberE7RootRecognition
public import CFSG.LocalAnalysis.StandardType.ExcPos.E6RationalRootPairs
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6Pullback

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley




theorem exists_original_twistedE6_root_comparison
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (lambda : e7Data_valid.minGroup K →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (hBs : Bs ≤ lambda.range)
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota) (hrange : iota.range = S.Γ)
    (hformula : ∀ u, iota u = S.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) * S.D.g0)
    (hwhole : ∀ z : ModGL .E7 (AlgebraicClosure K),
      (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K u) = z) ↔
      ∃ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = z)
    {r : MulAut Bs} (hr : GGIsReflection p r) (hrL : r ∈ ggAutomizer L Bs)
    (j : Fin Tag.E7.rank)
    (hroot : (rankOne (e7Datum K).rootGroup j).map lambda = ggRankOnePerf Bs r)
    (sigma : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hsigma : ∀ c, sigma c = c ^ Nat.card K)
    (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha)
    (y : e7Data_valid.minGroup K) (M : Subgroup (e7Data_valid.minGroup K))
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set _)))
    (hML : M.map lambda = L) (hRM : rankOne (e7Datum K).rootGroup j ≤ M)
    (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ) (hyBs : lambda y ∈ Bs)
    (hya : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K y) = rootDiagUnit .E7 a)
    (c : KernelComponent (rootCharHom a)) (w : WeylGroup .E7)
    (hMC : M.map (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom) =
      rationalComponent S.ρ S.Γ (rootCharHom a) c)
    (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    {q : ℕ} (hq0 : 1 ≤ q) (hq : S.D.q = 2 ^ q)
    (Phi : (ggU .twistedE6 0 q).K →* e7Data_valid.minGroup K)
    (phi : (ggU .twistedE6 0 q).K →* ModGL .E7 (AlgebraicClosure K))
    (hcomm : (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom).comp Phi = phi)
    (z : ModGL .E7 (AlgebraicClosure K))
    (gamma : Fin Tag.E7.rank → ℤ) (hgamma : IsRoot .E7 gamma)
    (hgPsi : gamma ∈ componentRoots (rootCharHom a) c)
    (hz : z ∈ rootSpan .E7 (AlgebraicClosure K) (componentRoots (rootCharHom a) c))
    (hstep : ∀ g ∈ rootSpan .E7 (AlgebraicClosure K) ({gamma, -gamma} : Set _),
      S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹)
    (hpos : ((twistedE6Datum 2 q).rootGroup (Pi.single (0 : Fin 4) 1)).map phi =
      ((rootSubgroup .E7 ↥(fixSubfield sigma) gamma).map
        (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom)
    (hneg : ((twistedE6Datum 2 q).rootGroup (-Pi.single (0 : Fin 4) 1)).map phi =
      ((rootSubgroup .E7 ↥(fixSubfield sigma) (-gamma)).map
        (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom) :
    ∃ v : e7Data_valid.minGroup K, v ∈ M ∧
      (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi =
        (rankOne (e7Datum K).rootGroup j).map (MulAut.conj v).toMonoidHom := by
  classical
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  letI : Algebra (ZMod 2) (AlgebraicClosure K) := inferInstance
  haveI : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (ZMod 2) (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans (ZMod 2) K (AlgebraicClosure K)
  obtain ⟨beta, hbeta, hbPsi, hnbPsi, hParent, _⟩ :=
    exists_e7_parent_fixed_root_in_e6_component_of_prime hp hp2 hK lambda hker hBs S iota
      hinj hrange hformula hwhole hr hrL j hroot sigma hsigma hPhi hRho y M hM hML hRM
      a hyBs hya c w hMC hPsi
  let alpha := iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom
  have hainj : Function.Injective alpha := hinj.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).injective
  have hParent' : (rankOne (e7Datum K).rootGroup j).map alpha =
      rootSpan .E7 (AlgebraicClosure K) {beta, -beta} ⊓ S.D.step.eqLocus (MonoidHom.id _) := by
    simpa only [Subgroup.map_map] using hParent
  obtain ⟨u, huN, hPair⟩ := LieKnownR2.ExcPos.exists_rational_e6_root_pair_conj
    S sigma hPhi hRho q hq0 hq a c w hPsi hbPsi hgPsi z hz hstep
  have hEq : (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map phi =
      ((rankOne (e7Datum K).rootGroup j).map alpha).map (MulAut.conj u).toMonoidHom := by
    exact (RCKRP.rckTw6_longLevi_fixed_image (K := K) (q := q)
      S phi sigma z gamma hgamma hstep hpos hneg).trans
      (hPair.trans (congrArg (fun P : Subgroup (ModGL .E7 (AlgebraicClosure K)) =>
        P.map (MulAut.conj u).toMonoidHom) hParent'.symm))
  obtain ⟨v, hvM, hvu, _⟩ := exists_mem_map_conj_of_map_le_map_conj hainj hMC hcomm huN hEq.le
  refine ⟨v, hvM, Subgroup.map_injective hainj ?_⟩
  rw [Subgroup.map_map, hcomm, Subgroup.map_map_conj, hvu]
  exact hEq

end CFSG.StandardType
