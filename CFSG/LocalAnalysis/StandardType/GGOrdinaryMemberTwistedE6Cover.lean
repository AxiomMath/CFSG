module
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6RootComponent
public import CFSG.LocalAnalysis.StandardType.GGSelectedMemberCover
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberE7ToralLang
public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6Scalar
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberTwistedE6Card
public noncomputable section
namespace CFSG.StandardType
open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.TwistedE6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE6 CFSG.StandardType.GGFinModel
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Phan.PhanE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem exists_ordinary_twistedE6_cover_of_rational_E7_component
    {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ} (hq0 : 0 < q)
    (M : Subgroup (e7Data_valid.minGroup K))
    (S : LangSetup Tag.E7 (AlgebraicClosure K) 5)
    (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota) (c : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c))
    (hMR : M.map (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom) =
      rationalComponent S.ρ S.Γ (rootCharHom a) c)
    (hT : rootDiagUnit .E7 a ∈ S.D.torus)
    (v : WeylGroup .E7) (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => v • alpha) '' parabolicRoots .E7 (e6Nodes .E7))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) c)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) c)]))
    (hq : S.D.q = 2 ^ q) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) c) = 1 ∧
    ∃ (Phi : twistedE6Group 2 q →* e7Data_valid.minGroup K)
      (phi : twistedE6Group 2 q →* ModGL .E7 (AlgebraicClosure K))
      (sigma : AlgebraicClosure K ≃+* AlgebraicClosure K)
      (z : ModGL .E7 (AlgebraicClosure K)) (gamma : Fin Tag.E7.rank → ℤ),
      Phi.range = M ∧ Phi.ker ≤ Subgroup.center (twistedE6Group 2 q) ∧
      (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom).comp Phi = phi ∧
      phi.range = rationalComponent S.ρ S.Γ (rootCharHom a) c ∧
      phi.ker ≤ Subgroup.center (twistedE6Group 2 q) ∧
      (∀ x, sigma x = x ^ 2 ^ q) ∧ z ∈ rootSpan .E7 (AlgebraicClosure K)
        (componentRoots (rootCharHom a) c) ∧
      phi.range ≤ rootSpan .E7 (AlgebraicClosure K) (componentRoots (rootCharHom a) c) ∧
      IsRoot .E7 gamma ∧ gamma ∈ componentRoots (rootCharHom a) c ∧
      -gamma ∈ componentRoots (rootCharHom a) c ∧
      (∀ g ∈ rootSpan .E7 (AlgebraicClosure K) ({gamma, -gamma} : Set (Fin Tag.E7.rank → ℤ)),
        S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹) ∧
      ((twistedE6Datum 2 q).rootGroup (Pi.single (0 : Fin 4) 1)).map phi =
        ((rootSubgroup .E7 ↥(fixSubfield sigma) gamma).map
          (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom ∧
      ((twistedE6Datum 2 q).rootGroup (-Pi.single (0 : Fin 4) 1)).map phi =
        ((rootSubgroup .E7 ↥(fixSubfield sigma) (-gamma)).map
          (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom := by
  obtain ⟨hlen, phi, sigma, z, gamma, hphirange, hphiker, hsigma, hz, hle, hroot,
      hgamma, hngamma, hstep, hpos, hneg⟩ :=
    RCKRP.rckTw_cover_E78_of_field S hT c v hPsi hout hq0 hq
  let theta := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K
  let alpha := iota.comp theta.toMonoidHom
  have hainj : Function.Injective alpha := hinj.comp theta.injective
  have haker : alpha.ker = ⊥ := MonoidHom.ker_eq_bot alpha hainj
  have hacent : alpha.ker ≤ Subgroup.center (e7Data_valid.minGroup K) := by
    rw [haker]
    exact bot_le
  have haodd : Odd (Nat.card alpha.ker) := by simp [haker]
  let eMR := (Subgroup.equivMapOfInjective M alpha hainj).trans (MulEquiv.subgroupCongr hMR)
  let : Group.IsPerfect (rationalComponent S.ρ S.Γ (rootCharHom a) c) := hqs.1
  let : Group.IsPerfect M :=
    Group.IsPerfect.ofSurjective (f := eMR.symm.toMonoidHom) eMR.symm.surjective
  have hrange : phi.range = M.map alpha := hphirange.trans hMR.symm
  let rho : (ggU .twistedE6 0 q).K →* ↥(M.map alpha) :=
    phi.codRestrict (M.map alpha) (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  have hrhosurj : Function.Surjective rho := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ phi.range := hrange.symm ▸ hx
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hx'
    exact ⟨u, Subtype.ext hu⟩
  have hrhoker : rho.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K := by
    intro x hx
    exact hphiker (congrArg Subtype.val (show rho x = 1 from hx))
  have ht : GGPosTag .twistedE6 := by simp [GGPosTag]
  have hadm : StatedLieAdmissible .twistedE6 0 2 q := by
    exact ⟨Nat.prime_two, by omega, rfl⟩
  obtain ⟨Phi, hPhirange, hPhiker, hcomm⟩ :=
    SelectedMemberCover.exists_ordinary_source_cover alpha hacent haodd ht hadm rho hrhosurj hrhoker
  have hcomm' : alpha.comp Phi = phi := hcomm.trans (by ext x; rfl)
  exact ⟨hlen, Phi, phi, sigma, z, gamma, hPhirange, hPhiker, hcomm', hphirange, hphiker,
    hsigma, hz, hle, hroot, hgamma, hngamma, hstep, hpos, hneg⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_coherent_native_twistedE6_cover_of_original_E7_three_join_of_marking
    (hTB : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region 3 B Bs x L D J)
    (hARow : ¬ GGSecFivePhanARow 3 B Bs x L D J)
    (hQTwo : ¬ GGSecFiveQTwoCell 3 B Bs x L D J)
    {ι : Type} {N : CoxeterMatrix ι} {e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) N e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hSix : ¬ GGSecFiveJoinOrderSixAt 3 L Bs 𝒦 N e)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (hψ : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ)
    (hJoin : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hmark : GGInnerDiagOnLabel ggRowP_ETwE6 3 Bs L) :
    ∃ q : ℕ, 4 ≤ 2 ^ q ∧ 3 ∣ 2 ^ q + 1 ∧
      ∃ (lambda : e7Data_valid.minGroup (GaloisField 2 q) →* G),
        GGPresentsG0 (ggG0 3 B x L D J) (e7Datum (GaloisField 2 q)) .E7 0 q lambda ∧
        ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl N e ∧
          GGIsReflection 3 r₀ ∧
          ∃ (i : Fin (Tag.rank .E7))
            (Γ : Bs →* MulAut (e7Data_valid.minGroup (GaloisField 2 q)))
            (y : e7Data_valid.minGroup (GaloisField 2 q))
            (M : Subgroup (e7Data_valid.minGroup (GaloisField 2 q))),
            (rankOne (e7Datum (GaloisField 2 q)).rootGroup i).map lambda =
                ggRankOnePerf Bs r₀ ∧
            (∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹) ∧
            y ^ 3 = 1 ∧ Γ ⟨x, hcfg.1.1.x_facts.1⟩ = MulAut.conj y ∧
            IsComponentOf M (Subgroup.centralizer {y}) ∧ M.map lambda = L ∧
            rankOne (e7Datum (GaloisField 2 q)).rootGroup i ≤ M ∧
            (∀ b z, z ∈ M → Γ b z ∈ M) ∧ lambda y = x ∧ y ≠ 1 ∧
            ∃ (S : LangSetup Tag.E7 (AlgebraicClosure (GaloisField 2 q)) 5)
              (a : Fin Tag.E7.rank → (AlgebraicClosure (GaloisField 2 q))ˣ)
              (iota : adjointGroup .E7 (GaloisField 2 q) →*
                ModGL .E7 (AlgebraicClosure (GaloisField 2 q)))
              (c : KernelComponent (rootCharHom a)),
              S.D.q = 2 ^ q ∧
              (∃ Fr : AlgebraicClosure (GaloisField 2 q) →+* AlgebraicClosure (GaloisField 2 q),
                (∀ z, Fr z = z ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
              (∀ z, iota z = S.D.g0⁻¹ *
                baseChangeGL (algebraMap (GaloisField 2 q) (AlgebraicClosure (GaloisField 2 q)))
                  (z : ModGL .E7 (GaloisField 2 q)) * S.D.g0) ∧
              (∀ u : e7Data_valid.minGroup (GaloisField 2 q), lambda u ∈ Bs →
                iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q) u) ∈
                  S.D.torus) ∧
              (∀ w : ModGL .E7 (AlgebraicClosure (GaloisField 2 q)),
                (∃ u : e7Data_valid.minGroup (GaloisField 2 q), lambda u ∈ Bs ∧
                  iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q) u) = w) ↔
                ∃ b : Fin Tag.E7.rank → (AlgebraicClosure (GaloisField 2 q))ˣ,
                  (∀ j, b j ^ 3 = 1) ∧ rootDiagUnit .E7 b = w) ∧
              rootDiagUnit .E7 a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧
              rootDiagUnit .E7 a ≠ 1 ∧ Function.Injective iota ∧ iota.range = S.Γ ∧
              iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q) y) =
                rootDiagUnit .E7 a ∧
              CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c) ∧
              M.map (iota.comp
                (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q)).toMonoidHom) =
                rationalComponent S.ρ S.Γ (rootCharHom a) c ∧
              compRank (componentRoots (rootCharHom a) c) = 6 ∧
              (componentRoots (rootCharHom a) c).ncard = 72 ∧
              ¬ twistInner (componentRoots (rootCharHom a) c)
                ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
                  (componentRoots (rootCharHom a) c)]) ∧
              ∃ v : WeylGroup .E7, componentRoots (rootCharHom a) c =
                (fun alpha => v • alpha) '' parabolicRoots .E7 (e6Nodes .E7) ∧
                (∀ A : SL2 (AlgebraicClosure (GaloisField 2 q)),
                  S.D.g0⁻¹ * rootSL2 .E7 (AlgebraicClosure (GaloisField 2 q))
                    (Pi.single i 1) A * S.D.g0 ∈
                    rootSpan .E7 (AlgebraicClosure (GaloisField 2 q))
                      (componentRoots (rootCharHom a) c)) ∧
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) c) = 1 ∧
    ∃ (Phi : twistedE6Group 2 q →* e7Data_valid.minGroup (GaloisField 2 q))
      (phi : twistedE6Group 2 q →* ModGL .E7 (AlgebraicClosure (GaloisField 2 q)))
      (sigma : AlgebraicClosure (GaloisField 2 q) ≃+* AlgebraicClosure (GaloisField 2 q))
      (z : ModGL .E7 (AlgebraicClosure (GaloisField 2 q))) (gamma : Fin Tag.E7.rank → ℤ),
      Phi.range = M ∧ Phi.ker ≤ Subgroup.center (twistedE6Group 2 q) ∧
      (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q)).toMonoidHom).comp Phi = phi ∧
      phi.range = rationalComponent S.ρ S.Γ (rootCharHom a) c ∧
      phi.ker ≤ Subgroup.center (twistedE6Group 2 q) ∧
      (∀ x, sigma x = x ^ 2 ^ q) ∧ z ∈ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q))
        (componentRoots (rootCharHom a) c) ∧
      phi.range ≤ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q)) (componentRoots (rootCharHom a) c) ∧
      IsRoot .E7 gamma ∧ gamma ∈ componentRoots (rootCharHom a) c ∧
      -gamma ∈ componentRoots (rootCharHom a) c ∧
      (∀ g ∈ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q)) ({gamma, -gamma} : Set (Fin Tag.E7.rank → ℤ)),
        S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹) ∧
      ((twistedE6Datum 2 q).rootGroup (Pi.single (0 : Fin 4) 1)).map phi =
        ((rootSubgroup .E7 ↥(fixSubfield sigma) gamma).map
          (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom ∧
      ((twistedE6Datum 2 q).rootGroup (-Pi.single (0 : Fin 4) 1)).map phi =
        ((rootSubgroup .E7 ↥(fixSubfield sigma) (-gamma)).map
          (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom := by
  obtain ⟨q, hq4, hpq, lambda, hPP, r₀, hr₀A, hr₀C, hr₀R, j, Gamma, y, M,
      hroot, hGamma, hyp, hGammax, hM, hML, hRM, hstable⟩ :=
    exists_native_E7_centralizer_of_twistedE6_join_of_marking hL1 hRk1 hGen hOrb hL2 hPair hNbr
      hcfg hReg hARow hQTwo hpres hE7 hSix t n f ψ hψ hJoin hmark
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    subst q
    norm_num at hq4
  have hK : Nat.card (GaloisField 2 q) = 2 ^ q := GaloisField.card 2 q (by omega)
  have hy : y ≠ 1 := ne_one_of_E7_centralizer_of_twistedE6_join hcfg hJoin e hE7
    hmark
    (GaloisField 2 q) lambda hPP.2.1.1 y M hM hML
  obtain ⟨hxy, S, a, iota, hqCard, hFrCard, hformula, hinj, hrange, hBs, hcube,
      hT, hap, h1, hiy⟩ :=
    exists_langData_of_original_E7_bstar_actor hTB hWI hcfg hpres hE7 hJoin
      (GaloisField 2 q) lambda hPP.2.1.1 hPP.2.1.2 Gamma hGamma y hGammax
  have hq : S.D.q = 2 ^ q := hqCard.trans hK
  have hFr : ∃ Fr : AlgebraicClosure (GaloisField 2 q) →+*
      AlgebraicClosure (GaloisField 2 q),
      (∀ z, Fr z = z ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) := by
    obtain ⟨Fr, hFr, hPhi⟩ := hFrCard
    exact ⟨Fr, fun z => by rw [hqCard]; exact hFr z, hPhi⟩
  obtain ⟨c, hqs, hMR⟩ := exists_rational_component_of_native_E7_centralizer_of_langData
    Nat.prime_three (by norm_num) y hy M hM S a iota hT hap hinj hrange hiy
  obtain ⟨lab, hlab, hrow, hhas⟩ :=
    exists_label_of_native_E7_component_image ggRowP_ETwE6 hmark lambda hPP.2.1.2 M hML
      S a iota hinj c hMR
  obtain ⟨h6, h72, hout⟩ := outerE6_rootComponent_of_E7_hasLabel
    Nat.prime_three (by norm_num) S hT hap h1 c hqs hlab hrow.1 hhas
  have hpF : (3 : AlgebraicClosure (GaloisField 2 q)) ≠ 0 := by
    intro h
    have hdiv := (CharP.cast_eq_zero_iff (AlgebraicClosure (GaloisField 2 q)) 2 3).mp h
    norm_num at hdiv
  have hTp :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
  obtain ⟨v, hPsi⟩ := RCKRP.rckTw_levi_E78 (Or.inl rfl) S Nat.prime_three hpF hTp c h6 h72
  have hParent : ∀ A : SL2 (AlgebraicClosure (GaloisField 2 q)),
      S.D.g0⁻¹ * rootSL2 .E7 (AlgebraicClosure (GaloisField 2 q)) (Pi.single j 1) A *
        S.D.g0 ∈ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q))
          (componentRoots (rootCharHom a) c) :=
    e7_rootSL2_conj_mem_e6ComponentRootSpan_of_component j hM hRM S iota hformula
      a hiy c v hPsi
  have hcover := exists_ordinary_twistedE6_cover_of_rational_E7_component hqpos M S a iota
    hinj c hqs hMR hT v hPsi hout hq
  exact ⟨q, hq4, hpq, lambda, hPP, r₀, hr₀A, hr₀C, hr₀R, j, Gamma, y, M,
    hroot, hGamma, hyp, hGammax, hM, hML, hRM, hstable, hxy, hy,
    S, a, iota, c, hq, hFr, hformula, hBs, hcube, hT, hap, h1, hinj, hrange, hiy,
    hqs, hMR, h6, h72, hout, v, hPsi, hParent, hcover⟩

theorem exists_coherent_native_twistedE6_cover_of_original_E7_join_of_marking
    (hTB : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hL1 : GGSecFiveL1PhanInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hGen : GGSecFiveGenPhanInput) (hOrb : GGSecFiveOrbPhanInput)
    (hL2 : GGSecFiveL2PhanInput) (hPair : GGSecFivePhanPairInput)
    (hNbr : GGSecFiveNonSplitNbrInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hReg : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hARow : ¬ GGSecFivePhanARow p B Bs x L D J)
    (hQTwo : ¬ GGSecFiveQTwoCell p B Bs x L D J)
    {ι : Type} {N : CoxeterMatrix ι} {e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) N e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hSix : ¬ GGSecFiveJoinOrderSixAt p L Bs 𝒦 N e)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (hψ : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hmark : GGInnerDiagOnLabel ggRowP_ETwE6 p Bs L) :
    ∃ q : ℕ, 4 ≤ 2 ^ q ∧ p ∣ 2 ^ q + 1 ∧
      ∃ (lambda : e7Data_valid.minGroup (GaloisField 2 q) →* G),
        GGPresentsG0 (ggG0 p B x L D J) (e7Datum (GaloisField 2 q)) .E7 0 q lambda ∧
        ∃ r₀ : MulAut ↥Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl N e ∧
          GGIsReflection p r₀ ∧
          ∃ (i : Fin (Tag.rank .E7))
            (Γ : Bs →* MulAut (e7Data_valid.minGroup (GaloisField 2 q)))
            (y : e7Data_valid.minGroup (GaloisField 2 q))
            (M : Subgroup (e7Data_valid.minGroup (GaloisField 2 q))),
            (rankOne (e7Datum (GaloisField 2 q)).rootGroup i).map lambda =
                ggRankOnePerf Bs r₀ ∧
            (∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹) ∧
            y ^ p = 1 ∧ Γ ⟨x, hcfg.1.1.x_facts.1⟩ = MulAut.conj y ∧
            IsComponentOf M (Subgroup.centralizer {y}) ∧ M.map lambda = L ∧
            rankOne (e7Datum (GaloisField 2 q)).rootGroup i ≤ M ∧
            (∀ b z, z ∈ M → Γ b z ∈ M) ∧ lambda y = x ∧ y ≠ 1 ∧
            ∃ (S : LangSetup Tag.E7 (AlgebraicClosure (GaloisField 2 q)) 5)
              (a : Fin Tag.E7.rank → (AlgebraicClosure (GaloisField 2 q))ˣ)
              (iota : adjointGroup .E7 (GaloisField 2 q) →*
                ModGL .E7 (AlgebraicClosure (GaloisField 2 q)))
              (c : KernelComponent (rootCharHom a)),
              S.D.q = 2 ^ q ∧
              (∃ Fr : AlgebraicClosure (GaloisField 2 q) →+* AlgebraicClosure (GaloisField 2 q),
                (∀ z, Fr z = z ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
              (∀ z, iota z = S.D.g0⁻¹ *
                baseChangeGL (algebraMap (GaloisField 2 q) (AlgebraicClosure (GaloisField 2 q)))
                  (z : ModGL .E7 (GaloisField 2 q)) * S.D.g0) ∧
              (∀ u : e7Data_valid.minGroup (GaloisField 2 q), lambda u ∈ Bs →
                iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q) u) ∈
                  S.D.torus) ∧
              (∀ w : ModGL .E7 (AlgebraicClosure (GaloisField 2 q)),
                (∃ u : e7Data_valid.minGroup (GaloisField 2 q), lambda u ∈ Bs ∧
                  iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q) u) = w) ↔
                ∃ b : Fin Tag.E7.rank → (AlgebraicClosure (GaloisField 2 q))ˣ,
                  (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = w) ∧
              rootDiagUnit .E7 a ∈ S.D.torus ∧ (∀ j, a j ^ p = 1) ∧
              rootDiagUnit .E7 a ≠ 1 ∧ Function.Injective iota ∧ iota.range = S.Γ ∧
              iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q) y) =
                rootDiagUnit .E7 a ∧
              CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) c) ∧
              M.map (iota.comp
                (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q)).toMonoidHom) =
                rationalComponent S.ρ S.Γ (rootCharHom a) c ∧
              compRank (componentRoots (rootCharHom a) c) = 6 ∧
              (componentRoots (rootCharHom a) c).ncard = 72 ∧
              ¬ twistInner (componentRoots (rootCharHom a) c)
                ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
                  (componentRoots (rootCharHom a) c)]) ∧
              ∃ v : WeylGroup .E7, componentRoots (rootCharHom a) c =
                (fun alpha => v • alpha) '' parabolicRoots .E7 (e6Nodes .E7) ∧
                (∀ A : SL2 (AlgebraicClosure (GaloisField 2 q)),
                  S.D.g0⁻¹ * rootSL2 .E7 (AlgebraicClosure (GaloisField 2 q))
                    (Pi.single i 1) A * S.D.g0 ∈
                    rootSpan .E7 (AlgebraicClosure (GaloisField 2 q))
                      (componentRoots (rootCharHom a) c)) ∧
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) c) = 1 ∧
    ∃ (Phi : twistedE6Group 2 q →* e7Data_valid.minGroup (GaloisField 2 q))
      (phi : twistedE6Group 2 q →* ModGL .E7 (AlgebraicClosure (GaloisField 2 q)))
      (sigma : AlgebraicClosure (GaloisField 2 q) ≃+* AlgebraicClosure (GaloisField 2 q))
      (z : ModGL .E7 (AlgebraicClosure (GaloisField 2 q))) (gamma : Fin Tag.E7.rank → ℤ),
      Phi.range = M ∧ Phi.ker ≤ Subgroup.center (twistedE6Group 2 q) ∧
      (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 q)).toMonoidHom).comp Phi = phi ∧
      phi.range = rationalComponent S.ρ S.Γ (rootCharHom a) c ∧
      phi.ker ≤ Subgroup.center (twistedE6Group 2 q) ∧
      (∀ x, sigma x = x ^ 2 ^ q) ∧ z ∈ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q))
        (componentRoots (rootCharHom a) c) ∧
      phi.range ≤ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q)) (componentRoots (rootCharHom a) c) ∧
      IsRoot .E7 gamma ∧ gamma ∈ componentRoots (rootCharHom a) c ∧
      -gamma ∈ componentRoots (rootCharHom a) c ∧
      (∀ g ∈ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q)) ({gamma, -gamma} : Set (Fin Tag.E7.rank → ℤ)),
        S.D.step (z * g * z⁻¹) = z * frobGL sigma g * z⁻¹) ∧
      ((twistedE6Datum 2 q).rootGroup (Pi.single (0 : Fin 4) 1)).map phi =
        ((rootSubgroup .E7 ↥(fixSubfield sigma) gamma).map
          (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom ∧
      ((twistedE6Datum 2 q).rootGroup (-Pi.single (0 : Fin 4) 1)).map phi =
        ((rootSubgroup .E7 ↥(fixSubfield sigma) (-gamma)).map
          (baseChangeGL (fixSubfield sigma).subtype)).map (MulAut.conj z).toMonoidHom := by
  by_cases hp3 : p = 3
  · subst p
    exact exists_coherent_native_twistedE6_cover_of_original_E7_three_join_of_marking
      hTB hWI hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hReg hARow hQTwo
      hpres hE7 hSix t n f ψ hψ hJoin hmark
  · obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
    obtain ⟨q, hq4, hpq, lambda, hPP, r₀, hr₀A, hr₀C, hr₀R, j, Gamma, y, M,
        hroot, hGamma, hyp, hGammax, hM, hML, hRM, hstable⟩ :=
      exists_native_E7_centralizer_of_twistedE6_join_of_marking hL1 hRk1 hGen hOrb hL2 hPair hNbr
        hcfg hReg hARow hQTwo hpres hE7 hSix t n f ψ hψ hJoin hmark
    have hqpos : 0 < q := by
      by_contra h
      have hq0 : q = 0 := by omega
      subst q
      norm_num at hq4
    have hK : Nat.card (GaloisField 2 q) = 2 ^ q := GaloisField.card 2 q (by omega)
    have hy : y ≠ 1 := ne_one_of_E7_centralizer_of_twistedE6_join hcfg hJoin e hE7
      hmark
      (GaloisField 2 q) lambda hPP.2.1.1 y M hM hML
    obtain ⟨hxy, S, a, iota, hqCard, hFrCard, hformula, hinj, hrange, hBs, hcube,
        hT, hap, h1, hiy⟩ :=
      exists_langData_of_original_E7_bstar_actor_of_ne_three hTB hWI hcfg hp3 hpres hE7 hJoin
        (GaloisField 2 q) lambda hPP.2.1.1 hPP.2.1.2 Gamma hGamma y hGammax
    have hq : S.D.q = 2 ^ q := hqCard.trans hK
    have hFr : ∃ Fr : AlgebraicClosure (GaloisField 2 q) →+*
        AlgebraicClosure (GaloisField 2 q),
        (∀ z, Fr z = z ^ S.D.q) ∧ S.D.Φ = Units.map (entrywiseHom Fr) := by
      obtain ⟨Fr, hFr, hPhi⟩ := hFrCard
      exact ⟨Fr, fun z => by rw [hqCard]; exact hFr z, hPhi⟩
    obtain ⟨c, hqs, hMR⟩ := exists_rational_component_of_native_E7_centralizer_of_langData
      hp hp2 y hy M hM S a iota hT hap hinj hrange hiy
    obtain ⟨lab, hlab, hrow, hhas⟩ :=
      exists_label_of_native_E7_component_image ggRowP_ETwE6 hmark lambda hPP.2.1.2 M hML
        S a iota hinj c hMR
    obtain ⟨h6, h72, hout⟩ := outerE6_rootComponent_of_E7_hasLabel
      hp hp2 S hT hap h1 c hqs hlab hrow.1 hhas
    have hpF : (p : AlgebraicClosure (GaloisField 2 q)) ≠ 0 := by
      intro h
      have hdiv := (CharP.cast_eq_zero_iff (AlgebraicClosure (GaloisField 2 q)) 2 p).mp h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdiv).symm
    have hTp :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap
    obtain ⟨v, hPsi⟩ := RCKRP.rckTw_levi_E78 (Or.inl rfl) S hp hpF hTp c h6 h72
    have hParent : ∀ A : SL2 (AlgebraicClosure (GaloisField 2 q)),
        S.D.g0⁻¹ * rootSL2 .E7 (AlgebraicClosure (GaloisField 2 q)) (Pi.single j 1) A *
          S.D.g0 ∈ rootSpan .E7 (AlgebraicClosure (GaloisField 2 q))
            (componentRoots (rootCharHom a) c) :=
      e7_rootSL2_conj_mem_e6ComponentRootSpan_of_component j hM hRM S iota hformula
        a hiy c v hPsi
    have hcover := exists_ordinary_twistedE6_cover_of_rational_E7_component hqpos M S a iota
      hinj c hqs hMR hT v hPsi hout hq
    exact ⟨q, hq4, hpq, lambda, hPP, r₀, hr₀A, hr₀C, hr₀R, j, Gamma, y, M,
      hroot, hGamma, hyp, hGammax, hM, hML, hRM, hstable, hxy, hy,
      S, a, iota, c, hq, hFr, hformula, hBs, hcube, hT, hap, h1, hinj, hrange, hiy,
      hqs, hMR, h6, h72, hout, v, hPsi, hParent, hcover⟩

omit
    [Finite G] in
theorem selected_original_twistedE6_comp_of_native_cover {q : ℕ}
    {L : Subgroup G} (hq : 1 ≤ q)
    (lambda : e7Data_valid.minGroup (GaloisField 2 q) →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup (GaloisField 2 q)))
    (M : Subgroup (e7Data_valid.minGroup (GaloisField 2 q))) (hML : M.map lambda = L)
    (Phi : (ggU .twistedE6 0 q).K →* e7Data_valid.minGroup (GaloisField 2 q))
    (hPhi : Phi.range = M) (hPhiker : Phi.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K) :
    StatedLieAdmissible .twistedE6 0 2 q ∧ 2 ≤ (ggU .twistedE6 0 q).D.rank ∧
      (lambda.comp Phi).range = L ∧
      (lambda.comp Phi).ker ≤ Subgroup.center (ggU .twistedE6 0 q).K ∧
      ∃ model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 q).D (GaloisField 2 q)
        (Pi.single (0 : Fin 4) 1),
        ((lambda.comp Phi).comp model.phi).range =
          (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map (lambda.comp Phi) := by
  have hZ : Subgroup.center (e7Data_valid.minGroup (GaloisField 2 q)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective lambda :=
    (MonoidHom.ker_eq_bot_iff lambda).mp
      (le_antisymm (by simpa only [hZ] using hker) bot_le)
  have hrange : (lambda.comp Phi).range = L := by
    rw [MonoidHom.range_comp, hPhi, hML]
  have hcompker : (lambda.comp Phi).ker ≤ Subgroup.center (ggU .twistedE6 0 q).K := by
    rw [MonoidHom.ker_comp_of_injective Phi lambda hinj]
    exact hPhiker
  have hi : rhoPerm (1 : Fin Tag.E6.rank) = 1 := by decide +kernel
  have hp : proj (Pi.single (1 : Fin Tag.E6.rank) 1) = Pi.single (0 : Fin 4) 1 := by
    funext k
    fin_cases k <;> rfl
  have hmodels := exists_selectedSL2Model_twistedE6_fixed_comp hq 1 hi (lambda.comp Phi)
  rw [hp] at hmodels
  obtain ⟨model, hmodel⟩ := hmodels
  refine ⟨⟨Nat.prime_two, by omega, rfl⟩, ?_, hrange, hcompker, model, hmodel⟩
  change 2 ≤ 4
  decide +kernel

omit
    [Finite G] in
theorem selected_original_twistedE6_member_of_root_containment {q : ℕ}
    {Bs L : Subgroup G} (hq : 1 ≤ q)
    (lambda : e7Data_valid.minGroup (GaloisField 2 q) →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup (GaloisField 2 q)))
    (M : Subgroup (e7Data_valid.minGroup (GaloisField 2 q))) (hML : M.map lambda = L)
    (j : Fin Tag.E7.rank) (r₀ : MulAut Bs)
    (hroot : (rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map lambda = ggRankOnePerf Bs r₀)
    (Phi : (ggU .twistedE6 0 q).K →* e7Data_valid.minGroup (GaloisField 2 q))
    (hPhi : Phi.range = M) (hPhiker : Phi.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K)
    (v : e7Data_valid.minGroup (GaloisField 2 q)) (hv : v ∈ M)
    (hle : (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi ≤
      (rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map (MulAut.conj v).toMonoidHom) :
    ∃ psi : (ggU .twistedE6 0 q).K →* G,
      StatedLieAdmissible .twistedE6 0 2 q ∧ 2 ≤ (ggU .twistedE6 0 q).D.rank ∧
      psi.range = L ∧ psi.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K ∧
      ∃ model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 q).D (GaloisField 2 q)
        (Pi.single (0 : Fin 4) 1),
        (psi.comp model.phi).range = ggRankOnePerf Bs r₀ := by
  have hcomp := rootLevi_map_eq_of_le_rankOne_E7 hq Phi hPhiker j v hle
  have hZ : Subgroup.center (e7Data_valid.minGroup (GaloisField 2 q)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hlinj : Function.Injective lambda :=
    (MonoidHom.ker_eq_bot_iff lambda).mp (le_antisymm (by simpa [hZ] using hker) bot_le)
  let C := (MulAut.conj v⁻¹).toMonoidHom
  let lambda' := lambda.comp C
  let psi := lambda'.comp Phi
  have hCinj : Function.Injective lambda' := hlinj.comp (MulAut.conj v⁻¹).injective
  have hMconj : M.map C = M := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change v⁻¹ * a * v ∈ M
      exact M.mul_mem (M.mul_mem (M.inv_mem hv) ha) hv
    · intro hx
      refine ⟨v * x * v⁻¹, M.mul_mem (M.mul_mem hv hx) (M.inv_mem hv), ?_⟩
      change v⁻¹ * (v * x * v⁻¹) * v = x
      group
  have hker' : lambda'.ker ≤ Subgroup.center (e7Data_valid.minGroup (GaloisField 2 q)) := by
    rw [MonoidHom.ker_eq_bot lambda' hCinj]
    exact bot_le
  have hML' : M.map lambda' = L := by
    change M.map (lambda.comp C) = L
    rw [← Subgroup.map_map, hMconj, hML]
  obtain ⟨hadm, hrk, hpsirange, hpsiker, model, hmodel⟩ :=
    selected_original_twistedE6_comp_of_native_cover hq lambda' hker' M hML'
      Phi hPhi hPhiker
  have hcancel : C.comp (MulAut.conj v).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change v⁻¹ * (v * x * v⁻¹) * v = x
    group
  have hUndo :
      ((rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map
        (MulAut.conj v).toMonoidHom).map C =
      rankOne (e7Datum (GaloisField 2 q)).rootGroup j := by
    rw [Subgroup.map_map, hcancel, Subgroup.map_id]
  have hwhole : (psi.comp model.phi).range = ggRankOnePerf Bs r₀ := by
    change (ggRootLevi (twistedE6Datum 2 q) (Pi.single (0 : Fin 4) 1)).map Phi = _ at hcomp
    change (psi.comp model.phi).range =
      (ggRootLevi (twistedE6Datum 2 q) (Pi.single (0 : Fin 4) 1)).map psi at hmodel
    erw [hmodel, show psi = lambda.comp (C.comp Phi) from rfl,
      ← Subgroup.map_map, ← Subgroup.map_map, hcomp, hUndo, hroot]
  exact ⟨psi, hadm, hrk, hpsirange, hpsiker, model, hwhole⟩

omit
    [Finite G] in
theorem selected_original_twistedE6_member_of_whole_comparison {q : ℕ}
    {Bs L : Subgroup G} (hq : 1 ≤ q)
    (lambda : e7Data_valid.minGroup (GaloisField 2 q) →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup (GaloisField 2 q)))
    (M : Subgroup (e7Data_valid.minGroup (GaloisField 2 q))) (hML : M.map lambda = L)
    (j : Fin Tag.E7.rank) (r₀ : MulAut Bs)
    (hroot : (rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map lambda = ggRankOnePerf Bs r₀)
    (Phi : (ggU .twistedE6 0 q).K →* e7Data_valid.minGroup (GaloisField 2 q))
    (hPhi : Phi.range = M) (hPhiker : Phi.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K)
    (v : e7Data_valid.minGroup (GaloisField 2 q)) (hv : v ∈ M)
    (hcomp : (ggRootLevi (ggU .twistedE6 0 q).D (Pi.single (0 : Fin 4) 1)).map Phi =
      (rankOne (e7Datum (GaloisField 2 q)).rootGroup j).map (MulAut.conj v).toMonoidHom) :
    ∃ psi : (ggU .twistedE6 0 q).K →* G,
      StatedLieAdmissible .twistedE6 0 2 q ∧ 2 ≤ (ggU .twistedE6 0 q).D.rank ∧
      psi.range = L ∧ psi.ker ≤ Subgroup.center (ggU .twistedE6 0 q).K ∧
      ∃ model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 q).D (GaloisField 2 q)
        (Pi.single (0 : Fin 4) 1),
        (psi.comp model.phi).range = ggRankOnePerf Bs r₀ := by
  exact selected_original_twistedE6_member_of_root_containment hq lambda hker M hML
    j r₀ hroot Phi hPhi hPhiker v hv hcomp.le

end CFSG.StandardType
