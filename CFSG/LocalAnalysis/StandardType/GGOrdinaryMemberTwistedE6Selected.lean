module
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberE7RootComparison

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

variable {G : Type} [Group G] [Finite G]

theorem exists_selected_twistedE6_member_of_original_E7_join_of_marking
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
    ∃ r₀ : MulAut Bs, r₀ ∈ ggAutomizer L Bs ∧ r₀ ∈ ggCoxRefl N e ∧
      ∃ (t' : StatedLieTag) (n' f' : ℕ) (ψ' : (ggU t' n' f').K →* G),
        StatedLieAdmissible t' n' 2 f' ∧ 2 ≤ (ggU t' n' f').D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' f').K ∧ ψ'.range = L ∧
        ∃ (k' : Type) (_ : Field k') (_ : Finite k') (_ : CharP k' 2)
          (δ : Fin (ggU t' n' f').D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU t' n' f').D k' δ),
          (ψ'.comp model.phi).range = ggRankOnePerf Bs r₀ := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  obtain ⟨q, hq4, hpq, lambda, hPP, r0, hrA, hrC, hrR, j, Gamma, y, M,
      hroot, hGamma, hyp, hGammaX, hM, hML, hRM, hstable, hxy, hy,
      S, a, iota, c, hq, hFr, hformula, hBST, hcube, hT, hap, h1, hinj, hrange, hiy,
      hqs, hMR, h6, h72, hout, w, hPsi, hParent, hOrbit,
      Phi, phi, sigma, z, gamma, hPhiRange, hPhiKer, hcomm, hphiRange, hphiKer,
      hsigma, hz, hphiLe, hgamma, hgPsi, hngPsi, hstep, hpos, hneg⟩ :=
    exists_coherent_native_twistedE6_cover_of_original_E7_join_of_marking
      hTB hWI hL1 hRk1 hGen hOrb hL2 hPair hNbr hcfg hReg hARow hQTwo
      hpres hE7 hSix t n f ψ hψ hJoin hmark
  have hq0 : q ≠ 0 := by intro h; simp only [h, pow_zero] at hq4; omega
  have hq1 : 1 ≤ q := by omega
  have hK : Nat.card (GaloisField 2 q) = 2 ^ q := GaloisField.card 2 q hq0
  have hK4 : 4 ≤ Nat.card (GaloisField 2 q) := hK.symm ▸ hq4
  have hBs : Bs ≤ lambda.range := by
    rw [hPP.2.1.1]
    exact bstar_le_ggG0_of_original_E7 hTB hWI hcfg hpres hE7 hJoin
  have hfull : ∀ b : Fin Tag.E7.rank → (AlgebraicClosure (GaloisField 2 q))ˣ,
      (∀ i, b i ^ p = 1) → rootDiagUnit .E7 b ∈ S.D.torus := by
    intro b hb
    obtain ⟨u, hu, heq⟩ := (hcube (rootDiagUnit .E7 b)).2 ⟨b, hb, rfl⟩
    rw [← heq]
    exact hBST u hu
  have hplus : p ∣ S.D.q + 1 := by simpa only [hq] using hpq
  have hRho := rho_eq_neg_of_full_torsion_torus_E7 hp hp2 S hfull hplus
  obtain ⟨Fr, hFr, hPhiFr⟩ := hFr
  have hsigFr : sigma.toRingHom = Fr := by
    ext u
    exact (hsigma u).trans (by simpa only [hq] using (hFr u).symm)
  have hPhiSigma : S.D.Φ = frobGL sigma := by
    unfold frobGL
    rw [hsigFr]
    exact hPhiFr
  have hsigmaCard : ∀ u, sigma u = u ^ Nat.card (GaloisField 2 q) := by
    intro u
    rw [hK]
    exact hsigma u
  have hyBs : lambda y ∈ Bs := by
    rw [hxy]
    exact hcfg.1.1.x_facts.1
  obtain ⟨v, hvM, hcomp⟩ := exists_original_twistedE6_root_comparison hp hp2 hK4
    lambda hPP.2.1.2 hBs S iota hinj hrange hformula hcube hrR hrA j hroot
    sigma hsigmaCard hPhiSigma hRho y M hM hML hRM a hyBs hiy c w hMR hPsi
    hq1 hq Phi phi hcomm z gamma hgamma hgPsi hz hstep hpos hneg
  obtain ⟨psi, hadm, hrk, hrangeL, hker, model, hwhole⟩ :=
    selected_original_twistedE6_member_of_whole_comparison hq1 lambda hPP.2.1.2 M hML
      j r0 hroot Phi hPhiRange hPhiKer v hvM hcomp
  exact ⟨r0, hrA, hrC, .twistedE6, 0, q, psi, hadm, hrk, hker, hrangeL,
    GaloisField 2 q, inferInstance, inferInstance, inferInstance,
    Pi.single (0 : Fin 4) 1, model, hwhole⟩

end CFSG.StandardType
