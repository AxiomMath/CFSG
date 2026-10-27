module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
public import CFSG.ClassicalInvolution.Q3.Q3TWWMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Lie
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPD4Rank4All
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiag
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KEXC.Basic
public import CFSG.RankThree.PartOne.TCX.Ree.Perm
public import CFSG.RankThree.PartTwo.Sec8.Item87Proof84

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule MinData.Valid CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.Adapters.RankTwoModelTransports CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep)
open scoped Matrix

theorem rationalComponentM_eq_of_layer
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (hρ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (hqs : CFSG.IsQuasisimple ↥(rootSpan τ L (componentRoots χ i) ⊓ S.D.model)) :
    rationalComponentM S.ρ S.Γ χ i = rootSpan τ L (componentRoots χ i) ⊓ S.D.model := by
  have horbit : rationalRootsM S.ρ χ i = componentRoots χ i := by
    ext γ
    constructor
    · rintro ⟨k, δ, hδ, rfl⟩
      induction k generalizing δ with
      | zero => exact hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply]
        exact ih _ (hρ δ hδ)
    · intro hγ
      exact ⟨0, γ, hγ, rfl⟩
  set P := rootSpan τ L (componentRoots χ i) ⊓ S.D.model with hP
  have hPP : ⁅P, P⁆ = P := by
    have h1 := (Group.isPerfect_def.1 hqs.1)
    rw [_root_.commutator_def] at h1
    have h2 := congrArg (Subgroup.map P.subtype) h1
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  have hPΓ : P ≤ S.Γ := by
    rw [← hPP]
    exact Subgroup.commutator_mono inf_le_right inf_le_right
  have hspan : rationalSpanM S.ρ S.Γ χ i = P := by
    rw [rationalSpanM, horbit]
    refine le_antisymm ?_ ?_
    · exact inf_le_inf_left _ (Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem hx hy)
          (S.D.model.inv_mem hx)) (S.D.model.inv_mem hy))
    · exact le_inf inf_le_left hPΓ
  rw [rationalComponentM, hspan, hPP]

theorem lieModelM_rationalComponent_of_e6_outer
    {τ : Tag} [hτ : M27Ok τ] [E6Sub τ]
    {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (v : WeylGroup τ)
    (hΨ : componentRoots χ i = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ))
    (hρ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (hout : ¬ twistInner (componentRoots χ i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)])) :
    ∃ f : ℕ, 0 < f ∧ ringChar L ^ f = S.D.q ∧
      LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
        Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i)) .twistedE6 0
        (ringChar L) f := by
  classical
  have hτ' : ∀ t : TwistTag, t.tag ≠ τ := by
    rcases hτ.isE7E8 with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hw : ∀ γ ∈ componentRoots χ i, w • γ ∈ componentRoots χ i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext c
    rw [hFr, hq, iterateFrobenius_def]
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hroots : ∀ α ∈ parabolicRoots τ (e6Nodes τ), IsRoot τ α := fun α hα => hα.1
  set Ψ := componentRoots χ i with hΨdef
  have hmodel : rootSpan τ L Ψ ⊓ S.D.model = rootSpan τ L Ψ ⊓
      twistedFixedPoints nw (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, -, hxF⟩
      refine ⟨hx, ?_⟩
      have hxF' : S.D.n * S.D.Φ x * S.D.n⁻¹ = x := hxF
      rw [hn, hΦ, hFr'] at hxF'
      exact hxF'
    · rintro ⟨hx, hxF⟩
      refine ⟨hx, rootSpan_le_adjointGroup L _ hx, ?_⟩
      change S.D.n * S.D.Φ x * S.D.n⁻¹ = x
      rw [hn, hΦ, hFr']
      exact hxF
  have htrans := rootSpan_inf_twistedFixedPoints_smul (iterateFrobenius L ℓ f) v nw hroots
  have hnvM := canonicalRep_mem_monomialSubgroup L v
  have hnwM := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hπ : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    have e : (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hΨ' : Ψ = (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := hΨ
  have hmaps : ∀ α ∈ parabolicRoots τ (e6Nodes τ),
      weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ • α ∈ parabolicRoots τ (e6Nodes τ) := by
    intro α hα
    rw [hπ]
    have h1 : w • (v • α) ∈ (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
      rw [← hΨ']
      exact hw _ (by rw [hΨ']; exact ⟨α, hα, rfl⟩)
    obtain ⟨β, hβ, hβe⟩ := h1
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  have hwJ : MapsJ τ (e6Set τ) (weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩) := by
    intro α hα
    have := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at this
  obtain ⟨u, hu, π, hπ12, hact⟩ := exists_action hwJ
  have hπJ : ∀ i ∈ e6Set τ, π i ∈ e6Set τ := by
    rcases hπ12 with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set τ, π.symm i ∈ e6Set τ := by
    rcases hπ12 with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  have hπρ : π = rhoτ τ := by
    rcases hπ12 with h1 | h1
    · exfalso
      apply hout
      subst h1
      set g : WeylGroup τ := v * u * v⁻¹ with hg
      have hgcl : g ∈ Subgroup.closure
          {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} := by
        have hu2 : u ∈ parabolicWeylGroup τ (e6Nodes τ) := by
          rw [e6Nodes_eq_e6Set]
          exact hu
        exact conj_parabolicWeyl_mem_closure v hΨ' hu2
      have hact1 : ∀ γ ∈ Ψ, S.ρ γ = g • γ := by
        intro γ hγ
        have hγ' := hγ
        rw [hΨ'] at hγ'
        obtain ⟨α, hα, rfl⟩ := hγ'
        have hαJ : ∀ k, k ∉ e6Set τ → α k = 0 := by
          intro k hk
          exact hα.2 k (by rwa [e6Nodes_eq_e6Set])
        have hwα : (v⁻¹ * w * v) • α = u • α := by
          have hα_eq : α = ∑ j ∈ (Finset.univ.filter fun j => j ∈ e6Set τ),
              α j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
            funext k
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            by_cases hk : k ∈ e6Set τ
            · rw [Finset.sum_eq_single k]
              · simp
              · intro b hb hbk
                simp [Ne.symm hbk]
              · intro hk'
                exact absurd (by simpa using hk) hk'
            · rw [hαJ k hk, Finset.sum_eq_zero]
              intro b hb
              have hbk : k ≠ b := fun h => hk (h ▸ (Finset.mem_filter.1 hb).2)
              simp [hbk]
          rw [hα_eq, Finset.smul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjJ : j ∈ e6Set τ := (Finset.mem_filter.1 hj).2
          rw [smul_comm (v⁻¹ * w * v) (α j) _, smul_comm u (α j) _, ← hπ, hact j hjJ]
          rfl
        have hρw : S.ρ (v • α) = w • (v • α) :=
          S.rho_eq_smul hτ' hn (IsRoot.smul hα.1 v)
        have : w • (v • α) = v • ((v⁻¹ * w * v) • α) := by
          rw [mul_smul, mul_smul, smul_inv_smul]
        show S.ρ (v • α) = g • (v • α)
        rw [hρw, this, hwα, hg, mul_smul, mul_smul, inv_smul_smul]
      have hsts : ∀ γ ∈ Ψ, g • γ ∈ Ψ := fun γ hγ => by
        rw [← hact1 γ hγ]
        exact hρ γ hγ
      refine ⟨g ^ componentOrbitLength S.ρ Ψ, Subgroup.pow_mem _ hgcl _, ?_⟩
      have key : ∀ n : ℕ, ∀ γ ∈ Ψ, (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ = (g ^ n) • γ ∧
          (g ^ n) • γ ∈ Ψ := by
        intro n
        induction n with
        | zero => exact fun γ hγ => ⟨by simp, by simpa using hγ⟩
        | succ n ih =>
          intro γ hγ
          obtain ⟨h1, h2⟩ := ih γ hγ
          refine ⟨?_, ?_⟩
          · rw [Function.iterate_succ_apply', h1, hact1 _ h2, ← mul_smul, ← pow_succ']
          · rw [pow_succ', mul_smul]
            exact hsts _ h2
      exact fun γ hγ => (key _ γ hγ).1
    · exact h1
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    exists_conj_twistedFixed hf hn'M hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ12, hgen⟩
  have hψ : Function.Injective (psi2 τ L ℓ f) := by
    intro x y hxy
    apply Subtype.ext
    have h1 := baseChangeGL_injective _ hxy
    exact (m27Equiv τ (K2 L ℓ f)).symm.injective (Subtype.ext h1)
  have hrange : stdLayer τ ℓ f n₁ = (psi2 τ L ℓ f).range :=
    hstd.stdLayer_eq_range_of_rho hπρ
  set P₀ := rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
    twistedFixedPoints (nv⁻¹ * nw * nv) (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))
    with hP₀
  have hQeq : rootSpan τ L (parabolicRoots τ (e6Nodes τ)) = subsystemGroup τ L (e6Set τ) := by
    rw [subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  have hconj : P₀.map (MulAut.conj h).toMonoidHom = stdLayer τ ℓ f n₁ := by
    ext g
    constructor
    · rintro ⟨x, ⟨hxQ, hxF⟩, rfl⟩
      rw [hQeq] at hxQ
      refine mem_stdLayer.2 ⟨?_, ?_⟩
      · exact mul_mem (mul_mem hh hxQ) (inv_mem hh)
      · exact (hlang x).1 hxF
    · intro hg
      obtain ⟨hgQ, hgF⟩ := mem_stdLayer.1 hg
      have hx : h⁻¹ * g * h ∈ subsystemGroup τ L (e6Set τ) :=
        mul_mem (mul_mem (inv_mem hh) hgQ) hh
      have hhx : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
      refine ⟨h⁻¹ * g * h, ⟨by rw [hQeq]; exact hx, ?_⟩, hhx⟩
      refine (hlang _).2 ?_
      rw [hhx]
      exact hgF
  have hP : rootSpan τ L Ψ ⊓ S.D.model = P₀.map (MulAut.conj nv).toMonoidHom := by
    rw [hmodel, hΨ']
    exact htrans
  let e1 : ↥(rootSpan τ L Ψ ⊓ S.D.model) ≃* ↥P₀ :=
    (MulEquiv.subgroupCongr hP).trans (P₀.equivMapOfInjective _ (MulAut.conj nv).injective).symm
  let e2 : ↥P₀ ≃* ↥(stdLayer τ ℓ f n₁) :=
    (P₀.equivMapOfInjective _ (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hconj)
  let e3 : ↥(stdLayer τ ℓ f n₁) ≃* ↥(psi2 τ L ℓ f).range := MulEquiv.subgroupCongr hrange
  let e4 : ↥(psi2 τ L ℓ f).range ≃* ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :=
    (MonoidHom.ofInjective hψ).symm
  let e := e1.trans (e2.trans (e3.trans e4))
  have : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
  have hk : Nat.card (K2 L ℓ f) = (ℓ ^ f) ^ 2 := by rw [card_K2 hf, pow_mul']
  have hk4 : 4 ≤ Nat.card (K2 L ℓ f) := by
    rw [hk]
    have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
    nlinarith
  have hθq : ∀ c, theta2 L ℓ f c = c ^ ℓ ^ f := fun c => iterateFrobenius_def ℓ f c
  have hqsG := fixedGroup_isQuasisimple_of_four_le_card (theta2 L ℓ f) theta2_theta2 hk4
  have hqsP : CFSG.IsQuasisimple ↥(rootSpan τ L Ψ ⊓ S.D.model) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqsG
  have hR : rationalComponentM S.ρ S.Γ χ i = rootSpan τ L Ψ ⊓ S.D.model :=
    rationalComponentM_eq_of_layer S i hρ hqsP
  have hqiso : ↥(rootSpan τ L Ψ ⊓ S.D.model) ⧸ Subgroup.center ↥(rootSpan τ L Ψ ⊓ S.D.model) ≃*
      ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) ⧸
        Subgroup.center ↥(fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hlie : LieModel (↥(rootSpan τ L Ψ ⊓ S.D.model) ⧸
      Subgroup.center ↥(rootSpan τ L Ψ ⊓ S.D.model)) .twistedE6 0 ℓ f :=
    LieModel.of_mulEquiv hqiso.symm
      (lieModel_twistedE6_fixed (theta2 L ℓ f) theta2_theta2 hℓ hf hk hθq)
  have hring : ringChar L = ℓ := ringChar.eq L ℓ
  refine ⟨f, hf, ?_, ?_⟩
  · rw [hring, hq]
  · rw [hR, hring]
    exact hlie

end CFSG.StandardType.TableCRes
