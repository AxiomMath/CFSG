module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover6Aux2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairTwCover78
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacShape
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacEAll
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.LieType.HighestRoot.RootsUnitary

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.TwistedE6
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.ClassicalInvolution.ModelFacts
  CFSG.LieType.RootSystem CFSG.LieType.HighestRoot CFSG.LieType.Steinberg
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open scoped MatrixGroups commutatorElement

theorem rckTw_levi_E78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0) {a : Fin τ.rank → Lˣ}
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : compRank (componentRoots (rootCharHom a) i) = 6)
    (hn : (componentRoots (rootCharHom a) i).ncard = 72) :
    ∃ v : WeylGroup τ, componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (e6Nodes τ) := by
  classical
  rcases hτ with rfl | rfl
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have hc6 : c.length = 6 := by rw [← hrank]; exact h6
    have h72 : kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset = 72 := by
      rw [← hncard]; exact hn
    have hCeq := kacCount_E7_six ((c.map (idxNode (r := Tag.E7.rank))).toFinset)
      (by rw [e7_card c hc, hc6]) h72
    refine ⟨v, ?_⟩
    rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE7 facts_E7 (J := e6Nodes Tag.E7)
      (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have hc6 : c.length = 6 := by rw [← hrank]; exact h6
    have h72 : kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset = 72 := by
      rw [← hncard]; exact hn
    have hCeq := kacCount_E8_six ((c.map (idxNode (r := Tag.E8.rank))).toFinset)
      (by rw [e8_card c hc, hc6]) h72
    refine ⟨v, ?_⟩
    rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE8 facts_E8 (J := e6Nodes Tag.E8)
      (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]

theorem rckTw_isLongestRoot_of_maxHeight
    {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {γ₀ : Fin D.rank → ℤ} (hγ₀ : γ₀ ∈ D.roots)
    (hmax : ∀ δ ∈ D.roots, ht δ ≤ ht γ₀) : IsLongestRoot D γ₀ := by
  have hrank : 0 < D.rank := by
    obtain ⟨w, i, -⟩ | ⟨w, i, -, -⟩ := hγ₀
    · exact Fin.pos i
    · exact Fin.pos i
  obtain ⟨r, hr⟩ := exists_isHighestRoot D hirr hdiv hrank
  have hdom : IsDominant D.isFiniteType γ₀ :=
    isDominant_of_ht_le D.isFiniteType fun k =>
      hmax _ (weylAction_mem_roots D.isFiniteType _ hγ₀)
  have h0 : (0 : Fin D.rank → ℤ) ≤ γ₀ := nonneg_of_isDominant D.isFiniteType hγ₀ hdom
  rcases hr.mem_roots with ⟨w, i, hwi⟩ | ⟨w, i, hi, hwi⟩
  · have hle : γ₀ ≤ r :=
      le_of_nonneg D.isFiniteType hirr hwi hr.longest hr.dominant hγ₀ h0
    have hht : ht γ₀ = ht r :=
      le_antisymm (hr.height_le γ₀ hγ₀) (hmax r hr.mem_roots)
    have hsum : ∑ k, (r - γ₀) k = 0 := by
      have h1 : (∑ k, r k) - (∑ k, γ₀ k) = 0 := by
        have : ht r = ht γ₀ := hht.symm
        simpa only [ht] using sub_eq_zero.mpr this
      calc ∑ k, (r - γ₀) k = (∑ k, r k) - (∑ k, γ₀ k) := by
            simp only [Pi.sub_apply, Finset.sum_sub_distrib]
        _ = 0 := h1
    have heq : γ₀ = r := by
      have hsub : r - γ₀ = 0 := by
        by_contra hne
        have h0' : 0 ≤ r - γ₀ := sub_nonneg.mpr hle
        have h1 := one_le_sum_of_nonneg h0' hne
        omega
      exact (sub_eq_zero.mp hsub).symm
    rw [heq]
    exact hr.isLongestRoot
  · rw [hdiv] at hi
    exact absurd hi (Set.notMem_empty i)

theorem rckTw_isLongestRoot_of_longRoot
    {K : Type*} [Group K] {D : UniversalRootDatum K}
    (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {β : Fin D.rank → ℤ} (hβ : GGLongRoot D β) : IsLongestRoot D β := by
  obtain ⟨w, γ₀, hγ₀, hmax, hβeq⟩ := hβ
  have hL : IsLongestRoot D γ₀ :=
    rckTw_isLongestRoot_of_maxHeight hirr hdiv hγ₀ hmax
  have hmap : IsLongestRoot D (weylAction D.isFiniteType w γ₀) := hL.map_weylAction w
  simpa [hβeq] using hmap


theorem rckPairTwE6_holds
    : RCKPairTwE6 := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq hshape hquasi
  classical
  obtain ⟨hkind, h6⟩ := hshape
  have hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    intro hin
    simp [twistKind, hin] at hkind
  have hn : (componentRoots (rootCharHom a) i).ncard = 72 := by
    by_contra hne
    simp [twistKind, hout, h6, hne] at hkind
    split_ifs at hkind <;> exact absurd hkind (by decide)
  have hτ := rckA4_tag h6
  have hpL := rckA4_cast_ne_zero hp hp2
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · have := S.hqpow.1
      rw [hq, h0, pow_zero] at this
      exact absurd this not_isPrimePow_one
    · exact h0
  have key : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ (φ : twistedE6Group 2 h →* ModGL τ GGL) (σ : GGL ≃+* GGL) (z : ModGL τ GGL)
        (γ : Fin τ.rank → ℤ),
        φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
        φ.ker ≤ Subgroup.center (twistedE6Group 2 h) ∧
        (∀ c, σ c = c ^ 2 ^ h) ∧ z ∈ rootSpan τ GGL (componentRoots (rootCharHom a) i) ∧
        φ.range ≤ rootSpan τ GGL (componentRoots (rootCharHom a) i) ∧ IsRoot τ γ ∧
        γ ∈ componentRoots (rootCharHom a) i ∧ -γ ∈ componentRoots (rootCharHom a) i ∧
        (∀ g ∈ rootSpan τ GGL ({γ, -γ} : Set (Fin τ.rank → ℤ)),
          S.D.step (z * g * z⁻¹) = z * frobGL σ g * z⁻¹) ∧
        ((twistedE6Datum 2 h).rootGroup (Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup τ ↥(fixSubfield σ) γ).map (baseChangeGL (fixSubfield σ).subtype)).map
            (MulAut.conj z).toMonoidHom ∧
        ((twistedE6Datum 2 h).rootGroup (-Pi.single (0 : Fin 4) 1)).map φ =
          ((rootSubgroup τ ↥(fixSubfield σ) (-γ)).map
            (baseChangeGL (fixSubfield σ).subtype)).map (MulAut.conj z).toMonoidHom := by
    rcases hτ with rfl | rfl | rfl
    · exact rckTw6_cover_all S hT i h6 hn hout hh hq
    · obtain ⟨v, hv⟩ := rckTw_levi_E78 (Or.inl rfl) S hp hpL hTp i h6 hn
      exact rckTw_cover_E78 S hT i v hv hout hh hq
    · obtain ⟨v, hv⟩ := rckTw_levi_E78 (Or.inr rfl) S hp hpL hTp i h6 hn
      exact rckTw_cover_E78 S hT i v hv hout hh hq
  obtain ⟨hs1, φ, σ, z, γ, hrange, hker, -, hzspan, hφspan, hγr, hγΨ, hγΨ', hzstep, hpin,
    hpin'⟩ := key
  have hΨK : componentRoots (rootCharHom a) i ⊆ kernelRoots (rootCharHom a) := fun α hα => by
    rw [componentRoots] at hα
    exact hα.choose
  have hspanH : rootSpan τ GGL (componentRoots (rootCharHom a) i) ≤
      torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)) := by
    refine le_sup_of_le_right ?_
    rw [rootSpan]
    exact iSup₂_le fun α hα => le_iSup₂_of_le α (hΨK hα) le_rfl
  have hzH := hspanH hzspan
  have hφH := hφspan.trans hspanH
  have hadm : StatedLieAdmissible .twistedE6 0 2 h := ⟨Nat.prime_two, hh, rfl⟩
  have hrk : 2 ≤ (ggU .twistedE6 0 h).D.rank := by
    show 2 ≤ (twistedE6Datum 2 h).rank
    show 2 ≤ 4
    norm_num
  haveI hfinM : Finite (ggU .twistedE6 0 h).K :=
    ggU_finite_exc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) ⟨hadm, hrk⟩
  obtain ⟨hcommM, -⟩ := ggU_perfect_lieModel hadm hrk
  have hsplit := CFSG.StandardType.LieOddCover.oddCentralSplit_ggU_pos (t := .twistedE6) (n := 0)
    (f := h) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))) hadm
  unfold RCKFrameCoverPair
  rw [hs1]
  simp only [Nat.mul_one]
  refine ⟨ggU .twistedE6 0 h, φ, rfl, ?_, hrange, hker, hfinM, Group.isPerfect_def.2 hcommM,
    hsplit, ?_⟩
  · exact Or.inl ⟨.twistedE6, 0,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), hadm, rfl⟩
  · intro _ β' hβ' hlong
    have hφmodel : φ.range ≤ S.D.model := by
      rw [hrange]
      have hΓ : S.Γ ≤ S.D.model := (Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem hx hy)
          (S.D.model.inv_mem hx)) (S.D.model.inv_mem hy) :
        ⁅S.D.model, S.D.model⁆ ≤ S.D.model)
      refine le_trans ?_ hΓ
      exact Subgroup.commutator_le.2 fun x hx y hy => by
        rw [commutatorElement_def]
        exact S.Γ.mul_mem (S.Γ.mul_mem (S.Γ.mul_mem hx.2 hy.2) (S.Γ.inv_mem hx.2))
          (S.Γ.inv_mem hy.2)
    obtain ⟨_, _, hct, -⟩ := hasBruhatDatum .twistedE6 0 2 h Nat.prime_two trivial hadm
    obtain ⟨hirr, hratio⟩ := cartanOK .twistedE6 0 2 h Nat.prime_two trivial hadm
    have hdiv : (ggU .twistedE6 0 h).D.divisible = ∅ := rfl
    have hl0 := isLongestRoot_single .twistedE6 0 2 h Nat.prime_two trivial hadm
      ⟨0, by show 0 < 4; norm_num⟩ (by show 0 < 2; norm_num)
    have hlβ : IsLongestRoot (modelUniv .twistedE6 0 2 h Nat.prime_two).D β' :=
      rckTw_isLongestRoot_of_longRoot hirr hdiv hlong
    obtain ⟨u, hu1, hu2⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hratio hl0 hlβ
    obtain ⟨z', hz'mem, hst1, hst2, hfx1, hfx2⟩ := rckPair_assemble S σ z hzH hzstep
      (H := torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)))
      (X := (ggU .twistedE6 0 h).D.rootGroup) φ hφmodel hφH hγr
      (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) hpin hpin' u hu1 hu2
    exact ⟨γ, hγΨ, z', hz'mem, hst1, hst2, hfx1, hfx2⟩

end CFSG.StandardType.RCKRP

end
