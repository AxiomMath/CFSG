module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierTwoDLabel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDExport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourE8

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal.Spin
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.GLTheoremA.T171Sh
  CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDExport


theorem rckTwoD_graph_labelled
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hk : twistKind S.ρ (rootCharHom a) i = .twoD) :
    (τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) ∧
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
    ∃ v ∈ componentWeylGroup (componentRoots (rootCharHom a) i),
      (∀ γ ∈ componentRoots (rootCharHom a) i, S.rhoTwist v γ ∈ componentRoots (rootCharHom a) i) ∧
      (∀ γ ∈ posRoots (componentRoots (rootCharHom a) i),
        S.rhoTwist v γ ∈ posRoots (componentRoots (rootCharHom a) i)) ∧
      IsGraphTwist (componentRoots (rootCharHom a) i) (S.rhoTwist v) ∧
      ∃ (m : ℕ) (_ : 4 ≤ m) (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m),
        CompsPTwoDLabel.IsForkLabelling (componentRoots (rootCharHom a) i) (S.rhoTwist v) ε := by
  classical
  let Ψ := componentRoots (rootCharHom a) i
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  obtain ⟨hr, hcard⟩ := shape_of_twistKind_twoD hk
  change 4 ≤ compRank Ψ at hr
  by_cases h4 : compRank Ψ = 4
  · have hτ := tag_simplyLaced_of_twistKind_twoD_rank_four S hT i hk h4
    have hst := image_componentRoots_eq_of_twoD_rank_four rankFourTwoDE8Stable_holds S hT i hk h4
    have hs1 : componentOrbitLength S.ρ Ψ = 1 := componentOrbitLength_eq_one hfin
      (fun γ hγ => hst.subset (Set.mem_image_of_mem _ hγ))
    have hni : ¬ twistInner Ψ S.ρ := by
      have h := not_twistInner_of_twistKind_twoD_exc (Or.inl hk)
      rwa [hs1, Function.iterate_one] at h
    have hinner2 := twistInner_iterate_two_of_twistKind_twoD hk hs1 h4
    obtain ⟨v, hv, hmaps, hpos, hne⟩ := exists_rhoTwist_rankFour S hΨ hst hni
    have hinvol := rhoTwist_sq_eq_self S hΨ hst hinner2 hv hpos
    have hsl : ∀ β ∈ Ψ, iform β β = 2 := by
      intro β hβ
      rw [← dotProduct_mulVec_eq_iform]
      exact rootForm_self hτ (hΨ.isRoot β hβ)
    have hG := isGraphTwist_of_rankFour hΨ hsl h4 hcard (S.rhoTwist v)
      (S.iform_rhoTwist v) hmaps hpos hinvol hne
    obtain ⟨ε, hε⟩ := rckTwoD_forkLabelling_four hΨ hsl h4 hcard (S.rhoTwist v)
      (S.iform_rhoTwist v) hmaps hpos hinvol hne
    exact ⟨hτ, hs1, v, hv, hmaps, hpos, hG, 4, le_rfl, ε, hε⟩
  · have h5 : 5 ≤ compRank Ψ := by omega
    have hτ := simplyLaced_of_five_le_rank (h5.trans (compRank_le Ψ))
    have hs1 := S.componentOrbitLength_eq_one_of_five_leT hT i h5
    obtain ⟨v, hv, hmaps, hpos, hG, m, hm, ε, hε⟩ := exists_graphTwist_labelled S hT i hk h5
    exact ⟨hτ, hs1, v, hv, hmaps, hpos, hG, m, by omega, ε, hε⟩

theorem rckTwoD_pinned_setup
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ h : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (hq : S.D.q = 2 ^ h)
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD) :
    ∃ (m : ℕ) (_ : 4 ≤ m) (ε : simpleRoots (componentRoots (rootCharHom a) i) ≃ Fin m)
      (z : ModGL τ L) (D : CFSG.RankThree.Lattice.GenFixedRootDatum τ 2 L
        (SpanQuot (componentRoots (rootCharHom a) i))),
      D.e = h ∧ compRank (componentRoots (rootCharHom a) i) = m ∧
      (rationalComponent S.ρ S.Γ (rootCharHom a) i).map (MulAut.conj z⁻¹).toMonoidHom = D.orbitGroup ∧
      D.simpleRootsJ = ((simpleRoots (componentRoots (rootCharHom a) i) :
        Finset (Fin τ.rank → ℤ)) : Set (Fin τ.rank → ℤ)) ∧
      (∀ β γ : simpleRoots (componentRoots (rootCharHom a) i),
        corootPair (β : Fin τ.rank → ℤ) γ = cartanD m (ε β) (ε γ)) ∧
      (∀ j : Fin m, j.val + 2 < m → D.θ (toReal (ε.symm j)) = toReal (ε.symm j)) ∧
      (∀ a' b' : Fin m, a'.val + 2 = m → b'.val + 1 = m →
        D.θ (toReal (ε.symm a')) = toReal (ε.symm b') ∧
        D.θ (toReal (ε.symm b')) = toReal (ε.symm a')) ∧
      z ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) ∧
      ∀ x : adjointGroup τ L,
        S.D.step (z * (x : ModGL τ L) * z⁻¹) = z * (D.F x : ModGL τ L) * z⁻¹ := by
  classical
  obtain ⟨hτ, hs1, v, hv, hmaps, hpos, hG, m, hm, ε, hε⟩ := rckTwoD_graph_labelled S hT i hk
  obtain ⟨r, e, hr, hchar, he, hqe⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hchar ‹CharP L 2›
  subst hr2
  have heh : e = h := Nat.pow_right_injective (by decide : 2 ≤ 2) (hqe.symm.trans hq)
  subst heh
  have hst := (outer_componentOrbitLength_spec S hT i).2.1
  rw [hs1, Function.iterate_one] at hst
  obtain ⟨z, D, hDe, hDθ, hRC, hDs, hzZ, hF⟩ :=
    exists_twoD_export_of_graph S hτ hT i hq he hst v hv hmaps hpos hG
  have hrank : compRank (componentRoots (rootCharHom a) i) = m := by
    rw [compRank_eq_card (isRootComponent_componentRoots i), ← Fintype.card_coe,
      Fintype.card_congr ε, Fintype.card_fin]
  refine ⟨m, hm, ε, z, D, hDe, hrank, hRC, hDs, hε.1, ?_, ?_, hzZ, hF⟩
  · intro j hj
    rw [hDθ, latticeRealExt_toReal, hε.2.1 j hj]
  · intro a' b' ha' hb'
    obtain ⟨h1, h2⟩ := hε.2.2 a' b' ha' hb'
    rw [hDθ, latticeRealExt_toReal, latticeRealExt_toReal, h1, h2]
    exact ⟨rfl, rfl⟩

end CFSG.StandardType.RCKRP
