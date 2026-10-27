module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeShapeLeaves
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4PairOfFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameD4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameETw
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCarrierSL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterCartan
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.GLTheoremA.T171Sh CFSG.StandardType.GGFinModel
  CFSG.LieType.AlgebraicGroups CFSG.StandardType.S2MathFi1035Pos

theorem rckTriD4_not_twistInner_two_of_exc {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    {i : KernelComponent χ} (h : twistKind ρ χ i = .exc)
    (hr : compRank (componentRoots χ i) = 4) :
    ¬ twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]) := by
  unfold twistKind at h
  split_ifs at h with h1 h2
  rcases h2 with ⟨h6, -⟩ | ⟨-, -, h3⟩
  · omega
  · exact h3


theorem rckPairTriD4_holds : RCKPairTriD4 := by
  intro τ p₀ S a hT p hp hp2 hTp i h hq ⟨hk, h4⟩ _
  have hc := ncard_of_twistKind_exc_rank_four hk h4
  have hout := not_twistInner_of_twistKind_twoD_exc (Or.inr ⟨hk, h4⟩)
  have h2 := rckTriD4_not_twistInner_two_of_exc hk h4
  have hh : 1 ≤ h := carrierSL_exp_pos S hq
  have hpL : (p : GGL) ≠ 0 := carrierSL_natCast_ne_zero hp hp2
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot _).subset fun γ hγ => isRoot_of_mem_componentRoots hγ
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [h4] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ h4))
  | D4 =>
    have hΨ : componentRoots (rootCharHom a) i = {γ : Fin Tag.D4.rank → ℤ | IsRoot Tag.D4 γ} := by
      refine Set.eq_of_subset_of_ncard_le (fun γ hγ => isRoot_of_mem_componentRoots hγ) ?_
        (finite_setOf_isRoot Tag.D4)
      rw [ncard_setOf_isRoot, hc]
      exact le_rfl
    have hρ : ∀ γ ∈ componentRoots (rootCharHom a) i,
        S.ρ γ ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact fun γ hγ => (S.frob.isRoot_iff γ).2 hγ
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, Function.iterate_one, hΨ] at hout
    exact rckFrameCoverPair_triD4_of_frame S a i hh hρ (hΨ ▸ rckTriD4Frame_D4 S hq hout)
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have hyz := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at hyz)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i h4 hc
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, Function.iterate_one] at hout
    rw [hs, mul_one] at h2
    exact rckFrameCoverPair_triD4_of_frame S a i hh hρ
      (rckTriD4Frame_E (Or.inl rfl) S hq i v hv hρ hout h2)
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have hyz := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at hyz)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i h4 hc
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, Function.iterate_one] at hout
    rw [hs, mul_one] at h2
    exact rckFrameCoverPair_triD4_of_frame S a i hh hρ
      (rckTriD4Frame_E (Or.inr (Or.inl rfl)) S hq i v hv hρ hout h2)
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have hyz := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at hyz)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i h4 hc
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, Function.iterate_one] at hout
    rw [hs, mul_one] at h2
    exact rckFrameCoverPair_triD4_of_frame S a i hh hρ
      (rckTriD4Frame_E (Or.inr (Or.inr rfl)) S hq i v hv hρ hout h2)

end CFSG.StandardType.RCKRP

end
