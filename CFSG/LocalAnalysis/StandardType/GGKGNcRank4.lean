module

public import CFSG.LocalAnalysis.StandardType.GGKGNotCDefs
import CFSG.LocalAnalysis.StandardType.GGKGNcInner
import CFSG.LocalAnalysis.StandardType.GGKGNcD4Layer
import CFSG.LocalAnalysis.StandardType.GGKGNcTwist

public section

namespace CFSG.StandardType.KG

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KD4L
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KE6 CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPD4Layers
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.GLTheoremA.KD264Lie.ExcUntw
open scoped Matrix MatrixGroups

theorem kgNotC_of_rank_four
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    {p : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    (hp : Nat.Prime p)
    (hpL : (↑p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (hTp : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ^ p = 1)
    (ha1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ) (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hr : CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) =
      4)
    (hc : (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i).ncard = 24)
    (hnin : ¬CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
        (⇑S.ρ :
            (Fin τ.rank → ℤ) →
              Fin τ.rank →
                ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  have hE6 := e6FixDNAll_proved
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [hr] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ hr))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) ha1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      exact kgNotC_rationalComponent_of_d4_outer d4Base_E6
        d4TrialityLayer_E6 (d4SwapLayer_E6 hE6) d4TrialityLayerKGNotC_E6
        d4SwapLayerKGNotC_E6 S hFr hΦ' hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hnin
    · rw [hs, Function.iterate_one] at hnin
      refine kgNotC_rationalComponent_of_d4_twE6_of_layer S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv
        hρ hnin (fun ℓ f _ _ hf hqf n hn u hu π hleaf hπ1 _ hact => ?_)
      have h12 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 2 := e6Idx_ne (by decide)
      have h14 : e6Idx (τ := Tag.E6) 1 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have h24 : e6Idx (τ := Tag.E6) 2 ≠ e6Idx 4 := e6Idx_ne (by decide)
      have hv1 : (e6Idx (τ := Tag.E6) 1).val = 1 ∨ (e6Idx (τ := Tag.E6) 1).val = 2 ∨
          (e6Idx (τ := Tag.E6) 1).val = 4 := Or.inl rfl
      have hv2 : (e6Idx (τ := Tag.E6) 2).val = 1 ∨ (e6Idx (τ := Tag.E6) 2).val = 2 ∨
          (e6Idx (τ := Tag.E6) 2).val = 4 := Or.inr (Or.inl rfl)
      have hv4 : (e6Idx (τ := Tag.E6) 4).val = 1 ∨ (e6Idx (τ := Tag.E6) 4).val = 2 ∨
          (e6Idx (τ := Tag.E6) 4).val = 4 := Or.inr (Or.inr rfl)
      rcases hleaf with hc | hc | hc | hc | hc | hc
      · exact absurd hc hπ1
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h12 hv1 hv2 hn hu hact).2,
          twisted_swap_layer_kgNotC hf h12 hv1 hv2 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h14 hv1 hv4 hn hu hact).2,
          twisted_swap_layer_kgNotC hf h14 hv1 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_swap_layer_E6 hE6 hf h24 hv2 hv4 hn hu hact).2,
          twisted_swap_layer_kgNotC hf h24 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h12 h24 h14 hv1 hv2 hv4 hn hu hact).2,
          twisted_triality_layer_kgNotC hf h12 h24 h14 hv1 hv2 hv4 hn hu hact⟩
      · rw [hc] at hact
        exact ⟨(twisted_triality_layer_E6 hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact).2,
          twisted_triality_layer_kgNotC hf h14 h24.symm h12 hv1 hv4 hv2 hn hu hact⟩
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact kgNotC_rationalComponent_of_d4_outer d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 (d4SwapLayer_E7 hE6)
      d4TrialityLayerKGNotC_E7 d4SwapLayerKGNotC_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact kgNotC_rationalComponent_of_d4_outer d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 (d4SwapLayer_E8 hE6)
      d4TrialityLayerKGNotC_E8 d4SwapLayerKGNotC_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hnin

theorem kgNotC_rationalComponent_outerD
    {τ : CFSG.Blueprint.Chevalley.Tag}
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    {p : ℕ}
    (hp : Nat.Prime p)
    {a : Fin τ.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ (i : Fin τ.rank), a i ^ p = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ) (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hshape : 4 ≤
        CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
          (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) ∧
      (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i).ncard =
        2 *
            CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
              (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) *
          (CFSG.HardMathSupport.Timmesfeld.LangTorus.compRank
              (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) -
            1))
    (hout : ¬CFSG.HardMathSupport.Timmesfeld.LangTorus.twistInner
        (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)
        (⇑S.ρ :
            (Fin τ.rank → ℤ) →
              Fin τ.rank →
                ℤ)^[CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength S.ρ
            (CFSG.LieType.Chevalley.componentRoots (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)]) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · obtain ⟨m, e, -, hlie⟩ := lieModel_rationalComponent_of_twoD_highG hp S hT hap h1 i h5
      hshape.2 hout (fun _ _ => True)
      (fun r _ _ e m he hm5 _ => CompsPTwoDChainO.twoDChainRecog_all he (by omega)) trivial
    exact ⟨.POmegaMinus, m, e, by decide, hlie⟩
  · have hr4 : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
      rw [hshape.2, hr4]
    have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    exact kgNotC_of_rank_four S hp hpL hT hTp h1 i hr4 hc hout

theorem kgNotC_rationalComponent_E6
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E6 L p₀)
    {p : ℕ}
    (hp : Nat.Prime p)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit CFSG.Blueprint.Chevalley.Tag.E6 a ∈ S.D.torus)
    (hap : ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.E6.rank), a i ^ p = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit CFSG.Blueprint.Chevalley.Tag.E6 a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E6) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hq : CFSG.IsQuasisimple
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact kgNotC_rationalComponent_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact kgNotC_inner_nonA_E6 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact kgNotC_rationalComponent_outerD S hp hT hap h1 i hD' hinner
    · exact (false_of_e6Class_E S hp hpL hTp h1 i hE'.1 hE'.2).elim

theorem kgNotC_rationalComponent_E7
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E7 L p₀)
    {p : ℕ}
    (hp : Nat.Prime p)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E7.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit CFSG.Blueprint.Chevalley.Tag.E7 a ∈ S.D.torus)
    (hap : ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.E7.rank), a i ^ p = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit CFSG.Blueprint.Chevalley.Tag.E7 a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E7) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hq : CFSG.IsQuasisimple
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact kgNotC_rationalComponent_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact kgNotC_inner_nonA_E7 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact kgNotC_rationalComponent_outerD S hp hT hap h1 i hD' hinner
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E7 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, by decide, hlie⟩

theorem kgNotC_rationalComponent_E8
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup CFSG.Blueprint.Chevalley.Tag.E8 L p₀)
    {p : ℕ}
    (hp : Nat.Prime p)
    {a : Fin CFSG.Blueprint.Chevalley.Tag.E8.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit CFSG.Blueprint.Chevalley.Tag.E8 a ∈ S.D.torus)
    (hap : ∀ (i : Fin CFSG.Blueprint.Chevalley.Tag.E8.rank), a i ^ p = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit CFSG.Blueprint.Chevalley.Tag.E8 a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := CFSG.Blueprint.Chevalley.Tag.E8) (M := Lˣ)
      (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hq : CFSG.IsQuasisimple
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact kgNotC_rationalComponent_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact kgNotC_inner_nonA_E8 S hp hpL hT hTp i hA hinner
  · obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA' | hD' | hE'
    · exact (hA hA').elim
    · exact kgNotC_rationalComponent_outerD S hp hT hap h1 i hD' hinner
    · obtain ⟨f, -, -, hlie⟩ :=
        lieModel_rationalComponent_of_outer_E8 S hp hpL hT hTp i hE'.1 hE'.2 hinner
      exact ⟨.twistedE6, 0, f, by decide, hlie⟩

theorem kgNotC_rationalComponent_E
    {τ : CFSG.Blueprint.Chevalley.Tag}
    (hτ : τ = CFSG.Blueprint.Chevalley.Tag.E6 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E7 ∨ τ = CFSG.Blueprint.Chevalley.Tag.E8)
    {L : Type}
    [Field L]
    [IsAlgClosed L]
    {p₀ : ℕ}
    (S : CFSG.HardMathSupport.Timmesfeld.LangTorus.LangSetup τ L p₀)
    {p : ℕ}
    (hp : Nat.Prime p)
    {a : Fin τ.rank → Lˣ}
    (hT : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ (i : Fin τ.rank), a i ^ p = 1)
    (h1 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit τ a ≠ 1)
    (i : CFSG.LieType.Chevalley.KernelComponent (τ := τ) (M := Lˣ) (CFSG.LieType.AlgebraicGroups.rootCharHom a))
    (hq : CFSG.IsQuasisimple
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i)) :
    CFSG.StandardType.KG.KGNotCLieType (ringChar L)
      ↥(CFSG.HardMathSupport.Timmesfeld.LangTorus.rationalComponent S.ρ S.Γ (CFSG.LieType.AlgebraicGroups.rootCharHom a) i) := by
  rcases hτ with rfl | rfl | rfl
  · exact kgNotC_rationalComponent_E6 S hp hT hap h1 i hq
  · exact kgNotC_rationalComponent_E7 S hp hT hap h1 i hq
  · exact kgNotC_rationalComponent_E8 S hp hT hap h1 i hq

end CFSG.StandardType.KG
