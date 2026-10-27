module

public import CFSG.LocalAnalysis.StandardType.GGK0LQD4Untw
public import CFSG.LocalAnalysis.StandardType.GGFamTwoDModel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDRecog
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.GLTheoremA.K155X CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.E6FourFine

private theorem lk0xlqtwod_label_of_model {X : Type} [Group X] {r N : ℕ} (h4 : 4 ≤ r)
    (h : CFSG.Open.StatedClassicalModel X .POmegaMinus r 2 N) : GGHasLabel ⟨.twD, r, N⟩ X := by
  have h2 : ¬ r = 2 := by omega
  have h3 : ¬ r = 3 := by omega
  unfold GGHasLabel LargeEvenRawDatum
  dsimp only
  rw [if_neg h2, if_neg h3]
  exact recipeOmegaMinus_of_statedClassicalModel h

private theorem lk0xlqtwod_finish {X : Type} [Group X] {r e N s q : ℕ} (h4 : 4 ≤ r)
    (hN : q ^ s = 2 ^ N) (hs : s = 1) (hq : q = 2 ^ e) (hlie : LieModel X .POmegaMinus r 2 e) :
    GGHasLabel ⟨.twD, r, N⟩ X := by
  rw [hs, pow_one, hq] at hN
  have heN : e = N := Nat.pow_right_injective (le_refl 2) hN
  rw [heN] at hlie
  exact lk0xlqtwod_label_of_model h4 (hlie.statedClassicalModel (by decide))

private theorem lk0xlqtwod_high
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i))
    (hD : (componentRoots (rootCharHom a) i).ncard =
      2 * compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) - 1))
    (hnin : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ e : ℕ, S.D.q = 2 ^ e ∧
        LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus
          (compRank (componentRoots (rootCharHom a) i)) 2 e := by
  classical
  have hL2 : ringChar L = 2 := ringChar.eq L 2
  have hst := S.image_componentRoots_eq_of_five_leT hT i h5
  have hρΨ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i :=
    fun γ hγ => by
      rw [← hst]
      exact ⟨γ, hγ, rfl⟩
  have hfin : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hs := componentOrbitLength_eq_one hfin hρΨ
  have hout : ¬ twistInner (componentRoots (rootCharHom a) i) (S.ρ : (Fin τ.rank → ℤ) → _) := by
    rw [hs, Function.iterate_one] at hnin
    exact hnin
  have hr := compRank_le_rank (componentRoots (rootCharHom a) i)
  have hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    cases τ <;> first | exact absurd (le_trans h5 hr) (by decide) | simp
  obtain ⟨e, he, hlie⟩ := TableCRes.fam_lieModel_rationalComponent_of_twoD_rank S hτ
    (rootCharHom a) i (fun γ hγ => outer_rho_mem_kernelRoots S hT hγ) hρΨ h5 hD hout a i rfl hp
    hpL hTp (fun r q => r = 2 ∨ 5 ≤ q) (CompsPTwoDRecog.twoDChainRecogAll_even_or_five L)
    (Or.inl hL2)
  rw [hL2] at he hlie
  exact ⟨hs, e, he.symm, hlie⟩

private theorem lk0xlqtwod_sq_inner {τ : Tag} {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ}
    {i : KernelComponent χ} (hk : twistKind ρ χ i = .twoD)
    (h4 : compRank (componentRoots χ i) = 4) :
    twistInner (componentRoots χ i)
      ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ (componentRoots χ i)]) := by
  unfold twistKind at hk
  split_ifs at hk with h1 h2 h3
  by_contra hcon
  exact h2 (Or.inr ⟨h4, by rw [h3.2, h4], hcon⟩)

private theorem lk0xlqtwod_four
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (h2 : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ e : ℕ, S.D.q = 2 ^ e ∧
        LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .POmegaMinus 4 2 e := by
  classical
  have hL2 : ringChar L = 2 := ringChar.eq L 2
  cases τ with
  | G2 =>
    have hle := compRank_le_rank (componentRoots (rootCharHom a) i)
    rw [h4] at hle
    exact absurd hle (by decide)
  | F4 =>
    obtain ⟨v, μ, -, hpinned⟩ := S.exists_pinnedT_of_prime hp hpL facts_F4 hTp
    obtain ⟨x, C, -, -, -, hr', hc'⟩ := hpinned i
    exact absurd (hc' ▸ hc) (kacCount_F4_four C (hr' ▸ h4))
  | D4 => exact absurd (rootDiagUnit_eq_one_of_ncard i (by rw [hc]; rfl)) h1
  | E6 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i h4 hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    refine ⟨hs, ?_⟩
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      have h := l154td4_d4_untw d4Base_E6 (d4SwapLayer_E6 e6FixDNAll_proved) d4SwapLayerFine_E6
        S hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) i v hv hρ hout h2 hf hq
      have hℓ2 : ℓ = 2 := (ringChar.eq L ℓ).symm.trans hL2
      subst hℓ2
      exact ⟨f, hq, h⟩
    · rw [hs, Function.iterate_one] at hout
      rw [hs] at h2
      obtain ⟨f, hf, h⟩ := l154td4_d4_tw S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hout
        (by simpa using h2)
      rw [ringChar.eq L 2] at hf h
      exact ⟨f, hf.symm, h⟩
  | E7 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i h4 hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    refine ⟨hs, ?_⟩
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have h := lq_d4_untw (Or.inr (Or.inl rfl)) d4Base_E7 (d4SwapLayer_E7 e6FixDNAll_proved)
      (lq_d4SwapLayerFine_E7) S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv
      hρ hout h2 hf hq
    have hℓ2 : ℓ = 2 := (ringChar.eq L ℓ).symm.trans hL2
    subst hℓ2
    exact ⟨f, hq, h⟩
  | E8 =>
    obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i h4 hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    refine ⟨hs, ?_⟩
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have h := lq_d4_untw (Or.inr (Or.inr rfl)) d4Base_E8 (d4SwapLayer_E8 e6FixDNAll_proved)
      (lq_d4SwapLayerFine_E8) S hFr hΦ hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv
      hρ hout h2 hf hq
    have hℓ2 : ℓ = 2 := (ringChar.eq L ℓ).symm.trans hL2
    subst hℓ2
    exact ⟨f, hq, h⟩

theorem lq_rec_twoD
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .twoD)
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.twD, compRank (componentRoots (rootCharHom a) i), N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hnin, h4, hD⟩ := twoD_kind_unpack hk
  by_cases h5 : 5 ≤ compRank (componentRoots (rootCharHom a) i)
  · obtain ⟨hs, e, hq, hlie⟩ := lk0xlqtwod_high S hp hpL hT hTp i h5 hD hnin
    exact lk0xlqtwod_finish h4 hN hs hq hlie
  · have h4' : compRank (componentRoots (rootCharHom a) i) = 4 := by omega
    have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by rw [hD, h4']
    obtain ⟨hs, e, hq, hlie⟩ := lk0xlqtwod_four S hp hpL hT hTp h1 i h4' hc hnin
      (lk0xlqtwod_sq_inner hk h4')
    rw [h4']
    exact lk0xlqtwod_finish (le_refl 4) hN hs hq hlie

end CFSG.StandardType.GGK0LQ

end
