module

public import CFSG.LocalAnalysis.StandardType.GGK0LQD4TwE6
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcD4Action
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove
public import CFSG.RankThree.PartOne.KD4L.TrialityLayer

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Lattice
  CFSG.StandardType.TablePThreeKG

private theorem lk0xlqtrid4_model
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
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ f : ℕ, 2 ^ f = S.D.q ∧
        LieModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .trialityD4 0 2 f := by
  classical
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
      obtain ⟨f, hf, hmodel⟩ := lieModel_rationalComponent_of_d4_triality d4Base_E6
        d4TrialityLayer_E6 S hFr hΦ' hn (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ)
        i v hv hρ hout h2
      rw [ringChar.eq L 2] at hf hmodel
      exact ⟨f, hf, hmodel⟩
    · rw [hs, Function.iterate_one] at hout
      rw [hs, mul_one] at h2
      obtain ⟨f, hf, hmodel⟩ := lq_triD4_twE6 S ⟨t, ht, Fr, hFr, hΦ⟩ i v hv hρ hout h2
      rw [ringChar.eq L 2] at hf hmodel
      exact ⟨f, hf, hmodel⟩
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
    obtain ⟨f, hf, hmodel⟩ := lieModel_rationalComponent_of_d4_triality d4Base_E7
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hout h2
    rw [ringChar.eq L 2] at hf hmodel
    exact ⟨f, hf, hmodel⟩
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
    obtain ⟨f, hf, hmodel⟩ := lieModel_rationalComponent_of_d4_triality d4Base_E8
      CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 S hFr hΦ hn
      (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) i v hv hρ hout h2
    rw [ringChar.eq L 2] at hf hmodel
    exact ⟨f, hf, hmodel⟩

theorem lq_rec_triD4
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hTp : rootDiagUnit τ a ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hk : twistKind S.ρ (rootCharHom a) i = .exc)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4)
    {N : ℕ} (hN : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ N) :
    GGHasLabel ⟨.triD4, 0, N⟩
      (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hnin, hcases⟩ := exc_kind hk
  have hc : (componentRoots (rootCharHom a) i).ncard = 24 := by
    rcases hcases with ⟨h6, -⟩ | ⟨-, h, -⟩
    · omega
    · exact h
  have h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
    rcases hcases with ⟨h6, -⟩ | ⟨-, -, h2'⟩
    · omega
    · exact h2'
  obtain ⟨hs, f, hf, hlie⟩ := lk0xlqtrid4_model S hp hpL hT hTp h1 i h4 hc hnin h2
  rw [hs, pow_one, ← hf] at hN
  have hfN : f = N := Nat.pow_right_injective (le_refl 2) hN
  rw [hfN] at hlie
  obtain ⟨-, hm⟩ := hlie.chevalleyExceptionalModel (by decide)
  exact recipeTwisted_of_twistedChevalleyModel .D4 hm

end CFSG.StandardType.GGK0LQ

end
