module

public import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoF4Class
public import CFSG.LocalAnalysis.StandardType.GGLangDetectsTwoRefl
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoRoots
import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

private theorem j4cF4HubP_holds :
    ∀ γ ∈ rts, ∀ γ'' ∈ rts, ipL γ γ'' ≠ 0 ∨
      ∃ γ' ∈ rts, ipL γ γ' ≠ 0 ∧ ipL γ' γ'' ≠ 0 := by
  decide +kernel

private theorem j4cReflOrthAll :
    ∀ g ∈ rts, ∃ d ∈ rts, ipL g g = (2 * ipL d g / ipL d d) * ipL d g := by
  decide +kernel

private theorem j4cReflOrthPerp :
    ∀ e ∈ rts, ∀ g ∈ rts, ipL g e = 0 →
      ∃ d ∈ rts, ipL d e = 0 ∧ ipL g g = (2 * ipL d g / ipL d d) * ipL d g := by
  decide +kernel

private theorem j4cReflCorootPair_vec4 (b g : List ℤ) :
    corootPair (vec4 b) (vec4 g) = 2 * ipL b g / ipL b b := by
  unfold corootPair
  rw [iform_F4, iform_F4, ipF4_vec4, ipF4_vec4]

private theorem j4cReflOrth_of_numeric {τ : Tag}
    {γ δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (h : iform γ γ = corootPair δ γ * iform δ γ) : iform (rootReflection δ • γ) γ = 0 := by
  rw [rootReflection_smul hδ, iform_sub_left, iform_smul_left, h, sub_self]

private theorem j4cComponentRoots_eq_rootSet
    {L : Type} [Field L] {a : Fin Tag.F4.rank → Lˣ}
    (hall : ∀ γ, IsRoot Tag.F4 γ → rootChar a γ = 1)
    (i : KernelComponent (rootCharHom a)) :
    componentRoots (rootCharHom a) i = {γ | IsRoot Tag.F4 γ} := by
  have hsingle : ∀ i j : KernelComponent (rootCharHom a), i = j := by
    intro i j
    obtain ⟨α, rfl⟩ := Quotient.exists_rep i
    obtain ⟨β, rfl⟩ := Quotient.exists_rep j
    obtain ⟨lα, hlα, hα⟩ := (mem_rts_iff (α : V4)).1 α.2.1
    obtain ⟨lβ, hlβ, hβ⟩ := (mem_rts_iff (β : V4)).1 β.2.1
    rcases j4cF4HubP_holds lα hlα lβ hlβ with h | ⟨l', hl', h1, h2⟩
    · refine mk_eq_of_iform_ne_zero (α := α) (β := β) ?_
      show iform (α : V4) (β : V4) ≠ 0
      rw [← hα, ← hβ, iform_F4, ipF4_vec4]
      exact h
    · have hγr : IsRoot Tag.F4 (vec4 l') := (mem_rts_iff (vec4 l')).2 ⟨l', hl', rfl⟩
      refine (mk_eq_of_iform_ne_zero (α := α) (β := ⟨vec4 l', hγr, hall _ hγr⟩)
        ?_).trans (mk_eq_of_iform_ne_zero (α := ⟨vec4 l', hγr, hall _ hγr⟩)
          (β := β) ?_)
      · show iform (α : V4) (vec4 l') ≠ 0
        rw [← hα, iform_F4, ipF4_vec4]
        exact h1
      · show iform (vec4 l') (β : V4) ≠ 0
        rw [← hβ, iform_F4, ipF4_vec4]
        exact h2
  have hcomp : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) := by
    ext γ
    exact ⟨fun h => h.1, fun h => ⟨h, hsingle (Quotient.mk _ ⟨γ, h⟩) i⟩⟩
  have hker : kernelRoots (rootCharHom a) = {γ | IsRoot Tag.F4 γ} := by
    ext γ
    exact ⟨fun h => h.1, fun h => ⟨h, hall γ h⟩⟩
  rw [hcomp, hker]

theorem langRatCentralizerDetects_two_F4
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup .F4 L p₀) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot .F4 γ → S.ρ γ = -γ)
    {a b : Fin Tag.F4.rank → Lˣ} (ha : rootDiagUnit .F4 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (hAlg : S.IsAlgebraic)
    (i : KernelComponent (rootCharHom a))
    (hnot : ¬ LangSmallSolv S.D.q S.ρ (rootCharHom a) i)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer {rootDiagUnit .F4 b}) :
    ∀ γ ∈ rationalRoots S.ρ (rootCharHom a) i, rootChar b γ = 1 := by
  have hq' : S.D.q = 2 ^ 1 := by rw [hq, pow_one]
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq'
  have hcomp : ∀ γ ∈ componentRoots (rootCharHom a) i, rootChar b γ = 1 := by
    intro γ hγ
    have hγr : IsRoot Tag.F4 γ := isRoot_of_mem_componentRoots hγ
    obtain ⟨g, hg, rfl⟩ := (mem_rts_iff γ).1 hγr
    obtain ⟨δ, hδ, hnum⟩ : ∃ δ ∈ componentRoots (rootCharHom a) i,
        iform (vec4 g) (vec4 g) = corootPair δ (vec4 g) * iform δ (vec4 g) := by
      rcases langRatDetectsTwoF4_class_cases hap i with hall | ⟨h6, hsame⟩ | ⟨e, he, hcls⟩
      · obtain ⟨d, hd, hd'⟩ := j4cReflOrthAll g hg
        refine ⟨vec4 d, ?_, ?_⟩
        · rw [j4cComponentRoots_eq_rootSet hall i]
          exact (mem_rts_iff _).2 ⟨d, hd, rfl⟩
        · simp only [iform_F4, ipF4_vec4, j4cReflCorootPair_vec4]
          exact hd'
      · exact absurd (langRatDetectsTwoF4_langSmallSolv_of_ncard_six S hq hρ ha i h6 hsame) hnot
      · obtain ⟨l, hl, rfl⟩ := (mem_rts_iff e).1 he
        have hγ' : IsRoot Tag.F4 (vec4 g) ∧ iform (vec4 g) (vec4 l) = 0 := by
          rw [hcls] at hγ
          exact hγ
        have hgl : ipL g l = 0 := by
          have h := hγ'.2
          rwa [iform_F4, ipF4_vec4] at h
        obtain ⟨d, hd, hdl, hd'⟩ := j4cReflOrthPerp l hl g hg hgl
        refine ⟨vec4 d, ?_, ?_⟩
        · rw [hcls]
          exact ⟨(mem_rts_iff _).2 ⟨d, hd, rfl⟩, by rw [iform_F4, ipF4_vec4]; exact hdl⟩
        · simp only [iform_F4, ipF4_vec4, j4cReflCorootPair_vec4]
          exact hd'
    exact langRatKills_of_reflection_commutator S (Or.inl rfl) hq' hAlg b i
      (Ψs := componentRoots (rootCharHom a) i) subset_rfl
      (fun δ hδ => Or.inr (hρ δ (isRoot_of_mem_componentRoots hδ))) hγ
      (Subgroup.subset_closure ⟨δ, hδ, rfl⟩)
      (j4cReflOrth_of_numeric (isRoot_of_mem_componentRoots hδ) hnum) hle
  rintro γ ⟨k, δ, hδ, rfl⟩
  have hδr : IsRoot Tag.F4 δ := isRoot_of_mem_componentRoots hδ
  have hiter : ∀ n : ℕ, (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] δ = δ ∨
      (S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[n] δ = -δ := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]
        exact Or.inr (hρ δ hδr)
      · rw [h, hρ (-δ) (IsRoot.neg hδr), neg_neg]
        exact Or.inl rfl
  rcases hiter k with h | h
  · rw [h]
    exact hcomp δ hδ
  · rw [h, CFSG.ClassicalInvolution.ModelFacts.Levi.rootChar_neg', hcomp δ hδ, inv_one]

end CFSG.StandardType.LangRat

end
