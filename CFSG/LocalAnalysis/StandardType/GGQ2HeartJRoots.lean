module

public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalComponent
public import CFSG.LocalAnalysis.StandardType.GGLangSixRoot
public import CFSG.ClassicalInvolution.RouteD.Root
public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.ClassicalInvolution.RouteD.Basic

public section

namespace CFSG.StandardType.QTwoHeartJ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.LangRat CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem two_mul_compRank_le_ncard
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    2 * compRank Ψ ≤ Ψ.ncard := by
  classical
  let S := simpleRoots Ψ
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
  have hSΨ : (S : Set (Fin τ.rank → ℤ)) ⊆ Ψ := fun β hβ => simpleRoots_subset hβ
  have hnegSΨ : ((S.image Neg.neg : Finset (Fin τ.rank → ℤ)) : Set _) ⊆ Ψ := by
    intro x hx
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hx
    exact hΨ.neg_mem β (hSΨ hβ)
  have hdisj : Disjoint (S : Set (Fin τ.rank → ℤ))
      ((S.image Neg.neg : Finset (Fin τ.rank → ℤ)) : Set _) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨β, hβ, hβx⟩ := Finset.mem_image.1 hx'
    have h1 : 0 < height x := simpleRoots_height_pos hx
    have h2 : height x < 0 := by
      rw [← hβx, height_neg]
      have := simpleRoots_height_pos hβ
      omega
    omega
  have hcard : ((S : Set (Fin τ.rank → ℤ)) ∪
      ((S.image Neg.neg : Finset (Fin τ.rank → ℤ)) : Set _)).ncard = 2 * S.card := by
    rw [Set.ncard_union_eq hdisj (Finset.finite_toSet S)
      (Finset.finite_toSet (S.image Neg.neg)),
      Set.ncard_coe_finset, Set.ncard_coe_finset,
      Finset.card_image_of_injective _ neg_injective]
    omega
  have hle : ((S : Set (Fin τ.rank → ℤ)) ∪
      ((S.image Neg.neg : Finset (Fin τ.rank → ℤ)) : Set _)).ncard ≤ Ψ.ncard := by
    refine Set.ncard_le_ncard ?_ hfin
    rintro x (hx | hx)
    · exact hSΨ hx
    · exact hnegSΨ hx
  have hcomp : compRank Ψ = S.card := (simpleRoots_card_eq_compRank hΨ).symm
  calc 2 * compRank Ψ = 2 * S.card := by rw [hcomp]
    _ = ((S : Set (Fin τ.rank → ℤ)) ∪
        ((S.image Neg.neg : Finset (Fin τ.rank → ℤ)) : Set _)).ncard := hcard.symm
    _ ≤ Ψ.ncard := hle

theorem six_lt_ncard_of_three_le_compRank
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (h3 : 3 ≤ compRank Ψ) : 6 < Ψ.ncard := by
  have h6 : 6 ≤ Ψ.ncard := by
    have := two_mul_compRank_le_ncard hΨ
    omega
  by_contra h
  have hcard : Ψ.ncard = 6 := by omega
  have hc : compRank Ψ = 2 := compRank_eq_two_of_ncard_eq_six hΨ hcard
  omega

private theorem qTwoHeartJRootsAux_reflect_eq (i : Fin 6) (v : Fin 6 → ℤ) :
    CFSG.LieType.RootSystem.reflection (CartanMatrix.E 6) i v =
      CFSG.Blueprint.Chevalley.reflect Tag.E6 i v := by
  rw [CFSG.LieType.RootSystem.reflection_apply, ← cartanE_eq]
  rfl

private theorem qTwoHeartJRootsAux_isRoot_rroot {v : Fin Tag.E6.rank → ℤ}
    (h : IsRoot Tag.E6 v) :
    CFSG.ClassicalInvolution.RouteD.RRoot (CartanMatrix.E 6) (show Fin 6 → ℤ from v) := by
  refine IsRoot.rec (motive := fun w _ =>
    CFSG.ClassicalInvolution.RouteD.RRoot (CartanMatrix.E 6) (show Fin 6 → ℤ from w))
    ?_ ?_ h
  · intro j
    exact CFSG.ClassicalInvolution.RouteD.RRoot.simple (show Fin 6 from j)
  · intro i w _ ih
    exact Eq.mpr (congrArg (fun x =>
      CFSG.ClassicalInvolution.RouteD.RRoot (CartanMatrix.E 6) x)
      (qTwoHeartJRootsAux_reflect_eq (show Fin 6 from i) (show Fin 6 → ℤ from w)).symm)
      (CFSG.ClassicalInvolution.RouteD.RRoot.reflect (A := CartanMatrix.E 6)
        (v := show Fin 6 → ℤ from w) (show Fin 6 from i) ih)

theorem rroot_E6_iff_isRoot {v : Fin 6 → ℤ} :
    CFSG.ClassicalInvolution.RouteD.RRoot (CartanMatrix.E 6) v ↔ IsRoot Tag.E6 v := by
  constructor
  · intro h
    induction h with
    | simple i => exact IsRoot.basis (τ := Tag.E6) i
    | @reflect i v _ ih =>
      rw [qTwoHeartJRootsAux_reflect_eq]
      exact IsRoot.reflect (τ := Tag.E6) i ih
  · intro h
    exact qTwoHeartJRootsAux_isRoot_rroot (v := show Fin Tag.E6.rank → ℤ from v) h

theorem three_le_compRank_of_quasisimple
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1)
    (i : KernelComponent (rootCharHom a))
    (hQ : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  classical
  let Ψ := componentRoots (rootCharHom a) i
  let J := rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hd3 : rootDiagUnit τ a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have ha : a ^ 3 = 1 := funext fun j => by simpa using ha3 j
    rw [ha, rootDiagUnit_one]
  have : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
  have h3L : (3 : L) ≠ 0 := by
    have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have h3L' : (3 : L) = 1 := by
      have h3 : (3 : L) = (2 : L) + 1 := by norm_num
      rw [h3, h2L, zero_add]
    rw [h3L']
    exact one_ne_zero
  have hq1 : S.D.q = 2 ^ 1 := by rw [hq]; norm_num
  have hρ' : ∀ γ, IsRoot τ γ → S.ρ γ = (-1 : ℤ) • latPerm 1 γ := by
    intro γ hγ
    rw [hρ γ hγ]
    exact (neg_one_smul ℤ (latPerm 1 γ)).symm
  have hΨne : Ψ.Nonempty := by
    by_contra hne
    have hEmpty : Ψ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hrootEmpty : rationalRoots S.ρ (rootCharHom a) i = ∅ := by
      rw [rationalRoots_eq_of_rho_neg S hρ i]
      simpa [Ψ] using hEmpty
    have hspan : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
    have hJbot : J = ⊥ := by
      simp [J, rationalComponent, rationalSpan, hrootEmpty, hspan]
    have hsub : Subsingleton ↥J := by
      rw [hJbot]
      infer_instance
    exact (not_subsingleton_iff_nontrivial.mpr
      (CFSG.LocalCores.isQuasisimple_nontrivial hQ)) hsub
  have hrankpos : 1 ≤ compRank Ψ := by
    have hspan_ne : Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) ≠ ⊥ := by
      intro hbot
      obtain ⟨α, hα⟩ := hΨne
      have hmem : (fun i => (α i : ℚ)) ∈
          Submodule.span ℚ ((fun γ (i : Fin τ.rank) => (γ i : ℚ)) '' Ψ) :=
        Submodule.subset_span ⟨α, hα, rfl⟩
      rw [hbot] at hmem
      have hzero : α = 0 := by
        ext j
        have hfun : (fun i => (α i : ℚ)) = 0 := by simpa using hmem
        have := congrFun hfun j
        have h0 : (α j : ℚ) = 0 := by simpa using this
        exact_mod_cast h0
      exact (hΨ.isRoot α hα).ne_zero hzero
    rw [compRank]
    exact (Submodule.one_le_finrank_iff).2 hspan_ne
  by_cases h3 : 3 ≤ compRank Ψ
  · exact h3
  · have hrle : compRank Ψ ≤ 2 := by omega
    have hsl : SimplyLacedTag τ := by
      rcases hτ with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases (show compRank Ψ = 1 ∨ compRank Ψ = 2 by omega) with hr1 | hr2
    · have hncard : Ψ.ncard = 2 := j4d_rank_one_ncard hsl hΨ hr1
      obtain ⟨α, hα⟩ := hΨne
      have hαroot : IsRoot τ α := hΨ.isRoot α hα
      have hpair : Ψ = {α, -α} := by
        have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
          intro x hx
          rcases hx with rfl | rfl
          · exact hα
          · exact hΨ.neg_mem α hα
        have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := by
          rw [Set.ncard_pair]
          intro h
          apply hαroot.ne_zero
          ext j
          have := congrFun h j
          simp only [Pi.neg_apply] at this
          change α j = (0 : ℤ)
          omega
        have hfinΨ : Ψ.Finite :=
          (finite_setOf_isRoot τ).subset fun γ hγ => hΨ.isRoot γ hγ
        exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hncard, hcard]) hfinΨ).symm
      have hsolv : Group.IsSolvable ↥J :=
        isSolvable_rationalComponent_of_latSolv S hq1 Nat.prime_three h3L (Equiv.refl _) (-1)
          (Or.inr rfl) (by rw [hq]; norm_num) hρ' hT ha3 i
          ⟨rfl, Or.inl ⟨α, by rw [rationalRoots_eq_of_rho_neg S hρ i]; exact hpair⟩⟩
      have : Group.IsPerfect ↥J := hQ.1
      exfalso
      exact (Group.IsPerfect.not_isSolvable (G := ↥J)) hsolv
    · have hncard : Ψ.ncard = 6 := j4d_rank_two_ncard hsl hΨ hr2
      have hsolv : Group.IsSolvable ↥J :=
        isSolvable_rationalComponent_of_latSolv S hq1 Nat.prime_three h3L (Equiv.refl _) (-1)
          (Or.inr rfl) (by rw [hq]; norm_num) hρ' hT ha3 i
          ⟨rfl, Or.inr ⟨by rw [rationalRoots_eq_of_rho_neg S hρ i]; exact hncard, by
            intro α _
            rfl⟩⟩
      have : Group.IsPerfect ↥J := hQ.1
      exfalso
      exact (Group.IsPerfect.not_isSolvable (G := ↥J)) hsolv

end CFSG.StandardType.QTwoHeartJ

end
