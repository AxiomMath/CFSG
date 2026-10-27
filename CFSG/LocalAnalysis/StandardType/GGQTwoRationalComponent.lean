module

public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.LocalAnalysis.StandardType.GGLangLatSolv
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankOne
public import CFSG.LocalAnalysis.StandardType.GGJ4dRankTwo
public import CFSG.LocalAnalysis.StandardType.GGJ4dSimpleRank
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.StandardType.QTwoCav

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootTorus CFSG.StandardType.LangRat
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement MatrixGroups


theorem three_le_rank_of_quasisimple_component
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQ : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    3 ≤ compRank (componentRoots (rootCharHom a) i) := by
  classical
  let Ψ := componentRoots (rootCharHom a) i
  let J := rationalComponent S.ρ S.Γ (rootCharHom a) i
  have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots (χ := rootCharHom a) i
  have hd3 : rootDiagUnit τ a ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have ha : a ^ 3 = 1 := funext fun j => by simpa using ha3 j
    rw [ha, rootDiagUnit_one]
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by rw [hq]; norm_num)
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
  have hJnt : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hQ
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
    exact (not_subsingleton ↥J) hsub
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
        have hfinΨ : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
        exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hncard, hcard]) hfinΨ).symm
      have hsolv : Group.IsSolvable ↥J :=
        isSolvable_rationalComponent_of_latSolv S hq1 Nat.prime_three h3L (Equiv.refl _) (-1)
          (Or.inr rfl) (by rw [hq]; norm_num) hρ' hT ha3 i
          ⟨rfl, Or.inl ⟨α, by rw [rationalRoots_eq_of_rho_neg S hρ i]; exact hpair⟩⟩
      haveI : Group.IsPerfect ↥J := hQ.1
      exfalso
      exact (Group.IsPerfect.not_isSolvable (G := ↥J)) hsolv
    · have hncard : Ψ.ncard = 6 := j4d_rank_two_ncard hsl hΨ hr2
      have hsolv : Group.IsSolvable ↥J :=
        isSolvable_rationalComponent_of_latSolv S hq1 Nat.prime_three h3L (Equiv.refl _) (-1)
          (Or.inr rfl) (by rw [hq]; norm_num) hρ' hT ha3 i
          ⟨rfl, Or.inr ⟨by rw [rationalRoots_eq_of_rho_neg S hρ i]; exact hncard, by
            intro α _
            rfl⟩⟩
      haveI : Group.IsPerfect ↥J := hQ.1
      exfalso
      exact (Group.IsPerfect.not_isSolvable (G := ↥J)) hsolv

theorem four_dvd_aut_of_quasisimple_component
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = -γ) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (ha3 : ∀ i, a i ^ 3 = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hQ : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    4 ∣ Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
      (fullThreeTorus S)) := by
  have h3 := three_le_rank_of_quasisimple_component S hτ hq hAlg hρ hT ha3 h1 i hQ
  exact four_dvd_aut_of_component_of_rank_three_le S hτ hq hAlg hρ
    (by rw [rootDiagUnit_pow, show a ^ 3 = 1 from funext ha3, rootDiagUnit_one]) i h3

end CFSG.StandardType.QTwoCav

end
