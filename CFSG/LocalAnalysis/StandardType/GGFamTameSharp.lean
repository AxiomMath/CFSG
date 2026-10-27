module

public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem compRank_eq_one_of_rank_one
    {τ : Tag} {M : Type} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (hrank : ∀ α ∈ componentRoots χ i, ∀ δ ∈ componentRoots χ i, δ = α ∨ δ = -α) :
    compRank (componentRoots χ i) = 1 := by
  classical
  obtain ⟨a, ha⟩ := Quotient.exists_rep i
  have hα : a.1 ∈ componentRoots χ i := ⟨a.2, ha⟩
  have hnegα : -a.1 ∈ componentRoots χ i :=
    (isRootComponent_componentRoots (χ := χ) i).neg_mem a.1 hα
  have hset : componentRoots χ i = ({a.1, -a.1} : Set (Fin τ.rank → ℤ)) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro δ hδ
      rcases hrank a.1 hα δ hδ with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro δ hδ
      rcases hδ with rfl | rfl
      · exact hα
      · exact hnegα
  rw [hset]
  set v : Fin τ.rank → ℚ := fun j => (a.1 j : ℚ) with hv
  have hv0 : v ≠ 0 := by
    intro h
    apply a.2.1.ne_zero
    funext j
    have hj : (a.1 j : ℚ) = 0 := by simpa [v] using congrFun h j
    exact_mod_cast hj
  have hneg : (fun j => (((-a.1) j : ℤ) : ℚ)) = -v := by
    ext j
    simp [v, Pi.neg_apply]
  have himg : (fun γ : Fin τ.rank → ℤ => fun j => (γ j : ℚ)) '' ({a.1, -a.1} : Set _) =
      ({v, -v} : Set (Fin τ.rank → ℚ)) := by
    rw [Set.image_pair, hneg, ← hv]
  have hspan : Submodule.span ℚ ({v, -v} : Set (Fin τ.rank → ℚ)) =
      Submodule.span ℚ ({v} : Set (Fin τ.rank → ℚ)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact Submodule.subset_span (Set.mem_singleton v)
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton v))
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Submodule.subset_span (Set.mem_insert v _)
  simp only [compRank]
  rw [himg, hspan]
  exact finrank_span_singleton hv0

private theorem twistKindM_suN_rank_ncard {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    {i : KernelComponent χ} (h : twistKindM ρ χ i = .suN) :
    2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard =
        compRank (componentRoots χ i) * (compRank (componentRoots χ i) + 1) := by
  unfold twistKindM at h
  split_ifs at h with h1 h2 h3 h4
  exact h4

theorem isQuasisimple_rationalComponentM_of_lambda2
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type}
    {a : ι → Fin τ.rank → Lˣ} (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a)) {n : ℕ}
    (hn : 2 ^ n = S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i))
    (hΛ : CFSG.Assembly.LargeEvenInLambda2 (componentLabel (compRank (componentRoots (famCharHom a) i))
      (componentRoots (famCharHom a) i).ncard (twistKindOf S.ρ (componentRoots (famCharHom a) i))
      n)) :
    CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
  classical
  cases hk : twistKindM S.ρ (famCharHom a) i with
  | inner =>
    by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)
    · exact langFamTame_inner_isQuasisimple hτ S hp hT hap h1 i hk (Or.inl hQ)
    · by_cases hrank : ∀ α ∈ componentRoots (famCharHom a) i,
          ∀ δ ∈ componentRoots (famCharHom a) i, δ = α ∨ δ = -α
      · exfalso
        have hrc : compRank (componentRoots (famCharHom a) i) = 1 :=
          compRank_eq_one_of_rank_one (famCharHom a) i hrank
        have hnc : (componentRoots (famCharHom a) i).ncard = 2 :=
          CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ncard_componentRoots_eq_two_of_rank_one
            (famCharHom a) i hrank
        have hkind : twistKindOf S.ρ (componentRoots (famCharHom a) i) = .inner := hk
        have hlabel : componentLabel (compRank (componentRoots (famCharHom a) i))
            (componentRoots (famCharHom a) i).ncard
            (twistKindOf S.ρ (componentRoots (famCharHom a) i)) n = ⟨.A, 1, n⟩ := by
          rw [hrc, hnc, hkind]
          simp [componentLabel]
        rw [hlabel] at hΛ
        dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hΛ
        have h2n : 2 ≤ n := hΛ.2.2 (by trivial)
        have hQlt : S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) < 4 :=
          not_le.1 hQ
        have hnlt : n < 2 := by
          have h2 : 2 ^ n < 2 ^ 2 := by
            rw [hn]
            simpa using hQlt
          exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h2
        omega
      · exact langFamTame_inner_isQuasisimple hτ S hp hT hap h1 i hk (Or.inr hrank)
  | suN =>
    refine langFamTame_suN_isQuasisimple hτ S hp hp2 hT hap h1 i hk ?_
    by_cases hq2 : S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 2
    · right
      intro hn6
      have hsuN := twistKindM_suN_rank_ncard S.ρ hk
      have hr2 : compRank (componentRoots (famCharHom a) i) = 2 := by
        have hN := hsuN.2
        rw [hn6] at hN
        have h2r := hsuN.1
        have hrle : compRank (componentRoots (famCharHom a) i) ≤ 2 := by
          by_contra h
          have h3 : 3 ≤ compRank (componentRoots (famCharHom a) i) := by omega
          have hge : 12 ≤ compRank (componentRoots (famCharHom a) i) *
              (compRank (componentRoots (famCharHom a) i) + 1) := by
            calc 12 = 3 * (3 + 1) := by norm_num
              _ ≤ compRank (componentRoots (famCharHom a) i) *
                  (compRank (componentRoots (famCharHom a) i) + 1) :=
                Nat.mul_le_mul h3 (Nat.succ_le_succ h3)
          omega
        omega
      have hkind : twistKindOf S.ρ (componentRoots (famCharHom a) i) = .suN := hk
      have hlabel : componentLabel (compRank (componentRoots (famCharHom a) i))
          (componentRoots (famCharHom a) i).ncard
          (twistKindOf S.ρ (componentRoots (famCharHom a) i)) n = ⟨.twA, 2, n⟩ := by
        rw [hr2, hkind]
        rfl
      rw [hlabel] at hΛ
      dsimp only [CFSG.Assembly.LargeEvenInLambda2] at hΛ
      have h2n : 2 ≤ n := hΛ.2.2 (by trivial)
      have hn1 : n = 1 := by
        have h : 2 ^ n = 2 ^ 1 := by rw [hn, hq2, pow_one]
        exact Nat.pow_right_injective (le_refl 2) h
      omega
    · exact Or.inl hq2
  | twoD =>
    obtain ⟨hnin, h4, hcard⟩ := twistKindM_twoD_unpack S.ρ hk
    by_cases h5 : 5 ≤ compRank (componentRoots (famCharHom a) i)
    · exact langFamTame_twoD_high hτ S hp hp2 hT hap h1 i hk h5
    · have hr : compRank (componentRoots (famCharHom a) i) = 4 := by omega
      have hc : (componentRoots (famCharHom a) i).ncard = 24 := by rw [hcard, hr]
      exact langFamTame_twoD_four hτ S hp hp2 hT hap h1 i hr hc hnin
  | exc => exact langFamTame_exc hτ S hp hp2 hT hap h1 i hk

end CFSG.StandardType.TableCRes
