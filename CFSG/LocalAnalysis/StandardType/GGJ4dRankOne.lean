module

public import CFSG.LocalAnalysis.StandardType.GGJ4dSimpleRank
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem j4d_rank_one_ncard
    {τ : Tag} (hτ : SimplyLacedTag τ) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hrank : compRank Ψ = 1) :
    Ψ.ncard = 2 := by
  classical
  have hcard : (simpleRoots Ψ).card = 1 := by
    rw [simpleRoots_card_eq_compRank hΨ, hrank]
  obtain ⟨α, hΔ⟩ := Finset.card_eq_one.mp hcard
  have hα : α ∈ simpleRoots Ψ := by
    rw [hΔ]
    exact Finset.mem_singleton_self α
  have hαroot : IsRoot τ α := simpleRoots_isRoot hα
  have hαΨ : α ∈ Ψ := simpleRoots_subset hα
  have hαα : iform α α = 2 :=
    CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hαroot
  have hα0 : α ≠ 0 := hαroot.ne_zero
  have hαne : α ≠ -α := by
    intro h
    apply hα0
    funext i
    have hi := congrFun h i
    simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
    omega
  let f : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun γ i => (γ i : ℚ)
  have hfinj : Function.Injective f := by
    intro x y h
    funext i
    exact Int.cast_injective (congrFun h i)
  let S : Submodule ℚ (Fin τ.rank → ℚ) := Submodule.span ℚ (f '' Ψ)
  have hS : Module.finrank ℚ S = 1 := by
    simpa [compRank, S, f] using hrank
  have hαS : f α ∈ S := Submodule.subset_span ⟨α, hαΨ, rfl⟩
  have hαne' : f α ≠ 0 := by
    intro h
    apply hα0
    funext i
    simpa [f] using congrFun h i
  let T : Submodule ℚ (Fin τ.rank → ℚ) := Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ))
  have hTle : T ≤ S := by
    change Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ)) ≤ S
    rw [Submodule.span_le]
    rintro x rfl
    exact hαS
  have hTfin : Module.finrank ℚ T = 1 := by
    change Module.finrank ℚ (Submodule.span ℚ ({f α} : Set (Fin τ.rank → ℚ))) = 1
    exact finrank_span_singleton hαne'
  have hT_eq : T = S := Submodule.eq_of_le_of_finrank_eq hTle (by rw [hTfin, hS])
  have hmem : ∀ β ∈ Ψ, β = α ∨ β = -α := by
    intro β hβΨ
    have hβroot : IsRoot τ β := hΨ.isRoot β hβΨ
    have hββ : iform β β = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two hτ hβroot
    have hβS : f β ∈ S := Submodule.subset_span ⟨β, hβΨ, rfl⟩
    have hβT : f β ∈ T := by
      rw [hT_eq]
      exact hβS
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hβT
    let p : ℤ := c.num
    let q : ℤ := c.den
    have hq0 : (q : ℚ) ≠ 0 := by
      dsimp [q]
      exact_mod_cast c.den_ne_zero
    have hcq : c = (p : ℚ) / (q : ℚ) := by
      dsimp [p, q]
      push_cast
      exact (Rat.num_div_den c).symm
    have hcq' : ((p : ℚ) / (q : ℚ)) • f α = f β := by
      rw [← hcq]
      exact hc
    have hmul : (p : ℚ) • f α = (q : ℚ) • f β := by
      have h := congrArg (fun v => (q : ℚ) • v) hcq'
      rw [smul_smul, mul_div_cancel₀ (p : ℚ) hq0] at h
      exact h
    have hEqf : f (p • α) = f (q • β) := by
      funext i
      have hi := congrFun hmul i
      simp only [f, Pi.smul_apply, smul_eq_mul] at hi ⊢
      push_cast at hi ⊢
      exact hi
    have hZ : p • α = q • β := by
      funext i
      have hi := congrFun hEqf i
      simp only [f, Pi.smul_apply, smul_eq_mul] at hi ⊢
      exact_mod_cast hi
    have hnorm : q ^ 2 = p ^ 2 := by
      have h1 : iform (q • β) (q • β) = iform (p • α) (p • α) := by rw [hZ]
      rw [iform_smul_left, iform_smul_right, iform_smul_left, iform_smul_right,
        hββ, hαα] at h1
      nlinarith
    have hpq : p = q ∨ p = -q :=
      eq_or_eq_neg_of_sq_eq_sq p q (by rw [hnorm])
    have hc1 : c = 1 ∨ c = -1 := by
      rcases hpq with h | h
      · left
        rw [hcq, h]
        exact div_self hq0
      · right
        rw [hcq, h]
        push_cast
        exact neg_div_self hq0
    have hfβ : f β = c • f α := hc.symm
    rcases hc1 with rfl | rfl
    · left
      exact hfinj (by simpa using hfβ)
    · right
      exact hfinj (by
        rw [hfβ]
        funext i
        simp [f])
  have hset : Ψ = ({α, -α} : Set (Fin τ.rank → ℤ)) := by
    apply Set.Subset.antisymm
    · intro β hβ
      rcases hmem β hβ with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
    · intro β hβ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hβ
      rcases hβ with rfl | rfl
      · exact hαΨ
      · exact hΨ.neg_mem α hαΨ
  rw [hset, Set.ncard_pair hαne]

end CFSG.StandardType.LangRat

end
