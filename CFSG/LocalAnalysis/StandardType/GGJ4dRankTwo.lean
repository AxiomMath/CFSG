module

public import CFSG.LocalAnalysis.StandardType.GGJ4dSimpleRank
public import CFSG.LocalAnalysis.StandardType.GGJ4dComponentWeyl

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d

private def a2Roots {τ : Tag} (α β : Fin τ.rank → ℤ) : Finset (Fin τ.rank → ℤ) :=
  ({α, β, α + β} : Finset (Fin τ.rank → ℤ)) ∪ {-α, -β, -(α + β)}

private theorem mem_a2Roots {τ : Tag} (α β x : Fin τ.rank → ℤ) :
    x ∈ a2Roots α β ↔
      x = α ∨ x = β ∨ x = α + β ∨ x = -α ∨ x = -β ∨ x = -(α + β) := by
  simp only [a2Roots, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem j4d_rank_two_ncard
    {τ : Tag} (hτ : SimplyLacedTag τ) {Ψ : Set (Fin τ.rank → ℤ)}
    (hΨ : IsRootComponent Ψ) (hrank : compRank Ψ = 2) :
    Ψ.ncard = 6 := by
  classical
  have hcard : (simpleRoots Ψ).card = 2 := by
    rw [simpleRoots_card_eq_compRank hΨ, hrank]
  obtain ⟨α, β, hne, hΔ⟩ := Finset.card_eq_two.mp hcard
  have hα : α ∈ simpleRoots Ψ := by rw [hΔ]; exact Finset.mem_insert_self _ _
  have hβ : β ∈ simpleRoots Ψ := by
    rw [hΔ]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hαr : IsRoot τ α := simpleRoots_isRoot hα
  have hβr : IsRoot τ β := simpleRoots_isRoot hβ
  have hαα : iform α α = 2 := iform_self_eq_two_of_simplyLaced' hτ hαr
  have hββ : iform β β = 2 := iform_self_eq_two_of_simplyLaced' hτ hβr
  have hposα : 0 < height α := simpleRoots_height_pos hα
  have hposβ : 0 < height β := simpleRoots_height_pos hβ
  have hSimple : SimpleAdj Ψ α β := by
    by_contra hns
    have hstay : ∀ γ, Relation.ReflTransGen (SimpleAdj Ψ) α γ → γ = α := by
      intro γ hγ
      induction hγ with
      | refl => rfl
      | tail _ hstep ih =>
        rw [ih] at hstep
        have hlast := hstep.2.1
        rw [hΔ] at hlast
        simp only [Finset.mem_insert, Finset.mem_singleton] at hlast
        rcases hlast with hc | hc
        · exact hc
        · exact absurd (hc ▸ hstep) hns
    exact hne (hstay β (simpleRoots_connected hΨ hα hβ)).symm
  have hpair_le : iform α β ≤ 0 := iform_simpleRoots_nonpos hΨ hα hβ hne
  have hpair_ne : iform α β ≠ 0 := hSimple.2.2
  have hpair_neg : iform α β < 0 := lt_of_le_of_ne hpair_le hpair_ne
  have hne_neg : α ≠ -β := by
    intro h
    rw [h, height_neg] at hposα
    omega
  have hsq := iform_sq_lt hαr hβr hne hne_neg
  rw [hαα, hββ] at hsq
  have hle_one : iform α β ≤ 1 := by nlinarith
  have hge_one : -1 ≤ iform α β := by nlinarith
  have hpair : iform α β = -1 := by omega
  have hpair' : iform β α = -1 := by rw [iform_comm β α, hpair]
  have hcorα : corootPair α β = -1 := by
    rw [corootPair_eq_iform hτ hαr β, hpair]
  have hcorβ : corootPair β α = -1 := by
    rw [corootPair_eq_iform hτ hβr α, hpair']
  have hραα : rootReflection α • α = -α := rootReflection_smul_self hαr
  have hρββ : rootReflection β • β = -β := rootReflection_smul_self hβr
  have hραβ : rootReflection α • β = α + β := by
    rw [rootReflection_smul hαr β, hcorα, neg_one_smul]
    abel
  have hρβα : rootReflection β • α = α + β := by
    rw [rootReflection_smul hβr α, hcorβ, neg_one_smul]
    abel
  have hραadd : rootReflection α • (α + β) = β := by
    rw [smul_add, hραα, hραβ]
    abel
  have hρβαdd : rootReflection β • (α + β) = α := by
    rw [smul_add, hρβα, hρββ]
    abel
  have hραnegα : rootReflection α • (-α) = α := by rw [smul_neg, hραα, neg_neg]
  have hραnegβ : rootReflection α • (-β) = -(α + β) := by rw [smul_neg, hραβ]
  have hραnegadd : rootReflection α • (-(α + β)) = -β := by
    rw [smul_neg, hραadd]
  have hρβnegα : rootReflection β • (-α) = -(α + β) := by rw [smul_neg, hρβα]
  have hρβnegβ : rootReflection β • (-β) = β := by rw [smul_neg, hρββ, neg_neg]
  have hρβnegadd : rootReflection β • (-(α + β)) = -α := by
    rw [smul_neg, hρβαdd]
  have hαΨ : α ∈ Ψ := simpleRoots_subset hα
  have hβΨ : β ∈ Ψ := simpleRoots_subset hβ
  have hαβΨ : α + β ∈ Ψ :=
    hΨ.add_mem α hαΨ β hβΨ (isRoot_add_of_iform_neg hαr hβr hne_neg (by omega))
  have hSΨ : (a2Roots α β : Set (Fin τ.rank → ℤ)) ⊆ Ψ := by
    intro x hx
    rw [Finset.mem_coe, mem_a2Roots] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hαΨ
    · exact hβΨ
    · exact hαβΨ
    · exact hΨ.neg_mem α hαΨ
    · exact hΨ.neg_mem β hβΨ
    · exact hΨ.neg_mem (α + β) hαβΨ
  have hSinv : ∀ δ ∈ simpleRoots Ψ, ∀ x ∈ (a2Roots α β : Set (Fin τ.rank → ℤ)),
      rootReflection δ • x ∈ (a2Roots α β : Set (Fin τ.rank → ℤ)) := by
    intro δ hδ x hx
    rw [Finset.mem_coe, mem_a2Roots] at hx ⊢
    have hδ' : δ = α ∨ δ = β := by
      have h := hδ
      rw [hΔ] at h
      simpa using h
    rcases hδ' with rfl | rfl
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hραα, hραβ, hραadd, hραnegα, hραnegβ, hραnegadd]
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hρβα, hρββ, hρβαdd, hρβnegα, hρβnegβ, hρβnegadd]
  have hΨS : Ψ ⊆ (a2Roots α β : Set (Fin τ.rank → ℤ)) := by
    intro x hx
    obtain ⟨w, hw, δ, hδ, rfl⟩ := exists_smul_simpleRoot hΨ hx
    have hδ' : δ = α ∨ δ = β := by
      have h := hδ
      rw [hΔ] at h
      simpa using h
    have hδS : δ ∈ (a2Roots α β : Set (Fin τ.rank → ℤ)) := by
      rw [Finset.mem_coe, mem_a2Roots]
      rcases hδ' with hδα | hδβ
      · exact Or.inl hδα
      · exact Or.inr (Or.inl hδβ)
    exact smul_mem_of_forall_rootReflection hΨ hSΨ hSinv hw δ hδS
  have hset : Ψ = (a2Roots α β : Set (Fin τ.rank → ℤ)) := le_antisymm hΨS hSΨ
  have hαneadd : α ≠ α + β := by
    intro h
    have := congrArg height h
    rw [height_add] at this
    omega
  have hβneadd : β ≠ α + β := by
    intro h
    have := congrArg height h
    rw [height_add] at this
    omega
  have hP : ({α, β, α + β} : Finset (Fin τ.rank → ℤ)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨α, β, α + β, hne, hαneadd, hβneadd, rfl⟩
  have hnegαβ : -α ≠ -β := by
    intro h
    exact hne (by simpa using congrArg (fun v => -v) h)
  have hnegαadd : -α ≠ -(α + β) := by
    intro h
    exact hαneadd (by simpa using congrArg (fun v => -v) h)
  have hnegβadd : -β ≠ -(α + β) := by
    intro h
    exact hβneadd (by simpa using congrArg (fun v => -v) h)
  have hN : ({-α, -β, -(α + β)} : Finset (Fin τ.rank → ℤ)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨-α, -β, -(α + β), hnegαβ, hnegαadd, hnegβadd, rfl⟩
  have hdisj : Disjoint ({α, β, α + β} : Finset (Fin τ.rank → ℤ)) {-α, -β, -(α + β)} := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    have hxpos : 0 < height x := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hposα
      · exact hposβ
      · rw [height_add]
        exact add_pos hposα hposβ
    have hyneg : height y < 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · rw [height_neg]
        omega
      · rw [height_neg]
        omega
      · rw [height_neg, height_add]
        omega
    rw [hxy] at hxpos
    omega
  have hcount : (a2Roots α β).card = 6 := by
    rw [a2Roots, Finset.card_union_of_disjoint hdisj, hP, hN]
  rw [hset, Set.ncard_coe_finset]
  exact hcount

end CFSG.StandardType.LangRat

end
