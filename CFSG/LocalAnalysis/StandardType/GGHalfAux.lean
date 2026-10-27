module

public import CFSG.LocalAnalysis.StandardType.GGHalfSlOn
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem exists_mem_ne_of_three {N : ℕ} {S : Set (Fin N)} {a b : Fin N}
    (h : ∃ a₀ b₀ c₀ : Fin N,
      a₀ ∈ S ∧ b₀ ∈ S ∧ c₀ ∈ S ∧ a₀ ≠ b₀ ∧ a₀ ≠ c₀ ∧ b₀ ≠ c₀) :
    ∃ d, d ∈ S ∧ d ≠ a ∧ d ≠ b := by
  obtain ⟨a₀, b₀, c₀, ha₀, hb₀, hc₀, hab₀, hac₀, hbc₀⟩ := h
  by_cases h0 : a₀ = a ∨ a₀ = b
  · by_cases h1 : b₀ = a ∨ b₀ = b
    · by_cases h2 : c₀ = a ∨ c₀ = b
      · exfalso
        rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        all_goals first
          | exact hab₀ (h0.trans h1.symm)
          | exact hac₀ (h0.trans h2.symm)
          | exact hbc₀ (h1.trans h2.symm)
      · exact ⟨c₀, hc₀, fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
    · exact ⟨b₀, hb₀, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
  · exact ⟨a₀, ha₀, fun h => h0 (Or.inl h), fun h => h0 (Or.inr h)⟩

theorem omegaBlock_mem_slOn {n : ℕ} (k : Fin n) {S : Set (Fin (n + 1))} (h1 : k.castSucc ∈ S)
    (h2 : k.succ ∈ S) : omegaBlock n k ∈ slOn (n + 1) S := by
  rw [omegaBlock, weylRep]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · exact transvection_mem_slOn _ 1 h1 h2
  · exact transvection_mem_slOn _ (-1) h2 h1
  · exact transvection_mem_slOn _ 1 h1 h2
  · exact transvection_mem_slOn _ 1 h1 h2

theorem slOn_perfect {N : ℕ} {S : Set (Fin N)}
    (hS : ∃ a b c : Fin N, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    slOn N S ≤ ⁅slOn N S, slOn N S⁆ := by
  rw [slOn, Subgroup.closure_le]
  rintro t ⟨a, b, hab, c, ha, hb, rfl⟩
  obtain ⟨d, hdS, hda, hdb⟩ := exists_mem_ne_of_three hS
  have h1 : SpecialLinearGroup.transvection hda.symm c ∈ slOn N S :=
    transvection_mem_slOn hda.symm c ha hdS
  have h2 : SpecialLinearGroup.transvection hdb 1 ∈ slOn N S :=
    transvection_mem_slOn hdb 1 hdS hb
  have hmem := Subgroup.commutator_mem_commutator h1 h2
  have hkey :=
    Matrix.SpecialLinearGroup.commutatorElement_transvection hda.symm hdb hab c (1 : F2)
  rw [hkey, mul_one] at hmem
  exact hmem

theorem exists_mulAut_of_range_eq {S G : Type*} [Group S] [Group G] {ψ ψ' : S →* G}
    (hψ : Function.Injective ψ) (hψ' : Function.Injective ψ') (h : ψ.range = ψ'.range) :
    ∃ α : MulAut S, ∀ s, ψ' (α s) = ψ s := by
  let e : S ≃* ψ.range := MonoidHom.ofInjective hψ
  let e' : S ≃* ψ'.range := MonoidHom.ofInjective hψ'
  let c : ψ.range ≃* ψ'.range := MulEquiv.subgroupCongr h
  refine ⟨e.trans (c.trans e'.symm), fun s => ?_⟩
  have hα : (e.trans (c.trans e'.symm)) s = e'.symm (c (e s)) := rfl
  rw [hα, ← MonoidHom.ofInjective_apply hψ' (x := e'.symm (c (e s)))]
  rw [MulEquiv.apply_symm_apply, MulEquiv.subgroupCongr_apply]
  exact MonoidHom.ofInjective_apply hψ (x := s)

end CFSG.StandardType.GGHalf

end
