module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.G11

theorem g10Four_zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem g10Four_add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v]
  have : (2 : ZMod 2) = 0 := by decide
  rw [this, zero_smul]

@[expose] def g10FourRestrict (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hK : Invariant K U) (k : K) : U ≃ₗ[ZMod 2] U where
  toFun u := ⟨k.1 u, hK k.1 k.2 u u.2⟩
  invFun u := ⟨k.1⁻¹ u, hK k.1⁻¹ (K.inv_mem k.2) u u.2⟩
  map_add' u w := Subtype.ext (map_add k.1 _ _)
  map_smul' c u := Subtype.ext (map_smul k.1 _ _)
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

omit [Finite V] in
@[simp] theorem g10FourRestrict_apply (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hK : Invariant K U) (k : K) (u : U) :
    ((g10FourRestrict K U hK k u : U) : V) = k.1 (u : V) := rfl

theorem g10Four_finrank_ker_ge (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (g : U →ₗ[ZMod 2] ZMod 2) :
    Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (LinearMap.ker g) + 1 := by
  by_cases hg : g = 0
  · rw [hg, LinearMap.ker_zero]
    simp
  · obtain ⟨u₀, hu₀⟩ : ∃ u₀, g u₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hg (LinearMap.ext hcon)
    have hu₁ : g u₀ = 1 := by
      rcases g10Four_zmod_two_cases (g u₀) with h0 | h0
      · exact absurd h0 hu₀
      · exact h0
    have hsup : LinearMap.ker g ⊔ Submodule.span (ZMod 2) {u₀} = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases g10Four_zmod_two_cases (g u) with h0 | h0
      · exact Submodule.mem_sup_left (LinearMap.mem_ker.2 h0)
      · have hk : u - u₀ ∈ LinearMap.ker g := by
          rw [LinearMap.mem_ker, map_sub, h0, hu₁]
          exact sub_self _
        have : u = (u - u₀) + u₀ := by abel
        rw [this]
        exact Submodule.add_mem_sup hk (Submodule.mem_span_singleton_self u₀)
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.ker g)
      (Submodule.span (ZMod 2) {u₀})
    rw [hsup, finrank_top] at h1
    have hne : u₀ ≠ 0 := fun h => hu₀ (by simp [h])
    have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u₀}) = 1 :=
      finrank_span_singleton hne
    omega

theorem g10Four_exists_two_ne_zero (M : Submodule (ZMod 2) V)
    (hM : 2 ≤ Module.finrank (ZMod 2) M) : ∃ a ∈ M, ∃ b ∈ M, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b := by
  by_contra hcon
  push Not at hcon
  have : Module.finrank (ZMod 2) M ≤ 1 := by
    rw [finrank_le_one_iff]
    by_cases hall : ∀ m : M, m = 0
    · exact ⟨0, fun w => ⟨0, by simp [hall w]⟩⟩
    · push Not at hall
      obtain ⟨m, hm⟩ := hall
      refine ⟨m, fun w => ?_⟩
      by_cases hw : w = 0
      · exact ⟨0, by simp [hw]⟩
      · refine ⟨1, ?_⟩
        have := hcon m.1 m.2 w.1 w.2 (fun h => hm (Subtype.ext h))
          (fun h => hw (Subtype.ext h))
        simp only [one_smul]
        exact Subtype.ext this
  omega

theorem g10Four_eq_of_finrank_le_one (M : Submodule (ZMod 2) V)
    (hM : Module.finrank (ZMod 2) M ≤ 1) {a b : V} (ha : a ∈ M) (hb : b ∈ M) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) : a = b := by
  rw [finrank_le_one_iff] at hM
  obtain ⟨v, hv⟩ := hM
  obtain ⟨c₁, hc₁⟩ := hv ⟨a, ha⟩
  obtain ⟨c₂, hc₂⟩ := hv ⟨b, hb⟩
  have e1 : a = c₁ • (v : V) := (congrArg Subtype.val hc₁).symm
  have e2 : b = c₂ • (v : V) := (congrArg Subtype.val hc₂).symm
  rcases g10Four_zmod_two_cases c₁ with rfl | rfl
  · exact absurd (by rw [e1, zero_smul]) ha0
  · rcases g10Four_zmod_two_cases c₂ with rfl | rfl
    · exact absurd (by rw [e2, zero_smul]) hb0
    · rw [e1, e2]

omit [Finite V] in
theorem g10Four_exists_dual (U : Submodule (ZMod 2) V) (c s : U)
    (hs : s ∉ Submodule.span (ZMod 2) {c}) :
    ∃ f : U →ₗ[ZMod 2] ZMod 2, f c = 0 ∧ f s = 1 := by
  obtain ⟨f, hf, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hs inferInstance
  refine ⟨f, ?_, ?_⟩
  · have : f c ∈ (Submodule.span (ZMod 2) {c}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    rw [hfmap] at this
    simpa using this
  · rcases g10Four_zmod_two_cases (f s) with h0 | h0
    · exact absurd h0 hf
    · exact h0

end CFSG.Quasithin
