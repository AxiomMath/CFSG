module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R4

structure L27 (K : Type*) [Group K] : Prop where
  sylow3 : ∀ a a' : K, a ^ 3 = 1 → a ≠ 1 → a' ^ 3 = 1 → a' ≠ 1 →
    ∃ g : K, ∃ i : ℕ, g * a * g⁻¹ = a' ^ i
  cent3 : ∀ x : K, x ^ 3 = 1 → x ≠ 1 → ∀ y : K, y * x = x * y → ∃ i : ℕ, y = x ^ i
  cent2 : ∀ z : K, z * z = 1 → z ≠ 1 → Nat.card (Subgroup.centralizer ({z} : Set K)) = 8
  inv3 : ∀ z : K, z * z = 1 → z ≠ 1 → ∃ a : K, a ^ 3 = 1 ∧ a ≠ 1 ∧ z * a * z⁻¹ = a⁻¹
  card2 : ∀ D : Subgroup K, IsSylowTwoOf D ⊤ → Nat.card D = 8
  simple : IsSimpleGroup K

theorem L27.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (h : L27 K') :
    L27 K := by
  refine ⟨fun a a' ha ha1 ha' ha'1 => ?_, fun x hx hx1 y hy => ?_, fun z hz2 hz1 => ?_,
    fun z hz2 hz1 => ?_, fun D hD => ?_, ?_⟩
  · obtain ⟨g, i, hg⟩ := h.sylow3 (e a) (e a') (by rw [← map_pow, ha, map_one])
      (fun h1 => ha1 (e.injective (by rw [h1, map_one])))
      (by rw [← map_pow, ha', map_one]) (fun h1 => ha'1 (e.injective (by rw [h1, map_one])))
    refine ⟨e.symm g, i, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hg, map_pow]
  · obtain ⟨i, hi⟩ := h.cent3 (e x) (by rw [← map_pow, hx, map_one])
      (fun h1 => hx1 (e.injective (by rw [h1, map_one]))) (e y) (by rw [← map_mul, ← map_mul, hy])
    exact ⟨i, e.injective (by rw [hi, map_pow])⟩
  · have h8 := h.cent2 (e z) (by rw [← map_mul, hz2, map_one])
      (fun h1 => hz1 (e.injective (by rw [h1, map_one])))
    rw [← h8]
    refine Nat.card_congr
      { toFun := fun y => ⟨e y, Subgroup.mem_centralizer_iff.2 fun w hw => by
          rw [Set.mem_singleton_iff] at hw
          rw [hw, ← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 y.2 z rfl)]⟩
        invFun := fun y => ⟨e.symm y, Subgroup.mem_centralizer_iff.2 fun w hw => by
          rw [Set.mem_singleton_iff] at hw
          rw [hw]
          apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact Subgroup.mem_centralizer_iff.1 y.2 (e z) rfl⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  · obtain ⟨a, ha3, ha1, haz⟩ := h.inv3 (e z) (by rw [← map_mul, hz2, map_one])
      (fun h1 => hz1 (e.injective (by rw [h1, map_one])))
    refine ⟨e.symm a, ?_, ?_, ?_⟩
    · apply e.injective
      rw [map_pow, MulEquiv.apply_symm_apply, ha3, map_one]
    · intro h1
      apply ha1
      rw [← MulEquiv.apply_symm_apply e a, h1, map_one]
    · apply e.injective
      rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
      exact haz
  · have h1 := h.card2 (D.map e.toMonoidHom) (by
      have := (isSylowTwoOf_map_mulEquiv e (X := D) (Y := ⊤)).2 hD
      rwa [show (⊤ : Subgroup K).map e.toMonoidHom = ⊤ from Subgroup.map_top_of_surjective _
        e.surjective] at this)
    rw [Subgroup.card_map_of_injective e.injective] at h1
    exact h1
  · have := h.simple
    exact e.isSimpleGroup

end E217R4

end CFSG.Quasithin
