module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs1

public section

namespace CFSG.Quasithin.H13.Abs523

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def IsKMin (𝒦V : Subgroup (MulAut V)) (Y : Subgroup V) : Prop :=
  Y ≠ ⊥ ∧ (∀ k ∈ 𝒦V, ∀ y ∈ Y, k y ∈ Y) ∧
    ∀ W : Subgroup V, W ≤ Y → W ≠ ⊥ → (∀ k ∈ 𝒦V, ∀ w ∈ W, k w ∈ W) → W = Y

@[expose] def fixK (𝒦V : Subgroup (MulAut V)) : Subgroup V where
  carrier := {x | ∀ k ∈ 𝒦V, k x = x}
  mul_mem' := fun {a b} ha hb k hk => by rw [map_mul, ha k hk, hb k hk]
  one_mem' := fun k _ => map_one k
  inv_mem' := fun {a} ha k hk => by rw [map_inv, ha k hk]

theorem exists_kmin (𝒦V : Subgroup (MulAut V)) (hV : (⊤ : Subgroup V) ≠ ⊥) :
    ∃ Y : Subgroup V, IsKMin 𝒦V Y := by
  let 𝒯 : Set (Subgroup V) := {Y | Y ≠ ⊥ ∧ ∀ k ∈ 𝒦V, ∀ y ∈ Y, k y ∈ Y}
  have hTop : (⊤ : Subgroup V) ∈ 𝒯 := ⟨hV, fun _ _ _ _ => trivial⟩
  obtain ⟨Y, hY𝒯, hmin⟩ := WellFounded.has_min wellFounded_lt 𝒯 ⟨⊤, hTop⟩
  refine ⟨Y, hY𝒯.1, hY𝒯.2, fun W hWY hW0 hWk => ?_⟩
  by_contra hne
  exact hmin W ⟨hW0, hWk⟩ (lt_of_le_of_ne hWY hne)

theorem fixK_eq_bot {𝒦V : Subgroup (MulAut V)} {vV : MulAut V}
    (hvN : vV ∈ Subgroup.normalizer (𝒦V : Set (MulAut V)))
    (hirr : ∀ W : Subgroup V, (∀ k ∈ 𝒦V, ∀ w ∈ W, k w ∈ W) → (∀ w ∈ W, vV w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (hnt : ∃ k ∈ 𝒦V, k ≠ 1) : fixK 𝒦V = ⊥ := by
  have hconj : ∀ k ∈ 𝒦V, vV⁻¹ * k * vV ∈ 𝒦V := by
    intro k hk
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hvN) k).mp hk
    simpa using h
  have hinv1 : ∀ k ∈ 𝒦V, ∀ w ∈ fixK 𝒦V, k w ∈ fixK 𝒦V := by
    intro k hk w hw
    show ∀ l ∈ 𝒦V, l (k w) = k w
    intro l hl
    have hwk : k w = w := hw k hk
    rw [hwk]
    exact hw l hl
  have hinv2 : ∀ w ∈ fixK 𝒦V, vV w ∈ fixK 𝒦V := by
    intro w hw
    show ∀ l ∈ 𝒦V, l (vV w) = vV w
    intro l hl
    calc l (vV w) = vV ((vV⁻¹ * l * vV) w) := by simp [MulAut.mul_apply]
      _ = vV w := by rw [hw _ (hconj l hl)]
  rcases hirr (fixK 𝒦V) hinv1 hinv2 with h | h
  · exact h
  · exfalso
    obtain ⟨k₀, hk₀, hk₀1⟩ := hnt
    apply hk₀1
    refine MulEquiv.ext fun x => ?_
    have hx : x ∈ fixK 𝒦V := by
      rw [h]
      exact Subgroup.mem_top x
    simpa using hx k₀ hk₀

end CFSG.Quasithin.H13.Abs523
