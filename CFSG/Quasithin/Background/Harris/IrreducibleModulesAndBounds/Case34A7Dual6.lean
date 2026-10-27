module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case34A7End6

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 Equiv

namespace Case34A7

theorem dot_nondeg (x : Fin 7 → ZMod 2) (hx : x ∈ permCore 7)
    (h : ∀ y : Fin 7 → ZMod 2, y ∈ permCore 7 → ∑ k, x k * y k = 0) : x = 0 := by
  have hx' : ∑ i, x i = 0 := hx
  have key : ∀ (a : Fin 7), a ≠ 6 → x a + x 6 = 0 := by
    intro a ha
    have hy : (fun i : Fin 7 => if i = a ∨ i = 6 then (1 : ZMod 2) else 0) ∈ permCore 7 := by
      show ∑ i, (if i = a ∨ i = 6 then (1 : ZMod 2) else 0) = 0
      revert ha
      revert a
      decide
    have hs := h _ hy
    revert hs ha
    fin_cases a <;> simp [Fin.sum_univ_seven]
  have c2 : ∀ p q : ZMod 2, p + q = 0 → p = q := by decide
  have e : ∀ a : Fin 7, x a = x 6 := by
    intro a
    by_cases ha : a = 6
    · rw [ha]
    · exact c2 _ _ (key a ha)
  rw [Fin.sum_univ_seven] at hx'
  simp only [e 0, e 1, e 2, e 3, e 4, e 5] at hx'
  have key2 : ∀ c : ZMod 2, c + c + c + c + c + c + c = 0 → c = 0 := by decide
  have h6 := key2 _ hx'
  funext i
  rw [e i, h6]
  rfl

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_permCore {L : Subgroup (GLV V)} {f : ↥L ≃* ↥(alternatingGroup (Fin 7))}
    {β : ↥(permCore 7) →ₗ[ZMod 2] V} (hβ : PermCoreData f β) : SelfDual L ⊤ := by
  obtain ⟨hbij, hequi⟩ := hβ
  let gl : V ≃ₗ[ZMod 2] ↥(permCore 7) := (LinearEquiv.ofBijective β hbij).symm
  let g : ↥(⊤ : Submodule (ZMod 2) V) →ₗ[ZMod 2] (Fin 7 → ZMod 2) :=
    (permCore 7).subtype ∘ₗ gl.toLinearMap ∘ₗ (⊤ : Submodule (ZMod 2) V).subtype
  have hg : ∀ i : ↥(⊤ : Submodule (ZMod 2) V), g i = (gl (i : V) : Fin 7 → ZMod 2) := fun i => rfl
  have hgmem : ∀ i, g i ∈ permCore 7 := fun i => (gl (i : V)).2
  have hgsurj : ∀ y ∈ permCore 7, ∃ j, g j = y := by
    intro y hy
    refine ⟨⟨β ⟨y, hy⟩, trivial⟩, ?_⟩
    rw [hg]
    show ((LinearEquiv.ofBijective β hbij).symm (β ⟨y, hy⟩) : Fin 7 → ZMod 2) = y
    rw [LinearEquiv.ofBijective_symm_apply_apply]
  let B : LinearMap.BilinForm (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) :=
    LinearMap.mk₂ (ZMod 2) (fun i j => ∑ k, g i k * g j k)
      (fun m₁ m₂ n => by simp [map_add, add_mul, Finset.sum_add_distrib])
      (fun c m n => by simp [map_smul, Finset.mul_sum, mul_assoc])
      (fun m n₁ n₂ => by simp [map_add, mul_add, Finset.sum_add_distrib])
      (fun c m n => by simp [map_smul, Finset.mul_sum, mul_left_comm])
  have hB : ∀ i j, B i j = ∑ k, g i k * g j k := fun i j => rfl
  have hleft : ∀ x : ↥(⊤ : Submodule (ZMod 2) V), (∀ y, B x y = 0) → x = 0 := by
    intro x hx
    have h0 : g x = 0 := by
      refine dot_nondeg _ (hgmem x) fun y hy => ?_
      obtain ⟨j, rfl⟩ := hgsurj y hy
      exact hx j
    have h1 : gl (x : V) = 0 := Subtype.ext h0
    have h2 : (x : V) = 0 := gl.injective (h1.trans (map_zero gl).symm)
    exact Subtype.ext h2
  refine ⟨B, ⟨hleft, fun y hy => hleft y fun x => ?_⟩, ?_⟩
  · rw [hB, ← hy x, hB]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · intro k hk i j i' j' hi hj
    let γ : ↥L := ⟨k, hk⟩
    have hact : ∀ i i' : ↥(⊤ : Submodule (ZMod 2) V), k (i : V) = (i' : V) →
        g i' = permAct ((f γ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) (g i) := by
      intro i i' h
      let σ : Perm (Fin 7) := ((f γ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))
      let x' : ↥(permCore 7) :=
        ⟨permAct σ (gl (i : V) : Fin 7 → ZMod 2), permAct_mem_permCore σ (gl (i : V)).2⟩
      have hm := hequi γ (gl (i : V)) x' rfl
      have h3 : β (gl (i : V)) = (i : V) := (LinearEquiv.ofBijective β hbij).apply_symm_apply _
      rw [h3] at hm
      have h4 : gl (i' : V) = x' := by
        apply gl.symm.injective
        have h5 : gl.symm = LinearEquiv.ofBijective β hbij := rfl
        rw [LinearEquiv.symm_apply_apply, h5]
        show (i' : V) = β _
        rw [hm]
        exact h.symm
      rw [hg, h4, hg i]
    rw [hB, hB, hact i i' hi, hact j j' hj]
    exact Equiv.sum_comp (((f γ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7))⁻¹)
      (fun m => g i m * g j m)

end Case34A7

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
