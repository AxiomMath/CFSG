module

public import CFSG.Quasithin.Background.G9StmtsModels

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11

namespace Case0M12

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem sum_permAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Fin n → ZMod 2) :
    ∑ i, permAct σ u i = ∑ i, u i := by
  unfold permAct
  exact Equiv.sum_comp σ⁻¹ u

theorem dot_permAct {n : ℕ} (σ : Equiv.Perm (Fin n)) (u w : Fin n → ZMod 2) :
    permAct σ u ⬝ᵥ permAct σ w = u ⬝ᵥ w := by
  unfold permAct dotProduct
  exact Equiv.sum_comp σ⁻¹ (fun i => u i * w i)

theorem permAct_mem {n : ℕ} (σ : Equiv.Perm (Fin n)) {u : Fin n → ZMod 2} (hu : u ∈ permCore n) :
    permAct σ u ∈ permCore n := by
  change ∑ i, permAct σ u i = 0
  rw [sum_permAct]
  exact hu

theorem dot_ones_left {n : ℕ} (w : Fin n → ZMod 2) :
    (fun _ => (1 : ZMod 2)) ⬝ᵥ w = ∑ i : Fin n, w i := by
  simp [dotProduct]

theorem selfDual_of_isPermCoreModule {n : ℕ} (hn : Even n) {H : Subgroup (GLV V)}
    {G₀ : Subgroup (Equiv.Perm (Fin n))} (h : IsPermCoreModule H G₀) : SelfDual H ⊤ := by
  obtain ⟨φ, β, hsurj, hker, hequiv⟩ := h
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective β (LinearMap.range_eq_top.2 hsurj)
  have hβs : ∀ x : V, β (s x) = x := fun x => congrArg (fun f => f x) hs
  have hdot : ∀ w w' z : ↥(permCore n), β w = β w' →
      (w : Fin n → ZMod 2) ⬝ᵥ (z : Fin n → ZMod 2) = (w' : Fin n → ZMod 2) ⬝ᵥ (z : Fin n → ZMod 2) := by
    intro w w' z hww
    have h0 : β (w + w') = 0 := by
      rw [map_add, hww, ← two_smul (ZMod 2)]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_smul]
    rcases (hker _).1 h0 with h1 | ⟨-, h1⟩
    · have h2 : (w : Fin n → ZMod 2) = (w' : Fin n → ZMod 2) := by
        funext i
        have := congrFun (congrArg Subtype.val h1) i
        have h3 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
        exact h3 _ _ this
      rw [h2]
    · have h2 : (w : Fin n → ZMod 2) = (w' : Fin n → ZMod 2) + fun _ => 1 := by
        funext i
        have h3 : ∀ a b : ZMod 2, a + b = 1 → a = b + 1 := by decide
        exact h3 _ _ (h1 i)
      have hz : ∑ i : Fin n, (z : Fin n → ZMod 2) i = 0 := z.2
      rw [h2, add_dotProduct, dot_ones_left, hz]
      simp
  let f : LinearMap.BilinForm (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) :=
    LinearMap.mk₂ (ZMod 2) (fun x y => ((s x.1 : ↥(permCore n)) : Fin n → ZMod 2) ⬝ᵥ
      ((s y.1 : ↥(permCore n)) : Fin n → ZMod 2))
      (by intros; simp [add_dotProduct]) (by intros; simp [smul_dotProduct])
      (by intros; simp [dotProduct_add]) (by intros; simp [dotProduct_smul])
  have hf : ∀ x y : ↥(⊤ : Submodule (ZMod 2) V), f x y =
      ((s x.1 : ↥(permCore n)) : Fin n → ZMod 2) ⬝ᵥ ((s y.1 : ↥(permCore n)) : Fin n → ZMod 2) :=
    fun _ _ => rfl
  have hcomm : ∀ x y : ↥(⊤ : Submodule (ZMod 2) V), f x y = f y x := fun x y => by
    rw [hf, hf, dotProduct_comm]
  have hleft : ∀ x : ↥(⊤ : Submodule (ZMod 2) V), (∀ y, f x y = 0) → x = 0 := by
    intro x hx
    set u : ↥(permCore n) := s x.1 with hu
    have horth : ∀ w : ↥(permCore n), (u : Fin n → ZMod 2) ⬝ᵥ (w : Fin n → ZMod 2) = 0 := by
      intro w
      have h1 := hx ⟨β w, Submodule.mem_top⟩
      rw [hf] at h1
      have h2 : β w = β (s (β w)) := (hβs _).symm
      have h3 := hdot w (s (β w)) u h2
      rw [dotProduct_comm, h3, dotProduct_comm]
      exact h1
    have hall : ∀ i j : Fin n, (u : Fin n → ZMod 2) i = (u : Fin n → ZMod 2) j := by
      intro i j
      by_cases hij : i = j
      · rw [hij]
      · have hw : (Pi.single i 1 + Pi.single j 1 : Fin n → ZMod 2) ∈ permCore n := by
          change ∑ k, (Pi.single i 1 + Pi.single j 1 : Fin n → ZMod 2) k = 0
          simp [Finset.sum_add_distrib, Pi.single_apply]
          decide
        have := horth ⟨_, hw⟩
        simp [dotProduct, mul_add, Finset.sum_add_distrib, Pi.single_apply] at this
        have h3 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
        exact h3 _ _ this
    have hβu : β u = 0 := by
      rw [hker]
      by_cases hone : ∃ i, (u : Fin n → ZMod 2) i = 1
      · obtain ⟨i0, hi0⟩ := hone
        exact Or.inr ⟨hn, fun j => (hall j i0).trans hi0⟩
      · left
        apply Subtype.ext
        funext i
        have : (u : Fin n → ZMod 2) i ≠ 1 := fun h' => hone ⟨i, h'⟩
        change (u : Fin n → ZMod 2) i = 0
        generalize (u : Fin n → ZMod 2) i = a at this
        revert a
        decide
    have : x.1 = 0 := by
      have h1 := hβs x.1
      rw [← hu, hβu] at h1
      exact h1.symm
    exact Subtype.ext this
  refine ⟨f, ⟨hleft, fun y hy => hleft y fun x => by rw [hcomm]; exact hy x⟩, ?_⟩
  intro k hk i j i' j' hki hkj
  let γ : ↥H := ⟨k, hk⟩
  have hp : ∀ x x' : ↥(⊤ : Submodule (ZMod 2) V), k (x : V) = (x' : V) →
      β ⟨permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s x.1 : Fin n → ZMod 2),
        permAct_mem _ (s x.1).2⟩ = β (s x'.1) := by
    intro x x' hxx
    rw [hequiv γ (s x.1) ⟨_, permAct_mem _ (s x.1).2⟩ rfl, hβs, hβs]
    exact hxx
  rw [hf, hf]
  have h1 := hdot _ _ (s j'.1) (hp i i' hki)
  have h2 := hdot _ _ ⟨permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s i.1 : Fin n → ZMod 2),
    permAct_mem _ (s i.1).2⟩ (hp j j' hkj)
  calc ((s i'.1 : ↥(permCore n)) : Fin n → ZMod 2) ⬝ᵥ ((s j'.1 : ↥(permCore n)) : Fin n → ZMod 2)
      = permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s i.1 : Fin n → ZMod 2) ⬝ᵥ
          ((s j'.1 : ↥(permCore n)) : Fin n → ZMod 2) := h1.symm
    _ = ((s j'.1 : ↥(permCore n)) : Fin n → ZMod 2) ⬝ᵥ
          permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s i.1 : Fin n → ZMod 2) := dotProduct_comm _ _
    _ = permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s j.1 : Fin n → ZMod 2) ⬝ᵥ
          permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s i.1 : Fin n → ZMod 2) := h2.symm
    _ = permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s i.1 : Fin n → ZMod 2) ⬝ᵥ
          permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (s j.1 : Fin n → ZMod 2) := dotProduct_comm _ _
    _ = ((s i.1 : ↥(permCore n)) : Fin n → ZMod 2) ⬝ᵥ ((s j.1 : ↥(permCore n)) : Fin n → ZMod 2) :=
        dot_permAct _ _ _

end Case0M12

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
