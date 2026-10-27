module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ASVolI.ChH

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem ne_and_ne_iff_swap_apply_eq {a b : α} (hab : a ≠ b) (x : α) :
    (x ≠ a ∧ x ≠ b) ↔ swap a b x = x := by
  rw [swap_apply_def]
  split_ifs with h₁ h₂
  · subst h₁
    exact iff_of_false (fun h => h.1 rfl) (fun h => hab h.symm)
  · subst h₂
    exact iff_of_false (fun h => h.2 rfl) (fun h => hab h)
  · exact iff_of_true ⟨h₁, h₂⟩ rfl

private theorem preserves_off_of_mem_centralizer {a b : α} (hab : a ≠ b) {g : Perm α}
    (hg : g ∈ Subgroup.centralizer ({swap a b} : Set (Perm α))) (x : α) :
    (g x ≠ a ∧ g x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
  have h : swap a b (g x) = g (swap a b x) :=
    congrArg (fun f : Perm α => f x) (Subgroup.mem_centralizer_iff.mp hg (swap a b) rfl)
  rw [ne_and_ne_iff_swap_apply_eq hab, ne_and_ne_iff_swap_apply_eq hab, h]
  exact g.injective.eq_iff

private def restrictOff {a b : α} (hab : a ≠ b) :
    ↥(alternatingGroup α ⊓ Subgroup.centralizer ({swap a b} : Set (Perm α))) →*
      Perm {x : α // x ≠ a ∧ x ≠ b} where
  toFun g := (g : Perm α).subtypePerm
    (preserves_off_of_mem_centralizer hab (Subgroup.mem_inf.mp g.2).2)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem restrictOff_injective {a b : α} (hab : a ≠ b) :
    Function.Injective (restrictOff hab) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hsign : sign (g : Perm α) = 1 :=
    mem_alternatingGroup.mp (Subgroup.mem_inf.mp g.2).1
  have hpres := preserves_off_of_mem_centralizer hab (Subgroup.mem_inf.mp g.2).2
  have hfix : ∀ x, x ≠ a → x ≠ b → (g : Perm α) x = x := fun x h₁ h₂ =>
    congrArg (fun f : Perm {x : α // x ≠ a ∧ x ≠ b} => (f ⟨x, h₁, h₂⟩ : α)) hg
  have hga : (g : Perm α) a = a ∨ (g : Perm α) a = b := by
    by_cases h₁ : (g : Perm α) a = a
    · exact Or.inl h₁
    by_cases h₂ : (g : Perm α) a = b
    · exact Or.inr h₂
    exact (((hpres a).mp ⟨h₁, h₂⟩).1 rfl).elim
  have hgb : (g : Perm α) b = a ∨ (g : Perm α) b = b := by
    by_cases h₁ : (g : Perm α) b = a
    · exact Or.inl h₁
    by_cases h₂ : (g : Perm α) b = b
    · exact Or.inr h₂
    exact (((hpres b).mp ⟨h₁, h₂⟩).2 rfl).elim
  rcases hga with ha | ha
  · have hb : (g : Perm α) b = b := by
      rcases hgb with h | h
      · exact absurd ((g : Perm α).injective (h.trans ha.symm)) hab.symm
      · exact h
    refine Subtype.ext ?_
    ext x
    by_cases h₁ : x = a
    · subst h₁
      exact ha
    · by_cases h₂ : x = b
      · subst h₂
        exact hb
      · exact hfix x h₁ h₂
  · have hb : (g : Perm α) b = a := by
      rcases hgb with h | h
      · exact h
      · exact absurd ((g : Perm α).injective (ha.trans h.symm)) hab
    have hg' : (g : Perm α) = swap a b := by
      ext x
      by_cases h₁ : x = a
      · subst h₁
        rw [swap_apply_left]
        exact ha
      · by_cases h₂ : x = b
        · subst h₂
          rw [swap_apply_right]
          exact hb
        · rw [swap_apply_of_ne_of_ne h₁ h₂]
          exact hfix x h₁ h₂
    rw [hg', sign_swap hab] at hsign
    exact absurd hsign (by decide)

private theorem restrictOff_surjective {a b : α} (hab : a ≠ b) :
    Function.Surjective (restrictOff hab) := by
  intro σ
  have hdisj : (ofSubtype σ : Perm α).Disjoint (swap a b) := fun x => by
    by_cases hx : x ≠ a ∧ x ≠ b
    · exact Or.inr (swap_apply_of_ne_of_ne hx.1 hx.2)
    · exact Or.inl (ofSubtype_apply_of_not_mem σ hx)
  have key : ∀ c : Perm α, (c = 1 ∨ c = swap a b) → sign ((ofSubtype σ : Perm α) * c) = 1 →
      ∃ g, restrictOff hab g = σ := by
    intro c hc hs
    have hcomm : Commute ((ofSubtype σ : Perm α) * c) (swap a b) := by
      rcases hc with rfl | rfl
      · simpa using hdisj.commute
      · exact hdisj.commute.mul_left (Commute.refl _)
    refine ⟨⟨(ofSubtype σ : Perm α) * c, Subgroup.mem_inf.mpr
      ⟨mem_alternatingGroup.mpr hs, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq⟩⟩, ?_⟩
    ext ⟨x, hx⟩
    have hcx : c x = x := by
      rcases hc with rfl | rfl
      · rfl
      · exact swap_apply_of_ne_of_ne hx.1 hx.2
    show ((ofSubtype σ : Perm α) (c x) : α) = σ ⟨x, hx⟩
    rw [hcx]
    exact ofSubtype_apply_of_mem σ hx
  rcases Int.units_eq_one_or (sign σ) with hs | hs
  · exact key 1 (Or.inl rfl) (by rw [mul_one, sign_ofSubtype, hs])
  · exact key (swap a b) (Or.inr rfl) (by rw [map_mul, sign_ofSubtype, hs, sign_swap hab]; decide)

theorem nonempty_alternatingInfCentralizer_swap_mulEquiv {a b : α} (hab : a ≠ b) :
    Nonempty (↥(alternatingGroup α ⊓ Subgroup.centralizer ({swap a b} : Set (Perm α))) ≃*
      Perm {x : α // x ≠ a ∧ x ≠ b}) :=
  ⟨MulEquiv.ofBijective (restrictOff hab)
    ⟨restrictOff_injective hab, restrictOff_surjective hab⟩⟩

end CFSG.ASVolI.ChH
