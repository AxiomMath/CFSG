module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16c167_block_trivial {S : Type*} {I : Set S} (hne : I.Nonempty)
    (hblock : ∀ π : Equiv.Perm S, π '' I = I ∨ Disjoint (π '' I) I) :
    I = Set.univ ∨ I.ncard = 1 := by
  classical
  by_contra hcon
  obtain ⟨hnu, hn1⟩ := not_or.1 hcon
  obtain ⟨a, ha⟩ := hne
  obtain ⟨c, hc⟩ : ∃ c, c ∉ I := by
    by_contra h
    push Not at h
    exact hnu (Set.eq_univ_of_forall h)
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ I, b ≠ a := by
    by_contra h
    push Not at h
    apply hn1
    rw [Set.ncard_eq_one]
    exact ⟨a, Set.eq_singleton_iff_unique_mem.2 ⟨ha, fun x hx => h x hx⟩⟩
  have hac : a ≠ c := fun h => hc (h ▸ ha)
  rcases hblock (Equiv.swap b c) with h | h
  · apply hc
    rw [← h]
    exact ⟨b, hb, Equiv.swap_apply_left b c⟩
  · have ha' : a ∈ (Equiv.swap b c) '' I :=
      ⟨a, ha, Equiv.swap_apply_of_ne_of_ne hba.symm hac⟩
    exact Set.disjoint_left.1 h ha' ha

set_option synthInstance.maxSize 2048 in
private theorem s16c167_perm_four_check :
    ∀ a b c : Equiv.Perm (Fin 4), a * a = 1 → b * b = 1 → c * c = 1 →
      a * b = b * a → a * c = c * a → b * c = c * b → a ≠ 1 → b ≠ 1 → b ≠ a →
      c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  decide +kernel

theorem s16c167_card_le_four_of_perm_four {α : Type*} [Finite α] (hα : Nat.card α = 4)
    {X : Subgroup (Equiv.Perm α)} (h2 : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 4 := by
  classical
  obtain ⟨e⟩ : Nonempty (α ≃ Fin 4) := ⟨(Finite.equivFin α).trans (finCongr hα)⟩
  let φ : Equiv.Perm α ≃* Equiv.Perm (Fin 4) := e.permCongrHom
  let X' : Subgroup (Equiv.Perm (Fin 4)) := X.map φ.toMonoidHom
  have hcard : Nat.card X = Nat.card X' :=
    (Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective).symm
  have h2' : ∀ x ∈ X', x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, h2 x hx, map_one]
  have hcomm : ∀ x ∈ X', ∀ y ∈ X', x * y = y * x := by
    intro x hx y hy
    have e1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h2' x hx)
    have e2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h2' y hy)
    have e3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (h2' _ (X'.mul_mem hx hy))
    calc x * y = (x * y)⁻¹ := e3.symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [e1, e2]
  have hcover : ∃ a b : Equiv.Perm (Fin 4), ∀ c ∈ X', c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
    by_cases h1 : ∀ x ∈ X', x = 1
    · exact ⟨1, 1, fun c hc => Or.inl (h1 c hc)⟩
    push Not at h1
    obtain ⟨a, haX, ha1⟩ := h1
    by_cases h2a : ∀ x ∈ X', x = 1 ∨ x = a
    · exact ⟨a, 1, fun c hc => (h2a c hc).elim Or.inl fun h => Or.inr (Or.inl h)⟩
    push Not at h2a
    obtain ⟨b, hbX, hb1, hba⟩ := h2a
    refine ⟨a, b, fun c hc => ?_⟩
    exact s16c167_perm_four_check a b c (h2' a haX) (h2' b hbX) (h2' c hc)
      (hcomm a haX b hbX) (hcomm a haX c hc) (hcomm b hbX c hc) ha1 hb1 hba
  obtain ⟨a, b, hab⟩ := hcover
  have hsub : (X' : Set (Equiv.Perm (Fin 4))) ⊆ {1, a, b, a * b} := by
    intro c hc
    rcases hab c hc with h | h | h | h <;> simp [h]
  rw [hcard]
  calc Nat.card X' = (X' : Set (Equiv.Perm (Fin 4))).ncard := (Nat.card_coe_set_eq _).symm
    _ ≤ ({1, a, b, a * b} : Set (Equiv.Perm (Fin 4))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
        simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
