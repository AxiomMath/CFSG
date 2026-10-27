module

public import CFSG.RankThree.PartOne.N1322.MonoAux

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

theorem isRefl_mono_cases' (h2 : (2 : K) ≠ 0) {σ : Perm (Fin 3)} {a : Fin 3 → Kˣ}
    (h : IsRefl (mono σ a : GL (Fin 3) K)) :
    (σ = 1 ∧ (a = epsU 0 ∨ a = epsU 1 ∨ a = epsU 2)) ∨ (σ = swap 0 1 ∧ a = aU 0 1 (a 0)) ∨
      (σ = swap 0 2 ∧ a = aU 0 2 (a 0)) ∨ (σ = swap 1 2 ∧ a = aU 1 2 (a 1)) := by
  rcases perm_involution_cases σ (mono_sq_eq_one h.sq).1 with rfl | rfl | rfl | rfl
  · exact Or.inl ⟨rfl, isRefl_diag h2 h⟩
  · exact Or.inr (Or.inl ⟨rfl, isRefl_swap (k := 2) (by decide) (by decide) (by decide)
      (by decide) h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, isRefl_swap (k := 1) (by decide) (by decide) (by decide)
      (by decide) h⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, isRefl_swap (k := 0) (by decide) (by decide) (by decide)
      (by decide) h⟩))

theorem mono_ext {σ τ : Perm (Fin 3)} {a b : Fin 3 → Kˣ} (hσ : σ = τ) (ha : ∀ j, a j = b j) :
    (mono σ a : GL (Fin 3) K) = mono τ b := by
  subst hσ
  exact congrArg _ (funext ha)

theorem aU_one (i j : Fin 3) : aU i j (1 : Kˣ) = fun _ => 1 := by
  funext m
  simp [aU]

@[expose] def permMono : Perm (Fin 3) →* GL (Fin 3) K where
  toFun σ := mono σ (fun _ => 1)
  map_one' := mono_one
  map_mul' σ τ := by
    show mono (σ * τ) (fun _ => 1) = mono σ (fun _ => 1) * mono τ (fun _ => 1)
    rw [mono_mul]
    exact mono_ext rfl (fun j => by simp)

theorem permMono_apply (σ : Perm (Fin 3)) :
    (permMono σ : GL (Fin 3) K) = mono σ (fun _ => 1) := rfl

theorem perm_words : ∀ σ : Perm (Fin 3), σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 1 2 ∨
    σ = swap 0 1 * swap 1 2 ∨ σ = swap 1 2 * swap 0 1 ∨
      σ = swap 0 1 * swap 1 2 * swap 0 1 := by decide

theorem permMono_mem {X : Subgroup (GL (Fin 3) K)} (h01 : permMono (swap 0 1) ∈ X)
    (h12 : permMono (swap 1 2) ∈ X) (σ : Perm (Fin 3)) : permMono σ ∈ X := by
  rcases perm_words σ with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [map_one]; exact X.one_mem
  · exact h01
  · exact h12
  · rw [map_mul]; exact X.mul_mem h01 h12
  · rw [map_mul]; exact X.mul_mem h12 h01
  · rw [map_mul, map_mul]; exact X.mul_mem (X.mul_mem h01 h12) h01

theorem pm_mul {a b : Kˣ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

theorem pm_inv {a : Kˣ} (ha : a = 1 ∨ a = -1) : a⁻¹ = 1 ∨ a⁻¹ = -1 := by
  rcases ha with rfl | rfl <;> simp

@[expose] def wb3 (K : Type*) [Field K] : Subgroup (GL (Fin 3) K) where
  carrier := {g | ∃ σ a, g = mono σ a ∧ ∀ j, a j = 1 ∨ a j = -1}
  mul_mem' := by
    rintro _ _ ⟨σ, a, rfl, ha⟩ ⟨τ, b, rfl, hb⟩
    exact ⟨σ * τ, fun j => a (τ j) * b j, mono_mul σ τ a b, fun j => pm_mul (ha _) (hb j)⟩
  one_mem' := ⟨1, fun _ => 1, mono_one.symm, fun _ => Or.inl rfl⟩
  inv_mem' := by
    rintro _ ⟨σ, a, rfl, ha⟩
    exact ⟨σ⁻¹, fun j => (a (σ⁻¹ j))⁻¹, mono_inv σ a, fun j => pm_inv (ha _)⟩

theorem mem_wb3_iff {g : GL (Fin 3) K} :
    g ∈ wb3 K ↔ ∃ σ a, g = mono σ a ∧ ∀ j, a j = 1 ∨ a j = -1 := Iff.rfl

theorem wb3_finite_card (h2 : (2 : K) ≠ 0) : Finite (wb3 K) ∧ Nat.card (wb3 K) ≤ 48 := by
  classical
  choose σf af hspec using fun g : wb3 K => g.2
  let f : wb3 K → Perm (Fin 3) × (Fin 3 → Bool) := fun g => (σf g, fun j => decide (af g j = -1))
  have hinj : Function.Injective f := by
    intro g g' hgg'
    have h1 : σf g = σf g' := congrArg Prod.fst hgg'
    have h3 : ∀ j, decide (af g j = -1) = decide (af g' j = -1) := fun j =>
      congrFun (congrArg Prod.snd hgg') j
    apply Subtype.ext
    rw [(hspec g).1, (hspec g').1, h1]
    refine congrArg _ (funext fun j => ?_)
    have e := h3 j
    rcases (hspec g).2 j with hj | hj <;> rcases (hspec g').2 j with hj' | hj'
    · rw [hj, hj']
    · exfalso
      simp [hj, hj', (neg_one_ne_one h2).symm] at e
    · exfalso
      simp [hj, hj', (neg_one_ne_one h2).symm] at e
    · rw [hj, hj']
  have hfin : Finite (wb3 K) := Finite.of_injective f hinj
  have := Nat.card_le_card_of_injective f hinj
  have h48 : Nat.card (Perm (Fin 3) × (Fin 3 → Bool)) = 48 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact ⟨hfin, by omega⟩

end CFSG.RankThree.PartOne.N1322
