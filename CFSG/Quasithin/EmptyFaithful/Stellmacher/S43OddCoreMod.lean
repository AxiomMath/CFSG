module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

namespace F53.Stellmacher.S43

namespace Odd

namespace Core

@[expose] def IsQuadF (Af : Finset (Perm (Fin 5))) : Prop :=
  ∀ a ∈ Af, ∀ b ∈ Af, ∀ w : orth.W, orth.act a (orth.act b w * w⁻¹) = orth.act b w * w⁻¹

instance (Af : Finset (Perm (Fin 5))) : Decidable (IsQuadF Af) := by
  unfold IsQuadF; infer_instance

@[expose] def HasSwapsF (Af : Finset (Perm (Fin 5))) : Prop := swap 0 2 ∈ Af ∧ swap 1 3 ∈ Af

instance (Af : Finset (Perm (Fin 5))) : Decidable (HasSwapsF Af) := by
  unfold HasSwapsF; infer_instance

private theorem image_S5SylE : (Finset.univ : Finset (Fin 8)).image S5SylE = S5SylF := by
  unfold S5SylF; decide +kernel

set_option maxRecDepth 100000 in
private theorem quadratic_finite : ∀ s ∈ (Finset.univ : Finset (Fin 8)).powerset,
    (1 : Perm (Fin 5)) ∈ s.image S5SylE → OfdMul (s.image S5SylE) →
      4 ≤ (s.image S5SylE).card → IsQuadF (s.image S5SylE) → HasSwapsF (s.image S5SylE) := by
  decide +kernel

theorem swap_mem_of_quadratic (A : Subgroup (Perm (Fin 5))) (hA : A ≤ S5Syl)
    (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ w : orth.W,
      orth.act a (orth.act b w * w⁻¹) = orth.act b w * w⁻¹)
    (h4 : 4 ≤ Nat.card A) : swap 0 2 ∈ A ∧ swap 1 3 ∈ A := by
  classical
  set s : Finset (Fin 8) := Finset.univ.filter fun i => S5SylE i ∈ A with hs
  set Af : Finset (Perm (Fin 5)) := s.image S5SylE with hAf
  have hmem : ∀ σ, σ ∈ A ↔ σ ∈ Af := by
    intro σ
    constructor
    · intro hσ
      have h1 : σ ∈ S5SylF := (mem_S5Syl_iff σ).mp (hA hσ)
      rw [← image_S5SylE, Finset.mem_image] at h1
      obtain ⟨i, -, rfl⟩ := h1
      exact Finset.mem_image.mpr ⟨i, by simp [hs, hσ], rfl⟩
    · intro hσ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hσ
      simpa [hs] using hi
  have hcardA : Nat.card A = Af.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  have hone : (1 : Perm (Fin 5)) ∈ Af := (hmem 1).mp A.one_mem
  have hmul : OfdMul Af := fun a ha b hb =>
    (hmem _).mp (A.mul_mem ((hmem a).mpr ha) ((hmem b).mpr hb))
  have hquad : IsQuadF Af := fun a ha b hb w => hq a ((hmem a).mpr ha) b ((hmem b).mpr hb) w
  have h := quadratic_finite s (Finset.mem_powerset.mpr (Finset.subset_univ s)) hone hmul
    (hcardA ▸ h4) hquad
  exact ⟨(hmem _).mpr h.1, (hmem _).mpr h.2⟩

set_option maxRecDepth 100000 in
theorem exists_fix_mul_fix : ∀ w : orth.W, ∃ w₁ w₂ : orth.W, orth.act (swap 0 2) w₁ = w₁ ∧
    orth.act (swap 1 3) w₂ = w₂ ∧ w = w₁ * w₂ := by
  decide +kernel

theorem swap_ne_one : swap (0 : Fin 5) 2 ≠ 1 ∧ swap (1 : Fin 5) 3 ≠ 1 := by
  decide

end Core

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
