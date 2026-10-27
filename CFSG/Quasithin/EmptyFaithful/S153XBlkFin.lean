module

public import CFSG.Quasithin.EmptyFaithful.S153VFin

public section

namespace CFSG.Quasithin.X1469.Blk

open Equiv CFSG.Quasithin.ModF CFSG.Quasithin.ModV CFSG.QuasithinUnique.A5.Delta5

theorem card_vanish : ∀ p : Fin 5,
    (Finset.univ.filter fun f : Fin 5 → ZMod 2 => isEven f ∧ f p = 0).card = 8 := by
  decide +kernel

theorem card_line : ∀ p : Fin 5,
    (Finset.univ.filter fun f : Fin 5 → ZMod 2 => isEven f ∧ (f = 0 ∨ f = zvec p)).card = 2 := by
  decide +kernel

theorem zvec_self (p : Fin 5) : zvec p p = 0 := by
  simp [zvec]

theorem fix_of_klein {p : Fin 5} {v : Perm (Fin 5)} (hv : v ∈ klein p) : v p = p := by
  simp only [klein, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  exact hv.2.2

set_option synthInstance.maxSize 4096 in
theorem exists_comm_rep : ∀ (p : Fin 5) (x : Fin 5 → ZMod 2), isEven x → x p = 0 →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p = p ∧
      ∃ w : Fin 5 → ZMod 2, isEven w ∧ x = w + pact σ w := by
  decide +kernel

theorem klein_faithful : ∀ p : Fin 5, ∀ v ∈ klein p,
    (∀ x : Fin 5 → ZMod 2, isEven x → x p = 0 → pact v x = x) → v = 1 := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem exists_map_vanish : ∀ (p : Fin 5) (x : Fin 5 → ZMod 2), isEven x → x p = 0 → x ≠ 0 →
    x ≠ zvec p → ∀ x' : Fin 5 → ZMod 2, isEven x' → x' p = 0 → x' ≠ 0 → x' ≠ zvec p →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p = p ∧ x' = pact σ x := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem exists_sum_zvec : ∀ (p : Fin 5) (x : Fin 5 → ZMod 2), isEven x → x p = 0 → x ≠ 0 →
    x ≠ zvec p → ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p = p ∧ x + pact σ x = zvec p := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
theorem exists_not_line : ∀ (p : Fin 5) (x : Fin 5 → ZMod 2), isEven x → x p = 0 → x ≠ 0 →
    x ≠ zvec p → ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p = p ∧
      x + pact σ x ≠ 0 ∧ x + pact σ x ≠ zvec p := by
  decide +kernel

theorem exists_conj_klein : ∀ p : Fin 5, ∀ v ∈ klein p, v ≠ 1 → ∀ v' ∈ klein p, v' ≠ 1 →
    ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ σ p = p ∧ v' = σ * v * σ⁻¹ := by
  decide +kernel

theorem exists_klein_not_line : ∀ (p : Fin 5) (x : Fin 5 → ZMod 2), isEven x → x p ≠ 0 →
    ∃ v ∈ klein p, x + pact v x ≠ 0 ∧ x + pact v x ≠ zvec p := by
  decide +kernel

def gam (p : Fin 5) : Perm (Fin 5) := swap (p + 1) (p + 2) * swap (p + 2) (p + 3)

theorem gam_spec : ∀ p : Fin 5, Perm.sign (gam p) = 1 ∧ gam p p = p ∧ gam p ^ 3 = 1 := by
  unfold gam
  decide +kernel

theorem eq_one_of_comm_gam : ∀ p : Fin 5, ∀ v ∈ klein p,
    v * gam p * v⁻¹ * (gam p)⁻¹ = 1 → v = 1 := by
  unfold gam
  decide +kernel

theorem exists_comm_gam : ∀ p : Fin 5, ∀ v ∈ klein p,
    ∃ v' ∈ klein p, v = v' * gam p * v'⁻¹ * (gam p)⁻¹ := by
  unfold gam
  decide +kernel

end CFSG.Quasithin.X1469.Blk
