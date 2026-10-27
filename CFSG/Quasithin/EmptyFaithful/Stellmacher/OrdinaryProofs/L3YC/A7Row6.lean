module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6

open Equiv

def xP : Perm (Fin 7) := swap 0 1 * swap 1 2

def yP : Perm (Fin 7) := swap 3 4 * swap 4 5

def pw (a b : Fin 3) : Perm (Fin 7) := xP ^ a.val * yP ^ b.val

def E9 : Subgroup (Perm (Fin 7)) := Subgroup.closure {xP, yP}

theorem xP_eq_pw : xP = pw 1 0 := by decide +kernel

theorem yP_eq_pw : yP = pw 0 1 := by decide +kernel

theorem pw_zero_zero : pw 0 0 = 1 := by decide +kernel

theorem pw_mul_pw : ∀ a b c d : Fin 3, pw a b * pw c d = pw (a + c) (b + d) := by
  decide +kernel

theorem pw_inv : ∀ a b : Fin 3, (pw a b)⁻¹ = pw (-a) (-b) := by decide +kernel

theorem mem_E9_iff (g : Perm (Fin 7)) : g ∈ E9 ↔ ∃ a b : Fin 3, g = pw a b := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨1, 0, xP_eq_pw⟩
      · exact ⟨0, 1, yP_eq_pw⟩
    | one => exact ⟨0, 0, pw_zero_zero.symm⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨c, d, rfl⟩ := hy
      exact ⟨a + c, b + d, pw_mul_pw a b c d⟩
    | inv x _ hx =>
      obtain ⟨a, b, rfl⟩ := hx
      exact ⟨-a, -b, pw_inv a b⟩
  · rintro ⟨a, b, rfl⟩
    unfold pw
    exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
      (pow_mem (Subgroup.subset_closure (by simp)) _)

def expo (g : Perm (Fin 7)) : Option (Fin 3 × Fin 3) :=
  (List.finRange 3 ×ˢ List.finRange 3).find? fun p => decide (pw p.1 p.2 = g)

theorem expo_pw : ∀ a b : Fin 3, expo (pw a b) = some (a, b) := by decide +kernel

def normalises (n : Perm (Fin 7)) : Bool :=
  (expo (n * xP * n⁻¹)).isSome && (expo (n * yP * n⁻¹)).isSome

def detOK (n : Perm (Fin 7)) : Bool :=
  match expo (n * xP * n⁻¹), expo (n * yP * n⁻¹) with
  | some (a, c), some (b, d) =>
      decide (((a.val : ℕ) : ZMod 3) * ((d.val : ℕ) : ZMod 3)
        - ((b.val : ℕ) : ZMod 3) * ((c.val : ℕ) : ZMod 3) = 1)
  | _, _ => false

set_option maxRecDepth 100000 in
theorem detOK_of_even : ∀ n : Perm (Fin 7), Equiv.Perm.sign n = 1 → normalises n = true →
    detOK n = true := by
  decide +kernel

theorem row6_normalizer_E9_det (n : Perm (Fin 7)) (hn : n ∈ alternatingGroup (Fin 7))
    (hN : n ∈ Subgroup.normalizer E9) :
    ∃ a b c d : Fin 3,
      ((a.val : ℕ) : ZMod 3) * ((d.val : ℕ) : ZMod 3)
        - ((b.val : ℕ) : ZMod 3) * ((c.val : ℕ) : ZMod 3) = 1 ∧
      n * xP * n⁻¹ = pw a c ∧ n * yP * n⁻¹ = pw b d := by
  have hx : xP ∈ E9 := Subgroup.subset_closure (by simp)
  have hy : yP ∈ E9 := Subgroup.subset_closure (by simp)
  obtain ⟨a, c, hxa⟩ := (mem_E9_iff _).1 ((Subgroup.mem_normalizer_iff.1 hN xP).1 hx)
  obtain ⟨b, d, hyb⟩ := (mem_E9_iff _).1 ((Subgroup.mem_normalizer_iff.1 hN yP).1 hy)
  have hsign : Equiv.Perm.sign n = 1 := Equiv.Perm.mem_alternatingGroup.1 hn
  have hnorm : normalises n = true := by
    simp [normalises, hxa, hyb, expo_pw]
  have hdet := detOK_of_even n hsign hnorm
  simp only [detOK, hxa, hyb, expo_pw, decide_eq_true_eq] at hdet
  exact ⟨a, b, c, d, hdet, hxa, hyb⟩

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC.A7Row6

end
