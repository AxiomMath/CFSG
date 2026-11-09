module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.Permutation.FinPackDec

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

open CFSG.Permutation.FinPack in
noncomputable def expoK (c : ℕ) : Option (Fin 3 × Fin 3) :=
  (List.finRange 3 ×ˢ List.finRange 3).find? fun p => Nat.beq (enc (pw p.1 p.2)) c

open CFSG.Permutation.FinPack in
theorem expo_eq_expoK (g : Perm (Fin 7)) : expo g = expoK (enc g) := by
  simp only [expo, expoK, beq_enc_eq_decide (by norm_num : 7 ≤ 16)]

def detK (o1 o2 : Option (Fin 3 × Fin 3)) : Bool :=
  o1.elim false fun p => o2.elim false fun q =>
    decide (((p.1.val : ℕ) : ZMod 3) * ((q.2.val : ℕ) : ZMod 3)
      - ((q.1.val : ℕ) : ZMod 3) * ((p.2.val : ℕ) : ZMod 3) = 1)

theorem detOK_eq_detK (n : Perm (Fin 7)) :
    detOK n = detK (expo (n * xP * n⁻¹)) (expo (n * yP * n⁻¹)) := by
  unfold detOK detK
  generalize expo (n * xP * n⁻¹) = o1
  generalize expo (n * yP * n⁻¹) = o2
  rcases o1 with _ | ⟨a, c⟩ <;> rcases o2 with _ | ⟨b, d⟩ <;> rfl

open CFSG.Permutation.FinPack in
set_option maxRecDepth 100000 in
theorem detOK_of_even : ∀ n : Perm (Fin 7), Equiv.Perm.sign n = 1 → normalises n = true →
    detOK n = true := by
  have hw : walkK 7 (fun c => !evenK 7 c ||
      !((expoK (mulK 7 (mulK 7 c (enc xP)) (invCK 7 c))).isSome &&
        (expoK (mulK 7 (mulK 7 c (enc yP)) (invCK 7 c))).isSome) ||
      detK (expoK (mulK 7 (mulK 7 c (enc xP)) (invCK 7 c)))
        (expoK (mulK 7 (mulK 7 c (enc yP)) (invCK 7 c)))) 7 0 0 0 = true := by
    decide +kernel
  have hn : 7 ≤ 16 := by norm_num
  intro n hs hN
  rw [detOK_eq_detK, expo_eq_expoK, expo_eq_expoK]
  rw [normalises, expo_eq_expoK, expo_eq_expoK] at hN
  have h := walkK_sound hw n
  simp only [evenK_enc_eq_decide hn, hs, invCK_enc hn, mulK_enc hn, hN, decide_true, Bool.not_true,
    Bool.false_or] at h
  exact h

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
