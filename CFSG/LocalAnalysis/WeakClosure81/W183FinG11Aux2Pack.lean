module

public import CFSG.Permutation.FinPackEven6
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183Pack

open Equiv CFSG.Permutation.FinPack

@[expose] def idC6 : ℕ := 5517840

theorem enc_one6 : enc (1 : Perm (Fin 6)) = idC6 := by decide +kernel

@[expose] noncomputable def pwK (c k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) idC6 (fun _ a => mulK 6 a c) k

theorem enc_pow6 (σ : Perm (Fin 6)) (k : ℕ) : enc (σ ^ k) = pwK (enc σ) k := by
  induction k with
  | zero => rw [pow_zero, enc_one6]; rfl
  | succ k ih =>
    rw [pow_succ, enc_mul (by norm_num), ih]
    rfl

theorem pow_eq_one_iff6 (σ : Perm (Fin 6)) (k : ℕ) :
    σ ^ k = 1 ↔ Nat.beq (pwK (enc σ) k) idC6 = true := by
  rw [Nat.beq_eq, ← enc_pow6, ← enc_one6]
  exact ⟨fun h => by rw [h], fun h => enc_inj (by norm_num) h⟩

theorem pow_eq_one_iffA (g : alternatingGroup (Fin 6)) (k : ℕ) :
    g ^ k = 1 ↔ Nat.beq (pwK (enc (g : Perm (Fin 6))) k) idC6 = true := by
  rw [← pow_eq_one_iff6, ← Subgroup.coe_pow]
  exact ⟨fun h => by simp [h], fun h => Subtype.ext h⟩

theorem pc6_memA (g : alternatingGroup (Fin 6)) : pc6 (g : Perm (Fin 6)) ∈ evenCodes6 :=
  memK_iff.1 (pc6_mem_even g (Perm.mem_alternatingGroup.1 g.2))

@[expose] noncomputable def oddK (c : ℕ) : Bool :=
  !Nat.beq (pwK (lo6 c) 45) idC6 || Nat.beq (pwK (lo6 c) 3) idC6 || Nat.beq (pwK (lo6 c) 5) idC6

theorem oddK_all : allK oddK evenCodes6 = true := by decide +kernel

theorem odd_of_check (g : alternatingGroup (Fin 6)) (hg : g ^ 45 = 1) : g ^ 3 = 1 ∨ g ^ 5 = 1 := by
  have h1 := allK_iff.1 oddK_all _ (pc6_memA g)
  unfold oddK at h1
  rw [lo6_pc6, (pow_eq_one_iffA g 45).1 hg, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h1
  exact h1.imp (pow_eq_one_iffA g 3).2 (pow_eq_one_iffA g 5).2

@[expose] def conjL : List (Perm (Fin 6)) :=
  [swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4, swap 0 1 * swap 4 5,
    swap 0 1 * swap 3 4, swap 0 1 * swap 3 5, swap 0 1 * swap 2 3, swap 0 1 * swap 2 4,
    swap 0 1 * swap 2 5]

@[expose] def conjC : List ℕ :=
  [76016899138320, 55336630375440, 38779530462480, 76081071993345, 91542955180545, 57526812168705,
    92509322879745, 90383313941505, 39810071016705]

theorem conjL_codes : conjL.map pc6 = conjC := by decide +kernel

theorem conjL_even : ∀ k ∈ conjL, Perm.sign k = 1 := by decide +kernel

@[expose] noncomputable def invK (KC : List ℕ) (m c : ℕ) : Bool :=
  !Nat.beq (pwK (lo6 c) m) idC6 ||
    anyK (fun k => Nat.beq (mulK 6 (mulK 6 (lo6 k) (lo6 c)) (hi6 k)) (hi6 c)) KC

theorem conj_inv_of_check {m : ℕ} (h : allK (invK conjC m) evenCodes6 = true)
    (g : alternatingGroup (Fin 6)) (hg : g ^ m = 1) :
    ∃ k : alternatingGroup (Fin 6), k * g * k⁻¹ = g⁻¹ := by
  have h1 := allK_iff.1 h _ (pc6_memA g)
  unfold invK at h1
  rw [lo6_pc6, (pow_eq_one_iffA g m).1 hg, Bool.not_true, Bool.false_or] at h1
  obtain ⟨kc, hkc, hk⟩ := anyK_iff.1 h1
  rw [← conjL_codes, List.mem_map] at hkc
  obtain ⟨k, hkL, rfl⟩ := hkc
  have e := enc_mul (n := 6) (by norm_num)
  simp only [lo6_pc6, hi6_pc6, Nat.beq_eq] at hk
  rw [← e, ← e] at hk
  refine ⟨⟨k, Perm.mem_alternatingGroup.2 (conjL_even k hkL)⟩, Subtype.ext ?_⟩
  simpa using enc_inj (by norm_num) hk

theorem invK3_all : allK (invK conjC 3) evenCodes6 = true := by decide +kernel

theorem invK5_all : allK (invK conjC 5) evenCodes6 = true := by decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.W183Pack
