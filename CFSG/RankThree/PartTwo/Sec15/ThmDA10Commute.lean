module

public import CFSG.GH74.Uniqueness.SU.SU13TA3PermE

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem thmD_exists_pow {c x : Perm (Fin 10)} (S : Finset (Fin 10)) (b0 : Fin 10)
    (hb : x b0 ∈ S) (hS : ∀ v ∈ S, ∃ m : Fin 3, (c ^ (m : ℕ)) b0 = v) (h : Commute x c) :
    ∃ i : Fin 3, ∀ y ∈ S, x y = (c ^ (i : ℕ)) y := by
  obtain ⟨i, hi⟩ := hS (x b0) hb
  refine ⟨i, fun y hy => ?_⟩
  obtain ⟨m, hm⟩ := hS y hy
  rw [← hm, apply_pow_of_commute h, ← hi, ← Perm.mul_apply, ← Perm.mul_apply, ← pow_add,
    ← pow_add, add_comm]

theorem thmD_fixed {t u : Perm (Fin 10)} (hu : Commute t u) {x : Fin 10} (hx : u x = x) :
    u (t x) = t x := by
  have h : t (u x) = u (t x) :=
    congrFun (congrArg (fun f : Perm (Fin 10) => (f : Fin 10 → Fin 10)) hu.eq) x
  rw [hx] at h
  exact h.symm

theorem thmD_fix_one : ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 → ∀ x : Fin 10,
    toP i j 0 x = x ↔ x ∈ ({6, 7, 8, 9} : Finset (Fin 10)) := by decide

theorem thmD_fix_two : ∀ j k : Fin 3, j ≠ 0 → k ≠ 0 → ∀ x : Fin 10,
    toP 0 j k x = x ↔ x ∈ ({0, 1, 2, 9} : Finset (Fin 10)) := by decide

theorem thmD_fix_three : ∀ i k : Fin 3, i ≠ 0 → k ≠ 0 → ∀ x : Fin 10,
    toP i 0 k x = x ↔ x ∈ ({3, 4, 5, 9} : Finset (Fin 10)) := by decide

theorem thmD_orbit_a : ∀ i j : Fin 3, i ≠ 0 → ∀ v ∈ ({0, 1, 2} : Finset (Fin 10)),
    ∃ m : Fin 3, (toP i j 0 ^ (m : ℕ)) 0 = v := by decide

theorem thmD_orbit_b : ∀ i j : Fin 3, j ≠ 0 → ∀ v ∈ ({3, 4, 5} : Finset (Fin 10)),
    ∃ m : Fin 3, (toP i j 0 ^ (m : ℕ)) 3 = v := by decide

theorem thmD_orbit_c : ∀ j k : Fin 3, k ≠ 0 → ∀ v ∈ ({6, 7, 8} : Finset (Fin 10)),
    ∃ m : Fin 3, (toP 0 j k ^ (m : ℕ)) 6 = v := by decide

theorem thmD_pow_a : ∀ i j n : Fin 3, ∀ y ∈ ({0, 1, 2} : Finset (Fin 10)),
    (toP i j 0 ^ (n : ℕ)) y = (pa ^ ((i * n : Fin 3) : ℕ)) y := by decide

theorem thmD_pow_b : ∀ i j n : Fin 3, ∀ y ∈ ({3, 4, 5} : Finset (Fin 10)),
    (toP i j 0 ^ (n : ℕ)) y = (pb ^ ((j * n : Fin 3) : ℕ)) y := by decide

theorem thmD_pow_c : ∀ j k n : Fin 3, ∀ y ∈ ({6, 7, 8} : Finset (Fin 10)),
    (toP 0 j k ^ (n : ℕ)) y = (pc ^ ((k * n : Fin 3) : ℕ)) y := by decide

theorem thmD_nine : ∀ x : Fin 10, x ∈ ({6, 7, 8, 9} : Finset (Fin 10)) →
    x ∈ ({0, 1, 2, 9} : Finset (Fin 10)) → x = 9 := by decide

theorem thmD_block_a : ∀ x : Fin 10, x ∈ ({0, 1, 2, 9} : Finset (Fin 10)) → x ≠ 9 →
    x ∈ ({0, 1, 2} : Finset (Fin 10)) := by decide

theorem thmD_block_b : ∀ x : Fin 10, x ∈ ({3, 4, 5, 9} : Finset (Fin 10)) → x ≠ 9 →
    x ∈ ({3, 4, 5} : Finset (Fin 10)) := by decide

theorem thmD_block_c : ∀ x : Fin 10, x ∈ ({6, 7, 8, 9} : Finset (Fin 10)) → x ≠ 9 →
    x ∈ ({6, 7, 8} : Finset (Fin 10)) := by decide

theorem thmD_cover : ∀ y : Fin 10, y ∈ ({0, 1, 2} : Finset (Fin 10)) ∨
    y ∈ ({3, 4, 5} : Finset (Fin 10)) ∨ y ∈ ({6, 7, 8} : Finset (Fin 10)) ∨ y = 9 := by decide

theorem exists_toP_of_commute_three (i₁ j₁ j₂ k₂ i₃ k₃ : Fin 3)
    (hi₁ : i₁ ≠ 0) (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) (hk₂ : k₂ ≠ 0) (hi₃ : i₃ ≠ 0) (hk₃ : k₃ ≠ 0)
    (t : Perm (Fin 10)) (h₁ : Commute t (toP i₁ j₁ 0)) (h₂ : Commute t (toP 0 j₂ k₂))
    (h₃ : Commute t (toP i₃ 0 k₃)) : ∃ i j k : Fin 3, t = toP i j k := by
  have ht9 : t 9 = 9 :=
    thmD_nine _
      ((thmD_fix_one i₁ j₁ hi₁ hj₁ (t 9)).mp (thmD_fixed h₁ (toP_apply_nine i₁ j₁ 0)))
      ((thmD_fix_two j₂ k₂ hj₂ hk₂ (t 9)).mp (thmD_fixed h₂ (toP_apply_nine 0 j₂ k₂)))
  have hne : ∀ x : Fin 10, x ≠ 9 → t x ≠ 9 :=
    fun x hx h => hx (t.injective (h.trans ht9.symm))
  have ht0 : t 0 ∈ ({0, 1, 2} : Finset (Fin 10)) :=
    thmD_block_a _
      ((thmD_fix_two j₂ k₂ hj₂ hk₂ (t 0)).mp
        (thmD_fixed h₂ ((thmD_fix_two j₂ k₂ hj₂ hk₂ 0).mpr (by decide))))
      (hne 0 (by decide))
  have ht3 : t 3 ∈ ({3, 4, 5} : Finset (Fin 10)) :=
    thmD_block_b _
      ((thmD_fix_three i₃ k₃ hi₃ hk₃ (t 3)).mp
        (thmD_fixed h₃ ((thmD_fix_three i₃ k₃ hi₃ hk₃ 3).mpr (by decide))))
      (hne 3 (by decide))
  have ht6 : t 6 ∈ ({6, 7, 8} : Finset (Fin 10)) :=
    thmD_block_c _
      ((thmD_fix_one i₁ j₁ hi₁ hj₁ (t 6)).mp
        (thmD_fixed h₁ ((thmD_fix_one i₁ j₁ hi₁ hj₁ 6).mpr (by decide))))
      (hne 6 (by decide))
  obtain ⟨n₁, hA⟩ := thmD_exists_pow (c := toP i₁ j₁ 0) (x := t) ({0, 1, 2} : Finset (Fin 10))
    0 ht0 (thmD_orbit_a i₁ j₁ hi₁) h₁
  obtain ⟨n₂, hB⟩ := thmD_exists_pow (c := toP i₁ j₁ 0) (x := t) ({3, 4, 5} : Finset (Fin 10))
    3 ht3 (thmD_orbit_b i₁ j₁ hj₁) h₁
  obtain ⟨n₃, hC⟩ := thmD_exists_pow (c := toP 0 j₂ k₂) (x := t) ({6, 7, 8} : Finset (Fin 10))
    6 ht6 (thmD_orbit_c j₂ k₂ hk₂) h₂
  refine ⟨i₁ * n₁, j₁ * n₂, k₂ * n₃, Perm.ext fun y => ?_⟩
  rcases thmD_cover y with hy | hy | hy | rfl
  · rw [hA y hy, thmD_pow_a i₁ j₁ n₁ y hy, toP_apply_a (i₁ * n₁) (j₁ * n₂) (k₂ * n₃) y hy]
  · rw [hB y hy, thmD_pow_b i₁ j₁ n₂ y hy, toP_apply_b (i₁ * n₁) (j₁ * n₂) (k₂ * n₃) y hy]
  · rw [hC y hy, thmD_pow_c j₂ k₂ n₃ y hy, toP_apply_c (i₁ * n₁) (j₁ * n₂) (k₂ * n₃) y hy]
  · rw [ht9, toP_apply_nine]

end CFSG.RankThree.PartTwo.Sec15.ThmD
