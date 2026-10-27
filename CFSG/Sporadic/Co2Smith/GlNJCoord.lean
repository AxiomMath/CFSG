module

public import CFSG.Sporadic.Co2Smith.GlWCheck

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Coord


@[expose] noncomputable def jcFold (m : ℕ) (l : List ℕ) : K :=
  l.foldr (fun i acc => if m.testBit i then jcB i * acc else acc) 1

theorem jcFold_mem (m : ℕ) (l : List ℕ) (hl : ∀ i ∈ l, i < 10) : jcFold m l ∈ Jc :=
  foldr_bits_mem m l hl

theorem jcFold_xor (a b : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 10) → jcFold (a ^^^ b) l = jcFold a l * jcFold b l
  | [], _ => by simp [jcFold]
  | i :: l, hl => by
    have hi : i < 10 := hl i List.mem_cons_self
    have hl' : ∀ j ∈ l, j < 10 := fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have ih := jcFold_xor a b l hl'
    have hca : jcB i * jcFold a l = jcFold a l * jcB i :=
      Jc_comm (jcB_mem hi) (jcFold_mem a l hl')
    have e : ∀ m, jcFold m (i :: l) = (if m.testBit i then jcB i * jcFold m l else jcFold m l) :=
      fun m => rfl
    rw [e, e, e, Nat.testBit_xor, ih]
    rcases Bool.eq_false_or_eq_true (a.testBit i) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (b.testBit i) with hb | hb <;> rw [ha, hb]
    · show jcFold a l * jcFold b l = jcB i * jcFold a l * (jcB i * jcFold b l)
      calc jcFold a l * jcFold b l = jcFold a l * (jcB i * jcB i) * jcFold b l := by
            rw [jcB_mul_self hi, mul_one]
        _ = (jcFold a l * jcB i) * (jcB i * jcFold b l) := by group
        _ = jcB i * jcFold a l * (jcB i * jcFold b l) := by rw [hca]
    · show jcB i * (jcFold a l * jcFold b l) = jcB i * jcFold a l * jcFold b l
      rw [mul_assoc]
    · show jcB i * (jcFold a l * jcFold b l) = jcFold a l * (jcB i * jcFold b l)
      rw [← mul_assoc, ← mul_assoc, hca]
    · rfl

theorem jcElt_eq_jcFold (m : ℕ) : jcElt m = jcFold m (List.range 10) := rfl

theorem jcElt_xor (a b : ℕ) : jcElt (a ^^^ b) = jcElt a * jcElt b :=
  jcFold_xor a b (List.range 10) fun _ hi => List.mem_range.1 hi

theorem jcElt_zero : jcElt 0 = 1 := by
  simp [jcElt]

theorem jcElt_mul_self (a : ℕ) : jcElt a * jcElt a = 1 := by
  rw [← jcElt_xor, Nat.xor_self, jcElt_zero]

theorem jcElt_inv (a : ℕ) : (jcElt a)⁻¹ = jcElt a :=
  inv_eq_of_mul_eq_one_right (jcElt_mul_self a)

theorem jcElt_comm (a b : ℕ) : jcElt a * jcElt b = jcElt b * jcElt a :=
  Jc_comm (jcElt_mem a) (jcElt_mem b)

theorem jcFold_two_pow {i : ℕ} :
    ∀ l : List ℕ, l.Nodup → jcFold (2 ^ i) l = if i ∈ l then jcB i else 1
  | [], _ => by simp [jcFold]
  | j :: l, hl => by
    have ih := jcFold_two_pow (i := i) l (List.nodup_cons.1 hl).2
    have e : jcFold (2 ^ i) (j :: l) =
        (if (2 ^ i).testBit j then jcB j * jcFold (2 ^ i) l else jcFold (2 ^ i) l) := rfl
    rw [e, ih, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij
      have hn : i ∉ l := (List.nodup_cons.1 hl).1
      simp [hn]
    · simp [hij]

theorem jcElt_two_pow {i : ℕ} (hi : i < 10) : jcElt (2 ^ i) = jcB i := by
  rw [jcElt_eq_jcFold, jcFold_two_pow _ List.nodup_range, ite_eq_left (List.mem_range.2 hi)]

theorem exists_coord {x : K} (hx : x ∈ Jc) : ∃ m < 1024, jcElt m = x := by
  refine closure_induction (p := fun x _ => ∃ m < 1024, jcElt m = x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, rfl⟩
    exact ⟨2 ^ (i : ℕ), Nat.pow_lt_pow_right (by norm_num) i.isLt |>.trans_eq (by norm_num),
      jcElt_two_pow i.isLt⟩
  · exact ⟨0, by norm_num, jcElt_zero⟩
  · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ^^^ b, Nat.xor_lt_two_pow (n := 10) ha hb, jcElt_xor a b⟩
  · rintro _ _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, (jcElt_inv a).symm⟩

end Coord

end CFSG.Sporadic.Co2Smith
