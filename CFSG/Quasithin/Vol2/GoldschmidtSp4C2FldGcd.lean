module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

variable {k : Type} [Field k] [CharP k 2]

def frobFixed (m : ℕ) : Subfield k where
  carrier := {t | t ^ 2 ^ m = t}
  mul_mem' := fun {a b} (ha : a ^ 2 ^ m = a) (hb : b ^ 2 ^ m = b) =>
    show (a * b) ^ 2 ^ m = a * b by rw [mul_pow, ha, hb]
  one_mem' := show (1 : k) ^ 2 ^ m = 1 from one_pow _
  add_mem' := fun {a b} (ha : a ^ 2 ^ m = a) (hb : b ^ 2 ^ m = b) =>
    show (a + b) ^ 2 ^ m = a + b by rw [add_pow_char_pow, ha, hb]
  zero_mem' := show (0 : k) ^ 2 ^ m = 0 from zero_pow (pow_ne_zero m two_ne_zero)
  neg_mem' := fun {a} (ha : a ^ 2 ^ m = a) =>
    show (-a) ^ 2 ^ m = -a by rw [CharTwo.neg_eq, ha]
  inv_mem' := fun {a} (ha : a ^ 2 ^ m = a) =>
    show a⁻¹ ^ 2 ^ m = a⁻¹ by rw [inv_pow, ha]

theorem mem_frobFixed {m : ℕ} {t : k} : t ∈ frobFixed (k := k) m ↔ t ^ 2 ^ m = t := Iff.rfl

theorem exists_subfield_of_gcd [Finite k] {n : ℕ} (hn : Nat.card k = 2 ^ n) (s : ℕ) :
    ∃ F₀ : Subfield k, Nat.card F₀ = 2 ^ Nat.gcd (2 * s + 1) n ∧
      ∀ t : k, t ≠ 0 → (t ^ (2 ^ (2 * s + 1) - 1) = 1 ↔ t ∈ F₀) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  set e := 2 ^ (2 * s + 1) - 1 with he
  have hpos : 0 < 2 ^ (2 * s + 1) := Nat.two_pow_pos _
  have hqe : 2 ^ (2 * s + 1) = e + 1 := by omega
  have hiff : ∀ t : k, t ≠ 0 → (t ^ e = 1 ↔ t ∈ frobFixed (k := k) (2 * s + 1)) := by
    intro t ht
    rw [mem_frobFixed, hqe, pow_succ]
    constructor
    · intro h
      rw [h, one_mul]
    · intro h
      have : t ^ e * t = 1 * t := by rw [h, one_mul]
      exact mul_right_cancel₀ ht this
  refine ⟨frobFixed (2 * s + 1), ?_, hiff⟩
  have hcu : Nat.card kˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, hn]
  have hker := IsCyclic.card_powMonoidHom_ker kˣ e
  have hgcd : (Nat.card kˣ).gcd e = 2 ^ Nat.gcd (2 * s + 1) n - 1 := by
    rw [hcu, he, Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_comm]
  rw [hgcd] at hker
  set K : Finset kˣ := Finset.univ.filter fun u : kˣ => u ^ e = 1 with hK
  have hKcard : K.card = 2 ^ Nat.gcd (2 * s + 1) n - 1 := by
    rw [← hker, Nat.card_eq_fintype_card, Fintype.card_subtype, hK]
    congr 1
  have hA : (Finset.univ.filter fun t : k => t ∈ frobFixed (k := k) (2 * s + 1)) =
      insert 0 (K.image Units.val) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image,
      hK]
    by_cases ht : t = 0
    · subst ht
      simp only [true_or, iff_true]
      exact (frobFixed (k := k) (2 * s + 1)).zero_mem
    · constructor
      · intro h
        refine Or.inr ⟨Units.mk0 t ht, Units.ext ?_, rfl⟩
        simpa using (hiff t ht).mpr h
      · rintro (h | ⟨u, hu, rfl⟩)
        · exact absurd h ht
        · exact (hiff _ u.ne_zero).mp (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
  have hnot : (0 : k) ∉ K.image Units.val := by
    simp only [Finset.mem_image, not_exists, not_and]
    exact fun u _ => u.ne_zero
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hA, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ Units.val_injective, hKcard]
  have : 1 ≤ 2 ^ Nat.gcd (2 * s + 1) n := Nat.one_le_two_pow
  omega

end CFSG.Quasithin.Ch3E213M.Sp4C2
