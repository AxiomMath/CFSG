module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.StandardType.GGFinModel

@[expose] def eps (p f : ℕ) : ℤ := if p ∣ 2 ^ f - 1 then 1 else -1

theorem eps_cases (p f : ℕ) : eps p f = 1 ∨ eps p f = -1 := by
  unfold eps
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem eps_eq_one_iff (p f : ℕ) : eps p f = 1 ↔ p ∣ 2 ^ f - 1 := by
  unfold eps
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd h1 h⟩

theorem eps_dvd {p f : ℕ} (h : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) :
    (p : ℤ) ∣ (2 : ℤ) ^ f - eps p f := by
  unfold eps
  split_ifs with h1
  · have h2 : ((2 ^ f - 1 : ℕ) : ℤ) = (2 : ℤ) ^ f - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [← h2]
    exact Int.natCast_dvd_natCast.mpr h1
  · have h3 : p ∣ 2 ^ f + 1 := h.resolve_left h1
    have h4 : ((2 ^ f + 1 : ℕ) : ℤ) = (2 : ℤ) ^ f - (-1) := by
      push_cast
      ring
    rw [← h4]
    exact Int.natCast_dvd_natCast.mpr h3

theorem eps_mul_pow_sub_one_dvd {p f : ℕ} (h : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) :
    (p : ℤ) ∣ eps p f * 2 ^ f - 1 := by
  have h1 := eps_dvd h
  rcases eps_cases p f with he | he
  · rw [he] at h1 ⊢
    have e : (1 : ℤ) * 2 ^ f - 1 = (2 : ℤ) ^ f - 1 := by ring
    rw [e]
    exact h1
  · rw [he] at h1 ⊢
    have e : (-1 : ℤ) * 2 ^ f - 1 = -((2 : ℤ) ^ f - (-1)) := by ring
    rw [e]
    exact (dvd_neg).2 h1

theorem not_dvd_pow_two_add_one_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ)
    (h : p ∣ 2 ^ f - 1) : ¬ p ∣ 2 ^ f + 1 := by
  intro h'
  have hf : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : p ∣ 2 := by
    have e : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rw [← e]
    exact Nat.dvd_sub h' h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem eps_eq_neg_one_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ)
    (h : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) : eps p f = -1 ↔ p ∣ 2 ^ f + 1 := by
  constructor
  · intro he
    by_contra hn
    have h1 : eps p f = 1 := (eps_eq_one_iff p f).2 (h.resolve_right hn)
    rw [he] at h1
    norm_num at h1
  · intro h3
    rcases eps_cases p f with he | he
    · exact absurd h3 (not_dvd_pow_two_add_one_of_dvd hp hp2 f ((eps_eq_one_iff p f).1 he))
    · exact he

theorem exists_zeta (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ∃ ζ : Lˣ, orderOf ζ = p := by
  have hne : (p : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L 2 p] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h).symm
  haveI : NeZero (p : L) := ⟨hne⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  refine ⟨(hζ.isUnit hp.ne_zero).unit, ?_⟩
  rw [← orderOf_units, IsUnit.unit_spec]
  exact hζ.eq_orderOf.symm

end CFSG.StandardType.GGFinModel
