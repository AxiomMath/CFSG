module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Ring.GeomSum

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

theorem two_pow_sub_one_dvd_iff {e a : ℕ} : 2 ^ e - 1 ∣ 2 ^ a - 1 ↔ e ∣ a := by
  refine ⟨fun h => ?_, fun ⟨q, hq⟩ => ?_⟩
  · have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 e a
    rw [Nat.gcd_eq_left h] at hg
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ Nat.gcd e a := Nat.one_le_two_pow
    have h3 : Nat.gcd e a = e := Nat.pow_right_injective le_rfl (by simp only; omega)
    exact Nat.gcd_eq_left_iff_dvd.mp h3
  · rw [hq, pow_mul]
    exact Nat.sub_one_dvd_pow_sub_one _ _

theorem prime_dvd_and_gcd_eq {e j p : ℕ} (hp : p.Prime) (he : 0 < e) (hjp : e ∣ j * p)
    (hj : ¬ e ∣ j) : p ∣ e ∧ Nat.gcd j e = e / p := by
  obtain ⟨j', e', hcop, hj', he'⟩ := Nat.exists_coprime j e
  have hg : 0 < Nat.gcd j e := Nat.gcd_pos_of_pos_right j he
  generalize Nat.gcd j e = g at hj' he' hg ⊢
  subst hj' he'
  have hdvd : e' ∣ j' * p :=
    Nat.dvd_of_mul_dvd_mul_right hg (by rwa [mul_right_comm] at hjp)
  rcases hp.eq_one_or_self_of_dvd e' (hcop.symm.dvd_of_dvd_mul_left hdvd) with h1 | h1
  · subst h1
    exact absurd (by rw [one_mul]; exact Dvd.intro_left _ rfl) hj
  · subst h1
    exact ⟨Dvd.intro _ rfl, by rw [Nat.mul_div_cancel_left _ hp.pos]⟩

theorem sum_two_pow_mul_sub_one (f p : ℕ) :
    (∑ k ∈ Finset.range p, 2 ^ (f * k)) * (2 ^ f - 1) = 2 ^ (f * p) - 1 := by
  have h := geom_sum_mul ((2 : ℤ) ^ f) p
  have key : ((∑ k ∈ Finset.range p, 2 ^ (f * k) : ℕ) : ℤ) * ((2 ^ f - 1 : ℕ) : ℤ) =
      ((2 ^ (f * p) - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub Nat.one_le_two_pow]
    simpa only [← pow_mul] using h
  exact_mod_cast key

theorem sum_two_pow_mul_modEq {f s p : ℕ} (hp : 1 < p) (hs : s.Coprime p) :
    ∑ k ∈ Finset.range p, 2 ^ (f * s * k) ≡ ∑ k ∈ Finset.range p, 2 ^ (f * k)
      [MOD 2 ^ (f * p) - 1] := by
  set n := 2 ^ (f * p) - 1 with hn
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  have h1 : (2 : ZMod n) ^ (f * p) = 1 := by
    have h := ZMod.natCast_self n
    rw [hn, Nat.cast_sub Nat.one_le_two_pow] at h
    push_cast at h
    exact sub_eq_zero.mp h
  have h2 : ∀ k, (2 : ZMod n) ^ (f * s * k) = 2 ^ (f * (s * k % p)) := by
    intro k
    have h := Nat.mod_add_div (s * k) p
    have he : f * s * k = f * (s * k % p) + f * p * (s * k / p) := by
      calc f * s * k = f * (s * k % p + p * (s * k / p)) := by rw [h, mul_assoc]
        _ = f * (s * k % p) + f * p * (s * k / p) := by ring
    rw [he, pow_add, pow_mul (2 : ZMod n) (f * p), h1, one_pow, mul_one]
  simp_rw [h2]
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hs hp
  refine Finset.sum_nbij' (fun k => s * k % p) (fun k => t * k % p) ?_ ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  · intro k _
    exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  · intro k hk
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, mul_comm t s, Nat.mul_mod, ht,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
  · intro k hk
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, ht,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hk)]
  · intro k _
    rfl

section Cyclic

variable {A : Type*} [Group A] [Finite A] [IsCyclic A]

theorem card_pow_eq_one_eq_gcd (k : ℕ) :
    Nat.card {x : A // x ^ k = 1} = Nat.gcd (Nat.card A) k := by
  let : CommGroup A := IsCyclic.commGroup
  rw [← IsCyclic.card_powMonoidHom_ker]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [MonoidHom.mem_ker])

theorem exists_pow_eq_of_pow_eq_one {d m k : ℕ} (hcard : Nat.card A = d * m)
    (hgcd : Nat.gcd (Nat.card A) k = d) {c : A} (hc : c ^ m = 1) : ∃ x : A, x ^ k = c := by
  let : CommGroup A := IsCyclic.commGroup
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hd : 0 < d := by
    rw [← hgcd]
    exact Nat.gcd_pos_of_pos_left k hpos
  obtain ⟨k', hk'⟩ : d ∣ k := hgcd ▸ Nat.gcd_dvd_right _ _
  have hle : (powMonoidHom k : A →* A).range ≤ (powMonoidHom m : A →* A).ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul, hk',
      show d * k' * m = Nat.card A * k' by rw [hcard]; ring, pow_mul, pow_card_eq_one',
      one_pow]
  have hm : m ∣ Nat.card A := ⟨d, by rw [hcard, mul_comm]⟩
  have hcard' : Nat.card (powMonoidHom m : A →* A).ker ≤
      Nat.card (powMonoidHom k : A →* A).range := by
    rw [IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right hm,
      hgcd, hcard, Nat.mul_div_cancel_left _ hd]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard'
  have hc' : c ∈ (powMonoidHom m : A →* A).ker := hc
  rw [← heq] at hc'
  obtain ⟨x, hx⟩ := hc'
  exact ⟨x, hx⟩

end Cyclic

section Group

variable {G : Type*} [Group G]

theorem pow_two_pow_eq_self_iff {x : G} {a : ℕ} : x ^ (2 ^ a) = x ↔ x ^ (2 ^ a - 1) = 1 := by
  rw [← pow_sub_one_mul (pow_ne_zero a two_ne_zero) x, mul_eq_right]

theorem inv_mul_pow_mul (x y : G) (n : ℕ) : y⁻¹ * x ^ n * y = (y⁻¹ * x * y) ^ n := by
  simpa using (conj_pow (a := y⁻¹) (b := x) (i := n)).symm

end Group

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
