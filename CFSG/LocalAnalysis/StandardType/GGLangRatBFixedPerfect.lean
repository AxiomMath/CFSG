module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.LangRat

open CFSG.RankThree.Classical2
open scoped MatrixGroups

private theorem langRatBQ_isAlgClosure_subfield {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (hAlg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ 2 ^ n = c) (K : Subfield L) :
    IsAlgClosure ↥K L := by
  rw [isAlgClosure_iff]
  refine ⟨inferInstance, Algebra.IsAlgebraic.mk fun c => ?_⟩
  obtain ⟨n, hn, hc⟩ := hAlg c
  by_cases hc0 : c = 0
  · rw [hc0]
    exact isAlgebraic_zero
  · have hm : 1 < 2 ^ n := Nat.one_lt_pow hn.ne' (by norm_num)
    refine IsAlgebraic.of_pow (r := c) (n := 2 ^ n - 1) (by omega) ?_
    have hpow : c ^ (2 ^ n - 1) = 1 := by
      have h1 : c ^ (2 ^ n - 1) * c = c := by
        rw [← pow_succ, Nat.sub_add_cancel (le_of_lt hm), hc]
      exact mul_right_cancel₀ hc0 (by rw [one_mul]; exact h1)
    rw [hpow]
    exact isAlgebraic_one

private theorem langRatBQ_card_fixedField {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {f : ℕ} (hf : 1 ≤ f) (K : Subfield L) (hmem : ∀ c : L, c ∈ K ↔ c ^ 2 ^ f = c) :
    Nat.card ↥K = 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← natCard_setOf_pow_eq_self (Ω := L) (ℓ := 2) (e := f) (by omega)]
  exact Nat.card_congr (Equiv.subtypeEquivRight hmem)

theorem langRatB_fixed_perfect_split
    {L : Type} [Field L] [IsAlgClosed L]
    (hAlg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ 2 ^ n = c) {f : ℕ} (hf : 1 ≤ f) {ν : ℕ} (hν : 3 ≤ ν)
    (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ) (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hΦ' : ∀ (x y : Fin ν) (hxy : x ≠ y) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hxy t) : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = 1 + Matrix.single (π x) (π y) ((β x y : L) * t ^ 2 ^ f)) :
    Group.IsPerfect ↥(fixSubgroup Φ') := by
  classical
  haveI : CharP L 2 := by
    obtain ⟨n, hn, h⟩ := hAlg (-1)
    have hev : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, hn.ne'⟩
    have h1 : (1 : L) = -1 := (Even.neg_one_pow hev).symm.trans h
    exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by linear_combination h1)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subfield L := RingHom.eqLocusField (iterateFrobenius L 2 f) (RingHom.id L)
  have hmem : ∀ c : L, c ∈ K ↔ c ^ 2 ^ f = c := fun c => by
    change iterateFrobenius L 2 f c = c ↔ c ^ 2 ^ f = c
    simp only [iterateFrobenius_def]
  have hk : Nat.card ↥K = 2 ^ f := langRatBQ_card_fixedField hf K hmem
  haveI : IsAlgClosure ↥K L := langRatBQ_isAlgClosure_subfield hAlg K
  obtain ⟨-, -, -, hqs, -, -⟩ :=
    sln_root_permuting_frobenius_fixed_split (k := ↥K) (Ω := L) (n := ν) (ℓ := 2) (f := f)
      Nat.prime_two hf hk hν π Φ' β (fun x y hxy t => hΦ' x y hxy t)
  exact hqs.1

theorem langRatB_fixed_perfect_unitary
    {L : Type} [Field L] [IsAlgClosed L]
    (hAlg : ∀ c : L, ∃ n : ℕ, 0 < n ∧ c ^ 2 ^ n = c) {f : ℕ} (hf : 1 ≤ f) {ν : ℕ} (hν : 3 ≤ ν)
    (hne : (ν, 2 ^ f) ≠ (3, 2))
    (π : Equiv.Perm (Fin ν)) (β : Fin ν → Fin ν → Lˣ) (Φ' : SL(ν, L) ≃* SL(ν, L))
    (hΦ' : ∀ (x y : Fin ν) (hxy : x ≠ y) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hxy t) : SL(ν, L)) :
        Matrix (Fin ν) (Fin ν) L) = 1 + Matrix.single (π y) (π x) ((β x y : L) * t ^ 2 ^ f)) :
    Group.IsPerfect ↥(fixSubgroup Φ') := by
  classical
  haveI : CharP L 2 := by
    obtain ⟨n, hn, h⟩ := hAlg (-1)
    have hev : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, hn.ne'⟩
    have h1 : (1 : L) = -1 := (Even.neg_one_pow hev).symm.trans h
    exact CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (by linear_combination h1)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K : Subfield L := RingHom.eqLocusField (iterateFrobenius L 2 f) (RingHom.id L)
  have hmem : ∀ c : L, c ∈ K ↔ c ^ 2 ^ f = c := fun c => by
    change iterateFrobenius L 2 f c = c ↔ c ^ 2 ^ f = c
    simp only [iterateFrobenius_def]
  have hk : Nat.card ↥K = 2 ^ f := langRatBQ_card_fixedField hf K hmem
  haveI : IsAlgClosure ↥K L := langRatBQ_isAlgClosure_subfield hAlg K
  obtain ⟨-, -, -, hbig, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary (k := ↥K) (Ω := L) (n := ν) (ℓ := 2) (f := f)
      Nat.prime_two hf hk hν π Φ' β (fun x y hxy t => hΦ' x y hxy t)
  exact (hbig hne).1.1

end CFSG.StandardType.LangRat
