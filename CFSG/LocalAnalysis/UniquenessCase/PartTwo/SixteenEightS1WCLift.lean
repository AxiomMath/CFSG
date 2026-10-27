module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup Pointwise

theorem s16w_exists_permuting_three_subgroup {A Q : Type*} [Group A] [Finite A] [Group Q]
    (φ : A →* Q) {T : Subgroup A} (hT2 : IsPGroup 2 ↥T) (hTsyl : ¬ 2 ∣ T.index)
    (hker : IsPGroup 2 ↥φ.ker) {J : Subgroup Q} (hTJ : T.map φ ≤ J) (hJ : J ≤ φ.range) {a : ℕ}
    (hJcard : Nat.card ↥J = 3 ^ a * Nat.card ↥(T.map φ)) :
    ∃ Y : Subgroup A, IsPGroup 3 ↥Y ∧ Nat.card ↥Y = 3 ^ a ∧
      (Y : Set A) * (T : Set A) = (T : Set A) * (Y : Set A) ∧ Y.map φ ≤ J ∧
      Function.Injective (φ.comp Y.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let JA : Subgroup A := J.comap φ
  have hKT : φ.ker ≤ T := by
    have h := IsPGroup.le_sylow_of_normal hker (hT2.toSylow hTsyl)
    simpa using h
  have hKJA : φ.ker ≤ JA := by
    intro k hk
    show φ k ∈ J
    rw [MonoidHom.mem_ker.mp hk]
    exact J.one_mem
  have hTJA : T ≤ JA := Subgroup.map_le_iff_le_comap.mp hTJ
  have hJAmap : JA.map φ = J := by
    show (J.comap φ).map φ = J
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hJ]
  have hJA_ker : Nat.card ↥φ.ker * Nat.card ↥J = Nat.card ↥JA := by
    have h := Subgroup.card_ker_mul_card_of_surjective (φ.subgroupMap_surjective JA)
    rw [Subgroup.ker_subgroupMap] at h
    rw [show Nat.card ↥(φ.ker.subgroupOf JA) = Nat.card ↥φ.ker from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJA).toEquiv, hJAmap] at h
    exact h
  have hKT_card : Nat.card ↥φ.ker * Nat.card ↥(T.map φ) = Nat.card ↥T := by
    have h := Subgroup.card_ker_mul_card_of_surjective (φ.subgroupMap_surjective T)
    rw [Subgroup.ker_subgroupMap] at h
    rw [show Nat.card ↥(φ.ker.subgroupOf T) = Nat.card ↥φ.ker from
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKT).toEquiv] at h
    exact h
  have hJA_card : Nat.card ↥JA = 3 ^ a * Nat.card ↥T := by
    calc Nat.card ↥JA = Nat.card ↥φ.ker * Nat.card ↥J := hJA_ker.symm
      _ = Nat.card ↥φ.ker * (3 ^ a * Nat.card ↥(T.map φ)) := by rw [hJcard]
      _ = 3 ^ a * (Nat.card ↥φ.ker * Nat.card ↥(T.map φ)) := by ring
      _ = 3 ^ a * Nat.card ↥T := by rw [hKT_card]
  obtain ⟨b, hb⟩ := hT2.exists_card_eq
  have h3ndvd : ¬ 3 ∣ 2 ^ b := fun h3 =>
    absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hfac : Nat.factorization (Nat.card ↥JA) 3 = a := by
    rw [hJA_card, hb,
      Nat.factorization_mul (pow_ne_zero a (by norm_num : (3 : ℕ) ≠ 0))
        (pow_ne_zero b (by norm_num : (2 : ℕ) ≠ 0)),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd h3ndvd, add_zero]
  let P : Sylow 3 ↥JA := Classical.arbitrary _
  have hPcard : Nat.card ↥P = 3 ^ a := by
    change Nat.card ↥(P : Subgroup ↥JA) = 3 ^ a
    rw [P.card_eq_multiplicity, hfac]
  let Y : Subgroup A := (P : Subgroup ↥JA).map JA.subtype
  have hYle : Y ≤ JA := by
    change (P : Subgroup ↥JA).map JA.subtype ≤ JA
    exact Subgroup.map_subtype_le (H := JA) P
  have hYcard : Nat.card ↥Y = 3 ^ a := (Subgroup.card_subtype JA P).trans hPcard
  have hcopYT : Nat.Coprime (Nat.card ↥Y) (Nat.card ↥T) := by
    rw [hYcard, hb]
    exact Nat.coprime_pow_primes a b Nat.prime_three Nat.prime_two (by norm_num)
  have hinf : Y ⊓ T = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopYT)
  have hYcard' : Nat.card ↥(Y.subgroupOf JA) = 3 ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv, hYcard]
  have hTcard' : Nat.card ↥(T.subgroupOf JA) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJA).toEquiv
  have hprod : Nat.card ↥(Y.subgroupOf JA) * Nat.card ↥(T.subgroupOf JA) = Nat.card ↥JA := by
    rw [hYcard', hTcard', ← hJA_card]
  have hcop : Nat.Coprime (Nat.card ↥(Y.subgroupOf JA)) (Nat.card ↥(T.subgroupOf JA)) := by
    rw [hYcard', hTcard', hb]
    exact Nat.coprime_pow_primes a b Nat.prime_three Nat.prime_two (by norm_num)
  have hcompl : Subgroup.IsComplement' (Y.subgroupOf JA) (T.subgroupOf JA) :=
    Subgroup.isComplement'_of_coprime hprod hcop
  refine ⟨Y, P.isPGroup'.map JA.subtype, hYcard, ?_, ?_, ?_⟩
  · have himgY : JA.subtype '' (Y.subgroupOf JA : Set ↥JA) = (Y : Set A) := by
      rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hYle]
    have himgT : JA.subtype '' (T.subgroupOf JA : Set ↥JA) = (T : Set A) := by
      rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hTJA]
    have himgu : JA.subtype '' (Set.univ : Set ↥JA) = (JA : Set A) := by
      rw [Set.image_univ, ← MonoidHom.coe_range, Subgroup.range_subtype]
    have hYT : (Y : Set A) * (T : Set A) = (JA : Set A) := by
      have h := congrArg (Set.image JA.subtype) hcompl.mul_eq
      rw [Set.image_mul JA.subtype, himgY, himgT, himgu] at h
      exact h
    have hTY : (T : Set A) * (Y : Set A) = (JA : Set A) := by
      have h := congrArg (Set.image JA.subtype) hcompl.symm.mul_eq
      rw [Set.image_mul JA.subtype, himgT, himgY, himgu] at h
      exact h
    exact hYT.trans hTY.symm
  · calc Y.map φ ≤ JA.map φ := Subgroup.map_mono hYle
      _ = J := hJAmap
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hyK : (y : A) ∈ φ.ker := hy
    have hyT : (y : A) ∈ T := hKT hyK
    have hmem : (y : A) ∈ Y ⊓ T := ⟨y.2, hyT⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
