module

public import CFSG.Milestones.ASVolI.A2
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofCrossUnit
import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Dict
import CFSG.Timmesfeld.Orders.ClassicalLinearThree
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofHighWit

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec21.Item223CensusResProof CFSG.Timmesfeld.ClassicalOrders

variable {n m : ℕ}

private theorem even_two_pow_pow {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Even ((2 ^ n) ^ k) :=
  Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by omega⟩

private theorem odd_two_pow_pow_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Odd ((2 ^ n) ^ k - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) (even_two_pow_pow hn hk) odd_one

private theorem padicValNat_two_cube_mul {n : ℕ} (hn : 1 ≤ n) {s : ℕ} (hs : Odd s) :
    padicValNat 2 ((2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * s)) = 3 * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq3 : (2 ^ n) ^ 3 ≠ 0 := pow_ne_zero _ (by positivity)
  have hodd := odd_two_pow_pow_sub_one hn (by norm_num : 1 ≤ 2)
  have hq21 : (2 ^ n) ^ 2 - 1 ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hodd)
  have hs0 : s ≠ 0 := fun h => Nat.not_odd_zero (h ▸ hs)
  rw [padicValNat.mul hq3 (mul_ne_zero hq21 hs0), padicValNat.mul hq21 hs0,
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat,
    padicValNat.eq_zero_of_not_dvd hs.not_two_dvd_nat, add_zero, add_zero]
  rw [← pow_mul, Nat.mul_comm, padicValNat.prime_pow]

theorem padicValNat_two_card_psu {K : Type} [Field K] (hu : UnitaryFieldData 2 n K) :
    padicValNat 2 (Nat.card (unitaryPSU hu 3)) = 3 * n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hu.finite
  have hcard := card_unitaryPSU_three_mul hu
  rw [card_unitarySU_three' hu, mul_assoc] at hcard
  have hM0 : Nat.card (unitaryPSU hu 3) ≠ 0 := Nat.card_pos.ne'
  have hg0 : Nat.gcd 3 (2 ^ n + 1) ≠ 0 := gcd_ne_zero_of_left (by norm_num)
  have hgz : padicValNat 2 (Nat.gcd 3 (2 ^ n + 1)) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd ?_
    intro h2dvd
    exact absurd (h2dvd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))) (by norm_num)
  have hmul : padicValNat 2 (Nat.card (unitaryPSU hu 3) * Nat.gcd 3 (2 ^ n + 1)) =
      padicValNat 2 (Nat.card (unitaryPSU hu 3)) := by
    rw [padicValNat.mul hM0 hg0, hgz, add_zero]
  rw [hcard, padicValNat_two_cube_mul hu.one_le
    (even_two_pow_pow hu.one_le (by norm_num : 1 ≤ 3)).add_one] at hmul
  exact hmul.symm

theorem padicValNat_two_card_psl {K : Type} [Field K] [Finite K] {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (hm : 1 ≤ m) :
    padicValNat 2 (Nat.card (StatedProj (StatedSL 3 K))) = 3 * m := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := card_psl_three_mul_gcd (K := K)
  rw [hK] at hcard
  have hM0 : Nat.card (StatedProj (StatedSL 3 K)) ≠ 0 := Nat.card_pos.ne'
  have hg0 : Nat.gcd 3 (2 ^ m - 1) ≠ 0 := gcd_ne_zero_of_left (by norm_num)
  have hgz : padicValNat 2 (Nat.gcd 3 (2 ^ m - 1)) = 0 := by
    refine padicValNat.eq_zero_of_not_dvd ?_
    intro h2dvd
    exact absurd (h2dvd.trans (Nat.gcd_dvd_left 3 (2 ^ m - 1))) (by norm_num)
  have hmul : padicValNat 2 (Nat.card (StatedProj (StatedSL 3 K)) * Nat.gcd 3 (2 ^ m - 1)) =
      padicValNat 2 (Nat.card (StatedProj (StatedSL 3 K))) := by
    rw [padicValNat.mul hM0 hg0, hgz, add_zero]
  rw [hcard, padicValNat_two_cube_mul hm (odd_two_pow_pow_sub_one hm (by norm_num))] at hmul
  exact hmul.symm

private theorem isConjByGL_of_isProjConjAut {q : ℕ} {F : Type} [Field F] [Finite F]
    {c : GL (Fin 3) F} {φ : MulAut (StatedProj (StatedSU 3 q F))}
    (hc : CFSG.ASVolI.ChA.IsProjConjAut (StatedSU 3 q F) c φ) :
    CFSG.HardMathSupport.Solomon.LocalBalance.IsConjByGL (StatedSU 3 q F) φ := by
  have hmap : (StatedSU 3 q F).map (MulAut.conj c).toMonoidHom ≤ StatedSU 3 q F := by
    rintro _ ⟨y, hy, rfl⟩
    change c * y * c⁻¹ ∈ StatedSU 3 q F
    rw [← (hc ⟨y, hy⟩).choose_spec.1]
    exact (hc ⟨y, hy⟩).choose.2
  have hnorm : c ∈ Subgroup.normalizer (StatedSU 3 q F : Set (GL (Fin 3) F)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulAut.conj c).injective])
  refine ⟨c, hnorm, ?_⟩
  intro A A' hA'
  let B : ↥(StatedSU 3 q F) := (hc A).choose
  have hB : (B : GL (Fin 3) F) = c * (A : GL (Fin 3) F) * c⁻¹ := (hc A).choose_spec.1
  have hφB : φ (QuotientGroup.mk A) = QuotientGroup.mk B := (hc A).choose_spec.2
  have hBA : B = A' := Subtype.ext (hB.trans hA'.symm)
  rw [hφB, hBA]

theorem exists_unitaryIsom3_of_isProjConjAut {K₁ : Type} [Field K₁]
    (hu₁ : UnitaryFieldData 2 m K₁) (hm : 2 ≤ m)
    {X : Type} [Group X] {e₁ : X ≃* StatedProj (StatedSU 3 (2 ^ m) K₁)}
    {c : GL (Fin 3) K₁} {ψ : MulAut X}
    (hc : CFSG.ASVolI.ChA.IsProjConjAut (StatedSU 3 (2 ^ m) K₁) c (MulAut.congr e₁ ψ)) :
    ∃ A : unitaryIsom3 hu₁,
      MulAut.congr (e₁.trans (unitaryPSUEquiv hu₁ (by norm_num : 1 ≤ 3)).symm) ψ =
        psuConj hu₁ A := by
  haveI := hu₁.finite
  have hq : 2 < 2 ^ m :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
  have hconj := isConjByGL_of_isProjConjAut (q := 2 ^ m) (F := K₁) hc
  obtain ⟨A, hA⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.AutL3.congr_psuO_mem_psuConj_range
      hu₁ hq (φ := MulAut.congr e₁ ψ) hconj
  refine ⟨A, ?_⟩
  rw [hA]
  ext x
  simp [MulAut.congr_apply, MulEquiv.trans_apply, CFSG.HardMathSupport.Solomon.Coordinator.psuO]

theorem eq_of_card_unitaryPSU {K K₁ : Type} [Field K] [Field K₁]
    (hu₁ : UnitaryFieldData 2 m K₁) (hu : UnitaryFieldData 2 n K)
    (hcard : Nat.card (unitaryPSU hu₁ 3) = Nat.card (unitaryPSU hu 3)) : m = n := by
  have h1 := padicValNat_two_card_psu hu₁
  have h2 := padicValNat_two_card_psu hu
  rw [hcard] at h1
  omega

theorem map_range_psuConj_le_of_model {K K₁ : Type} [Field K] [Field K₁]
    (hu₁ : UnitaryFieldData 2 m K₁)
    (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n) {X : Type} [Group X] [Finite X]
    (e : X ≃* unitaryPSU hu 3) (e₁ : X ≃* unitaryPSU hu₁ 3) :
    (psuConj hu₁).range.map (MulAut.congr e₁.symm).toMonoidHom ≤
      (psuConj hu).range.map (MulAut.congr e.symm).toMonoidHom := by
  have hcard : Nat.card (unitaryPSU hu₁ 3) = Nat.card (unitaryPSU hu 3) :=
    (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  have hmn : m = n := eq_of_card_unitaryPSU hu₁ hu hcard
  subst m
  have hq : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  rintro _ ⟨ρ, hρ, rfl⟩
  have hφ : MulAut.congr (e₁.symm.trans e) ρ ∈ (psuConj hu).range :=
    congr_mem_psuConj_range_of_eq hu hu₁ hq (e₁.symm.trans e) hρ
  refine ⟨MulAut.congr (e₁.symm.trans e) ρ, hφ, ?_⟩
  ext x
  simp [MulAut.congr_apply, MulEquiv.trans_apply]

private theorem card_orders_false {M q : ℕ}
    (hPSL : M * Nat.gcd 3 (q - 1) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1))
    (hPSU : M * Nat.gcd 3 (q + 1) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1))
    (hq4 : 4 ≤ q) : False := by
  have hpos : 0 < q ^ 3 * (q ^ 2 - 1) := by
    have h4 : 16 ≤ q ^ 2 := by
      have h := Nat.pow_le_pow_left hq4 2
      norm_num at h
      exact h
    exact Nat.mul_pos (pow_pos (by omega) 3) (by omega)
  have hEq : (q ^ 3 - 1) * Nat.gcd 3 (q + 1) = (q ^ 3 + 1) * Nat.gcd 3 (q - 1) := by
    have h1 : (M * Nat.gcd 3 (q - 1)) * Nat.gcd 3 (q + 1) =
        (M * Nat.gcd 3 (q + 1)) * Nat.gcd 3 (q - 1) := by ring
    rw [hPSL, hPSU] at h1
    have h1' : (q ^ 3 * (q ^ 2 - 1)) * ((q ^ 3 - 1) * Nat.gcd 3 (q + 1)) =
        (q ^ 3 * (q ^ 2 - 1)) * ((q ^ 3 + 1) * Nat.gcd 3 (q - 1)) := by
      calc (q ^ 3 * (q ^ 2 - 1)) * ((q ^ 3 - 1) * Nat.gcd 3 (q + 1)) =
          (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) * Nat.gcd 3 (q + 1) := by ring
        _ = (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) * Nat.gcd 3 (q - 1) := h1
        _ = (q ^ 3 * (q ^ 2 - 1)) * ((q ^ 3 + 1) * Nat.gcd 3 (q - 1)) := by ring
    exact Nat.eq_of_mul_eq_mul_left hpos h1'
  have hg0 : Nat.gcd 3 (q - 1) = 1 ∨ Nat.gcd 3 (q - 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q - 1))
  have hg1 : Nat.gcd 3 (q + 1) = 1 ∨ Nat.gcd 3 (q + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q + 1))
  have hQ : 8 ≤ q ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq4 3
  rcases hg0 with h0 | h0 <;> rcases hg1 with h1 | h1 <;>
    rw [h0, h1] at hEq <;> omega

theorem not_exists_psl_model {K : Type} [Field K] (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    {X : Type} [Group X] [Finite X] (e : X ≃* unitaryPSU hu 3)
    {m : ℕ} {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2 ^ m)
    (e' : X ≃* StatedProj (StatedSL 3 K')) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rw [pow_zero] at hK'
      have h2 := Finite.one_lt_card (α := K')
      omega
    · exact hm0
  have hcard : Nat.card (StatedProj (StatedSL 3 K')) = Nat.card (unitaryPSU hu 3) :=
    (Nat.card_congr e'.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  have hmn : m = n := by
    have h1 := padicValNat_two_card_psl hK' hm1
    have h2 := padicValNat_two_card_psu hu
    rw [hcard] at h1
    omega
  rw [hmn] at hK'
  have hcardPSL := card_psl_three_mul_gcd (K := K')
  rw [hK'] at hcardPSL
  have hcardPSU := card_unitaryPSU_three_mul hu
  rw [card_unitarySU_three' hu, mul_assoc] at hcardPSU
  set q := 2 ^ n with hq
  rw [hcard] at hcardPSL
  have hPSL : Nat.card (unitaryPSU hu 3) * Nat.gcd 3 (q - 1) =
      q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [hcardPSL, mul_assoc]
  have hPSU : Nat.card (unitaryPSU hu 3) * Nat.gcd 3 (q + 1) =
      q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    rw [hcardPSU, mul_assoc]
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact card_orders_false hPSL hPSU hq4

theorem mem_map_range_psuConj_of_isProjConjAut {X : Type} [Group X] [Finite X] {n : ℕ}
    {K : Type} [Field K] (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (e : X ≃* unitaryPSU hu 3) {m : ℕ} {K₁ : Type} [Field K₁] [Finite K₁]
    {e₁ : X ≃* StatedProj (StatedSU 3 (2 ^ m) K₁)} {c : GL (Fin 3) K₁} {ψ : MulAut X}
    (hK₁card : Nat.card K₁ = (2 ^ m) ^ 2)
    (hc : CFSG.ASVolI.ChA.IsProjConjAut (StatedSU 3 (2 ^ m) K₁) c (MulAut.congr e₁ ψ)) :
    ψ ∈ (psuConj hu).range.map (MulAut.congr e.symm).toMonoidHom := by
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rw [pow_zero] at hK₁card
      have h2 := Finite.one_lt_card (α := K₁)
      have h3 : Nat.card K₁ = 1 := by
        rw [hK₁card]
        norm_num
      omega
    · exact hm0
  have hu₁ : UnitaryFieldData 2 m K₁ :=
    ⟨Nat.prime_two, hm1, by rw [hK₁card, ← pow_mul, Nat.mul_comm m 2]⟩
  let e₁' : X ≃* unitaryPSU hu₁ 3 :=
    e₁.trans (unitaryPSUEquiv hu₁ (by norm_num : 1 ≤ 3)).symm
  have hcard : Nat.card (unitaryPSU hu₁ 3) = Nat.card (unitaryPSU hu 3) :=
    (Nat.card_congr e₁'.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  have hmn : m = n := eq_of_card_unitaryPSU hu₁ hu hcard
  have hm2 : 2 ≤ m := by omega
  obtain ⟨A, hA⟩ := exists_unitaryIsom3_of_isProjConjAut hu₁ hm2 hc
  have hle := map_range_psuConj_le_of_model hu₁ hu hn e e₁'
  have hmem : MulAut.congr e₁'.symm (psuConj hu₁ A) ∈
      (psuConj hu₁).range.map (MulAut.congr e₁'.symm).toMonoidHom :=
    Subgroup.mem_map_of_mem _ ⟨A, rfl⟩
  have hψ : MulAut.congr e₁'.symm (psuConj hu₁ A) = ψ := by
    rw [← hA]
    ext x
    simp [MulAut.congr_apply, MulEquiv.trans_apply, e₁']
  exact hψ ▸ hle hmem

theorem innDiagSubgroup_le_map_range_psuConj {X : Type} [Group X] [Finite X] {n : ℕ}
    {K : Type} [Field K] (hu : UnitaryFieldData 2 n K) (hn : 2 ≤ n)
    (e : X ≃* unitaryPSU hu 3) :
    CFSG.ASVolI.ChA.innDiagSubgroup X ≤
      (psuConj hu).range.map (MulAut.congr e.symm).toMonoidHom := by
  rw [CFSG.ASVolI.ChA.innDiagSubgroup, Subgroup.closure_le]
  intro ψ hψ
  rcases hψ with hin | ⟨m, K', hK'f, hK'fin, e', c, hK'card, hc⟩ |
    ⟨m, K₁, hK₁f, hK₁fin, e₁, c, hK₁card, hc⟩
  · obtain ⟨x, rfl⟩ := hin
    have hconj : MulAut.congr e.symm (MulAut.conj (e x)) = MulAut.conj x := by
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply, MulEquiv.trans_apply]
    rw [← hconj]
    exact Subgroup.mem_map_of_mem _ ((stdPinnedPSU3 hu).inn_le ⟨e x, rfl⟩)
  · letI := hK'f
    letI := hK'fin
    exfalso
    exact not_exists_psl_model hu hn e hK'card e'
  · letI := hK₁f
    letI := hK₁fin
    exact mem_map_range_psuConj_of_isProjConjAut hu hn e hK₁card hc

end CFSG.RankThree.PartTwo.KFacts

end
