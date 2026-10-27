module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.RankThree.PartOne.StrongP

section Orbit

variable {p : ℕ} {H : Type*} [Group H] [Finite H] {Y : Subgroup H}

theorem IsStronglyPEmbedded.index_modEq_card [Fact p.Prime] (hY : IsStronglyPEmbedded p Y)
    {P : Subgroup H} (hP : IsPGroup p P) (hPY : P ≤ Y) : Y.index ≡ 1 [MOD Nat.card P] := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype (H ⧸ Y) := Fintype.ofFinite _
  haveI : Fintype (MulAction.orbitRel.Quotient P (H ⧸ Y)) := Fintype.ofFinite _
  haveI : ∀ x : H ⧸ Y, Fintype (MulAction.stabilizer P x) := fun x => Fintype.ofFinite _
  set base : H ⧸ Y := QuotientGroup.mk 1 with hbase_def
  have hbase : ∀ q : P, q • base = base := fun q => by
    change ((q : H) • (QuotientGroup.mk 1 : H ⧸ Y)) = QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk]
    exact QuotientGroup.eq.mpr (by simpa using hPY q.2)
  have hfree : ∀ x : H ⧸ Y, x ≠ base → ∀ q : P, q • x = x → q = 1 := by
    intro x hx q hq
    induction x using QuotientGroup.induction_on with
    | H g =>
      have hgY : g ∉ Y := fun hg => hx (QuotientGroup.eq.mpr (by simpa using hg))
      by_contra hq1
      have hqH : (q : H) ≠ 1 := fun h => hq1 (Subtype.ext h)
      have hmem : (q : H)⁻¹ ∈ Y ⊓ conjSub g Y := by
        refine Subgroup.mem_inf.2 ⟨Y.inv_mem (hPY q.2), ?_⟩
        rw [mem_conjSub_iff]
        have h1 : (QuotientGroup.mk ((q : H) * g) : H ⧸ Y) = QuotientGroup.mk g := hq
        have h2 := QuotientGroup.eq.mp h1
        simpa [mul_assoc] using h2
      obtain ⟨k, hk⟩ := hP q
      have hk' : orderOf (q : H) ∣ p ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        have := congrArg Subtype.val hk
        simpa using this
      obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hk'
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hjo
        exact hqH hjo
      have hpo : p ∣ orderOf (q : H) := by
        rw [hjo]
        exact dvd_pow_self p hj0
      have hdvd : orderOf (⟨(q : H)⁻¹, hmem⟩ : ↥(Y ⊓ conjSub g Y)) ∣ Nat.card ↥(Y ⊓ conjSub g Y) :=
        orderOf_dvd_natCard _
      have hord : orderOf (⟨(q : H)⁻¹, hmem⟩ : ↥(Y ⊓ conjSub g Y)) = orderOf (q : H) := by
        rw [← Subgroup.orderOf_coe]
        exact orderOf_inv _
      rw [hord] at hdvd
      exact hY.2.2 g hgY (hpo.trans hdvd)
  have hcard : Nat.card P ≠ 0 := Nat.card_pos.ne'
  have hcf := MulAction.card_eq_sum_card_group_div_card_stabilizer P (H ⧸ Y)
  set ω₀ : MulAction.orbitRel.Quotient P (H ⧸ Y) := Quotient.mk'' base with hω₀
  have hterm_base : Fintype.card P / Fintype.card (MulAction.stabilizer P (ω₀.out)) = 1 := by
    have hout : ω₀.out = base := by
      have h1 : (Quotient.mk'' ω₀.out : MulAction.orbitRel.Quotient P (H ⧸ Y)) = ω₀ := Quotient.out_eq' ω₀
      have h2 : MulAction.orbitRel P (H ⧸ Y) ω₀.out base := Quotient.exact' (h1.trans hω₀)
      obtain ⟨q, hq⟩ := (MulAction.orbitRel_apply.1 h2)
      rw [← hq]
      exact hbase q
    rw [hout]
    have htop : MulAction.stabilizer P base = ⊤ := by
      ext q
      rw [MulAction.mem_stabilizer_iff]
      exact ⟨fun _ => Subgroup.mem_top q, fun _ => hbase q⟩
    have h1 : Fintype.card (MulAction.stabilizer P base) = Fintype.card P := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, htop, Subgroup.card_top]
    rw [h1]
    exact Nat.div_self Fintype.card_pos
  have hterm_other : ∀ ω : MulAction.orbitRel.Quotient P (H ⧸ Y), ω ≠ ω₀ →
      Fintype.card P / Fintype.card (MulAction.stabilizer P (ω.out)) = Fintype.card P := by
    intro ω hω
    have hne : ω.out ≠ base := by
      intro h
      apply hω
      rw [← Quotient.out_eq' ω, h]
    have hbot : MulAction.stabilizer P ω.out = ⊥ := by
      ext q
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
      exact ⟨hfree _ hne q, fun h => by rw [h, one_smul]⟩
    have h1 : Fintype.card (MulAction.stabilizer P ω.out) = 1 := by
      rw [← Nat.card_eq_fintype_card, hbot, Subgroup.card_bot]
    rw [h1, Nat.div_one]
  have hsum : Fintype.card (H ⧸ Y) = 1 + ((Finset.univ.erase ω₀).card) * Fintype.card P := by
    rw [hcf, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ ω₀), hterm_base]
    congr 1
    rw [Finset.sum_congr rfl (fun ω hω => hterm_other ω (Finset.ne_of_mem_erase hω)), Finset.sum_const,
      smul_eq_mul]
  have hidx : Y.index = Fintype.card (H ⧸ Y) := Nat.card_eq_fintype_card
  rw [hidx, hsum, ← Nat.card_eq_fintype_card (α := P)]
  exact (Nat.add_mul_mod_self_right 1 _ _)

end Orbit

end CFSG.RankThree.PartOne

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

theorem no_divisor_modEq_one (d : ℕ) (hd : d ∣ 3280076800) (h : d ≡ 1 [MOD 3 ^ 9]) : d = 1 := by
  have hfac : (3280076800 : ℕ) = 2 ^ 17 * 5 ^ 2 * 7 ^ 1 * 11 ^ 1 * 13 ^ 1 := by norm_num
  rw [hfac] at hd
  obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.1 hd
  obtain ⟨c, hc, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 13)).1 h₂
  obtain ⟨d₃, d₄, h₃, h₄, rfl⟩ := Nat.dvd_mul.1 h₁
  obtain ⟨e, he, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 11)).1 h₄
  obtain ⟨d₅, d₆, h₅, h₆, rfl⟩ := Nat.dvd_mul.1 h₃
  obtain ⟨c7, hc7, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 h₆
  obtain ⟨d₇, d₈, h₇, h₈, rfl⟩ := Nat.dvd_mul.1 h₅
  obtain ⟨a, ha, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).1 h₇
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 h₈
  have key : ∀ K ∈ ([1, 5, 25, 7, 35, 175, 11, 55, 275, 77, 385, 1925, 13, 65, 325, 91, 455, 2275, 143,
      715, 3575, 1001, 5005, 25025] : List ℕ), ∀ a < 18, (2 ^ a * K) % 3 ^ 9 = 1 → 2 ^ a * K = 1 := by
    decide
  have hK : 5 ^ b * 7 ^ c7 * 11 ^ e * 13 ^ c ∈ ([1, 5, 25, 7, 35, 175, 11, 55, 275, 77, 385, 1925, 13, 65,
      325, 91, 455, 2275, 143, 715, 3575, 1001, 5005, 25025] : List ℕ) := by
    interval_cases b <;> interval_cases c7 <;> interval_cases e <;> interval_cases c <;> simp
  have hd : 2 ^ a * 5 ^ b * 7 ^ c7 * 11 ^ e * 13 ^ c = 2 ^ a * (5 ^ b * 7 ^ c7 * 11 ^ e * 13 ^ c) := by
    ring
  have h' : (2 ^ a * (5 ^ b * 7 ^ c7 * 11 ^ e * 13 ^ c)) % 3 ^ 9 = 1 := by
    rw [← hd]
    have := h
    unfold Nat.ModEq at this
    rw [this]
    norm_num
  rw [hd]
  exact key _ hK a (by omega) h'

theorem not_isStronglyPEmbedded_three_of_fi22 {X : Type} [Group X] [Finite X]
    (h : IsSpor X .Fi22) (N : Subgroup X) : ¬ IsStronglyPEmbedded 3 N := by
  intro hN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h
  have hX0 : Nat.card X = 64561751654400 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Fi22.card_Fi22
  have hX : Nat.card X = 3 ^ 9 * 3280076800 := by
    rw [hX0]
    norm_num
  obtain ⟨P, hP, hPN⟩ := hN.exists_isSylowOf_le
  let S : Sylow 3 X := hP.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hP.2.2)
  have hSP : (S : Subgroup X) = P := IsPGroup.toSylow_coe _ _
  have hPcard : Nat.card P = 3 ^ 9 := by
    have h1 : Nat.card S = 3 ^ (Nat.card X).factorization 3 := S.card_eq_multiplicity
    have h2 : (Nat.card X).factorization 3 = 9 := by
      rw [Nat.factorization_def _ Nat.prime_three, hX, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [h2] at h1
    rw [← hSP]
    exact h1
  have hmod := hN.index_modEq_card hP.2.1 hPN
  rw [hPcard] at hmod
  have hdvd : N.index ∣ 3280076800 := by
    obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hPN
    have h1 := Subgroup.card_mul_index N
    rw [hX, hr, hPcard, mul_assoc] at h1
    have h2 : r * N.index = 3280076800 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    exact Dvd.intro_left r h2
  have hidx := no_divisor_modEq_one _ hdvd hmod
  exact hN.1 (Subgroup.index_eq_one.1 hidx)

end CFSG.LocalAnalysis.UniquenessCase.UCK
