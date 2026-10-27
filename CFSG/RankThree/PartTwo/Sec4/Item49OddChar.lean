module

public import CFSG.RankThree.PartTwo.Sec4.Item49Tools
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary
import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item49OddChar

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item49Tools
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence center_map_equiv)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSp StatedSL specialLinearGroupEquivStatedSL)

section General

variable {H : Type*} [Group H]

theorem normal_of_commutator_mem {N : Subgroup H} (hN : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N) :
    N.Normal :=
  ⟨fun n hn g => by simpa [mul_assoc] using N.mul_mem (hN g n) hn⟩

theorem quotient_mul_comm_of_commutator_mem {N : Subgroup H} [N.Normal]
    (hN : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N) (a b : H ⧸ N) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with
  | H x =>
  induction b using QuotientGroup.induction_on with
  | H y =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  simpa [mul_assoc] using hN y⁻¹ x⁻¹

theorem odd_card_oThreePrime_of_commutator_mem [Finite H] (N : Subgroup H)
    (hN : Odd (Nat.card N)) (hcomm : ∀ a b : H, a * b * a⁻¹ * b⁻¹ ∈ N) :
    Odd (Nat.card (oThreePrime H)) := by
  have : N.Normal := normal_of_commutator_mem hcomm
  exact odd_card_oThreePrime_of_comm_quotient N hN (quotient_mul_comm_of_commutator_mem hcomm)

theorem odd_card_of_dvd_three {N : Subgroup H} (hN : Nat.card N ∣ 3) : Odd (Nat.card N) :=
  Odd.of_dvd_nat (by decide) hN

theorem finite_outer (X : Type*) [Group X] [Finite X] : Finite (Outer X) := by
  have : Finite (MulAut X) := MulEquiv.finite_left
  infer_instance

theorem not_three_dvd_card_outer_of_forall_pow {X : Type*} [Group X] [Finite X] {m : ℕ}
    (hm : ¬ 3 ∣ m) (hpow : ∀ τ : MulAut X, τ ^ m ∈ inner X) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  intro h3
  have : Finite (Outer X) := finite_outer X
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Outer X) 3 h3
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (QuotientGroup.mk τ : Outer X) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hpow τ
  exact hm (hx ▸ orderOf_dvd_of_pow_eq_one h1)

theorem not_three_dvd_card_outer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ¬ 3 ∣ Nat.card (Outer Y)) : ¬ 3 ∣ Nat.card (Outer X) := by
  rwa [Nat.card_congr (equivalence e).toEquiv]

theorem odd_card_oThreePrime_outer_of_not_dvd {X : Type*} [Group X] [Finite X]
    (h3 : ¬ 3 ∣ Nat.card (Outer X)) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Finite (Outer X) := finite_outer X
  exact odd_card_oThreePrime_of_not_dvd h3

theorem odd_card_oThreePrime_outer_of_comm {X : Type*} [Group X] [Finite X]
    (hcomm : ∀ a b : Outer X, a * b = b * a) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Finite (Outer X) := finite_outer X
  exact odd_card_oThreePrime_of_comm hcomm

theorem odd_card_oThreePrime_outer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (hY : Odd (Nat.card (oThreePrime (Outer Y)))) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have : Finite (Outer X) := finite_outer X
  have : Finite (Outer Y) := finite_outer Y
  exact (odd_card_oThreePrime_outer_congr e).mpr hY

theorem odd_card_oThreePrime_outer_of_center_mulEquiv {X S P : Type*} [Group X] [Group S]
    [Group P] [Finite X] [Group.IsPerfect X] (e : X ≃* S) (eP : S ⧸ Subgroup.center S ≃* P)
    (hP : Odd (Nat.card (oThreePrime (Outer P)))) : Odd (Nat.card (oThreePrime (Outer X))) := by
  have eZ : X ⧸ Subgroup.center X ≃* S ⧸ Subgroup.center S :=
    QuotientGroup.congr _ _ e (center_map_equiv e)
  have : Finite (Outer (X ⧸ Subgroup.center X)) := finite_outer _
  exact odd_card_oThreePrime_outer_of_center X
    (odd_card_oThreePrime_outer_of_mulEquiv (eZ.trans eP) hP)

theorem subsingleton_ringAut_of_card_prime {K : Type*} [Field K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) : Subsingleton (K ≃+* K) :=
  (Nat.card_eq_one_iff_unique.mp (card_ringAut_eq hp le_rfl (by rw [hK, pow_one]))).1

end General

theorem odd_card_oThreePrime_outer_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X]
    {K : Type} [Field K] [Finite K] (e : X ≃* GorensteinWalter.PSL2 K) :
    Odd (Nat.card (oThreePrime (Outer X))) :=
  odd_card_oThreePrime_outer_of_comm fun a b => (equivalence e).injective (by
    rw [map_mul, map_mul]
    exact OuterDerived.outer_psl2_mul_comm K _ _)

theorem odd_card_oThreePrime_outer_projectiveSL_three (K : Type) [Field K] [Finite K] :
    Odd (Nat.card (oThreePrime (Outer (LinearFlag.projectiveSL 3 K)))) := by
  have : Finite (Outer (LinearFlag.projectiveSL 3 K)) := finite_outer _
  obtain ⟨N, -, hcard, hcomm⟩ :=
    OuterDerived.exists_linear_outer_diagonal (K := K) (n := 3) le_rfl
  exact odd_card_oThreePrime_of_commutator_mem N
    (odd_card_of_dvd_three (hcard.trans (Nat.gcd_dvd_left 3 _))) hcomm

theorem odd_card_oThreePrime_outer_primeFormP_three {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    Odd (Nat.card (oThreePrime (Outer (UnitaryHigher.primeFormP h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))))) := by
  have : Finite K := h.finite
  have : Finite (Outer (UnitaryHigher.primeFormP h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := finite_outer _
  obtain ⟨N, -, hcard, hcomm⟩ :=
    OuterDerived.exists_unitary_outer_diagonal h (n := 3) le_rfl (fun h2 => by omega)
  exact odd_card_oThreePrime_of_commutator_mem N
    (odd_card_of_dvd_three (hcard.trans (Nat.gcd_dvd_left 3 _))) hcomm

theorem odd_card_oThreePrime_outer_unitaryPSU_three {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    Odd (Nat.card (oThreePrime (Outer (unitaryPSU h 3)))) := by
  have : Finite K := h.finite
  obtain ⟨⟨eT⟩, -⟩ :=
    UnitaryHigher.unitary_full_diagonal_outer_order h (n := 3) le_rfl (fun h2 => by omega)
  exact odd_card_oThreePrime_outer_of_mulEquiv eT.symm
    (odd_card_oThreePrime_outer_primeFormP_three h hq)

theorem odd_card_oThreePrime_outer_of_mulEquiv_statedSL {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] {K : Type} [Field K] [Finite K] (e : X ≃* StatedSL 3 K) :
    Odd (Nat.card (oThreePrime (Outer X))) :=
  odd_card_oThreePrime_outer_of_center_mulEquiv (e.trans (specialLinearGroupEquivStatedSL 3 K).symm)
    (QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 K).symm)
    (odd_card_oThreePrime_outer_projectiveSL_three K)

theorem odd_card_oThreePrime_outer_of_mulEquiv_unitarySU {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (e : X ≃* unitarySU p f K 3) :
    Odd (Nat.card (oThreePrime (Outer X))) :=
  odd_card_oThreePrime_outer_of_center_mulEquiv e (suCenterEquiv h hq)
    (odd_card_oThreePrime_outer_unitaryPSU_three h hq)

theorem not_three_dvd_card_outer_psp4 {K : Type} [Field K] [Finite K] (hodd : ringChar K ≠ 2)
    (hK : Subsingleton (K ≃+* K)) : ¬ 3 ∣ Nat.card (Outer (StatedProj (StatedSp 2 K))) := by
  refine not_three_dvd_card_outer_of_forall_pow (m := 2) (by norm_num) fun τ => ?_
  obtain ⟨A, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd τ
  rw [Subsingleton.elim σ 1, map_one, mul_one]
  exact isInnerAut_spConjAut_sq A

theorem not_three_dvd_card_outer_projectiveSL_four {K : Type} [Field K] [Finite K]
    (hK : Subsingleton (K ≃+* K)) : ¬ 3 ∣ Nat.card (Outer (LinearFlag.projectiveSL 4 K)) := by
  refine not_three_dvd_card_outer_of_forall_pow (m := 8) (by norm_num) fun τ => ?_
  obtain ⟨A, σ, ε, hε, rfl⟩ :=
    (LinearFlag.automorphism_generation (K := K) (n := 4) (by norm_num)).2 τ
  have htrans := LinearFlag.standard_automorphism_transport (K := K) (n := 4)
  rw [Subsingleton.elim σ 1, map_one, mul_one]
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 4) K,
      (LinearFlag.conjAut 4 K A * LinearFlag.dualAut 4 K ^ ε) ^ 2 = LinearFlag.conjAut 4 K B := by
    interval_cases ε
    · exact ⟨A * A, by rw [pow_zero, mul_one, pow_two, htrans.1]⟩
    · refine ⟨A * Matrix.GeneralLinearGroup.inverseTranspose A, ?_⟩
      rw [pow_one, pow_two, ← htrans.1, ← htrans.2.2.2.2.1 A]
      group
  have h8 : (LinearFlag.conjAut 4 K A * LinearFlag.dualAut 4 K ^ ε) ^ 8 =
      LinearFlag.conjAut 4 K B ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, hB]
  rw [h8]
  exact isInnerAut_conjAut_pow_n B

section G2


open CFSG.Blueprint.Chevalley in
theorem mem_inner_adjointGroup_G2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {K : Type} [Field K]
    (hK : Nat.card K = p) (α : MulAut (adjointGroup Tag.G2 K)) :
    α ∈ inner (adjointGroup Tag.G2 K) := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    LieType.Chevalley.odd_F4_and_nonexceptional_G2_automorphism_normal_form hp (by omega) le_rfl
      K (by rw [hK, pow_one]) Tag.G2 (Or.inr ⟨rfl, by omega⟩)
  have : Subsingleton (K ≃+* K) := subsingleton_ringAut_of_card_prime hp hK
  have hα : α ∈ Θ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  rw [hker] at hα
  exact hα

theorem not_three_dvd_card_outer_g2 {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp3 : 3 < p) (h : Blueprint.ChevalleyExceptionalModel X .G2 p 1) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨K, _, _, hK, ⟨e₁⟩⟩ := exists_mulEquiv_adjointGroup_G2 h
  rw [pow_one] at hK
  have : Finite (Blueprint.Chevalley.adjointGroup Blueprint.Chevalley.Tag.G2 K) :=
    Finite.of_equiv X e₁.toEquiv
  exact not_three_dvd_card_outer_of_mulEquiv e₁
    (not_three_dvd_card_outer_of_forall_pow (m := 1) (by norm_num) fun τ => by
      rw [pow_one]
      exact mem_inner_adjointGroup_G2 Fact.out hp3 hK τ)

end G2

end CFSG.RankThree.PartTwo.Sec4.Item49OddChar

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.LocalAnalysis.ComponentInitial

theorem oddOThreePrime_list46_one (X : Type) [Group X] [Finite X]
    (hX : ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Nonempty (X ≃* projSL 2 (GaloisField p e))) :
    Odd (Nat.card (oThreePrime (Outer X))) := by
  obtain ⟨p, e, _, -, -, ⟨e₁⟩⟩ := hX
  exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv_psl2 (e₁.trans (projSLEquivPSL _))

theorem oddOThreePrime_list46_two (X : Type) [Group X] [Finite X]
    (hX : ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
        Nonempty (X ≃* projSU 3 p e)))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) := by
  obtain ⟨p, e, _, hp3, he1, -, hX⟩ := hX
  have hp : p.Prime := Fact.out
  have hq2 : 2 < p ^ e := lt_of_lt_of_le (by omega) (Nat.le_self_pow (by omega) p)
  have : Group.IsPerfect X := hq.1
  rcases hX with ⟨K, _, _, ⟨-, ⟨e₁⟩⟩ | ⟨hK, ⟨e₁⟩⟩⟩ | he₁ | he₁
  · exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv_statedSL e₁
  · have hU : UnitaryFieldData p e K := ⟨hp, he1, by rw [hK, ← pow_mul, mul_comm]⟩
    exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv_unitarySU hU hq2 e₁
  · obtain ⟨e₁⟩ := he₁
    exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv
      (e₁.trans (projSLEquivProjectiveSL 3 _))
      (Item49OddChar.odd_card_oThreePrime_outer_projectiveSL_three _)
  · obtain ⟨e₁⟩ := he₁
    have hU := unitaryFieldData_galoisField p e he1
    exact Item49OddChar.odd_card_oThreePrime_outer_of_mulEquiv
      (e₁.trans (projSUEquivUnitaryPSU p e hU))
      (Item49OddChar.odd_card_oThreePrime_outer_unitaryPSU_three hU hq2)

section Three


theorem not_three_dvd_card_outer_list46_three (X : Type) [Group X] [Finite X]
    (hX : ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      (Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
        Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
        (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
        (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  obtain ⟨p, _, hp3, hX⟩ := hX
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p 1) = p := by rw [card_galoisField p 1 le_rfl, pow_one]
  have hsub := Item49OddChar.subsingleton_ringAut_of_card_prime hp hK
  rcases hX with hG2 | he₁ | ⟨hp1, ⟨e₁⟩⟩ | ⟨-, ⟨e₁⟩⟩
  · exact Item49OddChar.not_three_dvd_card_outer_g2 hp3 hG2
  · obtain ⟨e₁⟩ := he₁
    have hodd : ringChar (GaloisField p 1) ≠ 2 := by
      rw [ringChar.eq (GaloisField p 1) p]
      omega
    exact Item49OddChar.not_three_dvd_card_outer_of_mulEquiv
      (e₁.trans (projSpEquivStatedProj 2 _)) (Item49OddChar.not_three_dvd_card_outer_psp4 hodd hsub)
  · exact Item49OddChar.not_three_dvd_card_outer_of_mulEquiv e₁ (outU4p_holds p hp3 hp1)
  · exact Item49OddChar.not_three_dvd_card_outer_of_mulEquiv
      (e₁.trans (projSLEquivProjectiveSL 4 _))
      (Item49OddChar.not_three_dvd_card_outer_projectiveSL_four hsub)

theorem oddOThreePrime_list46_three (X : Type) [Group X] [Finite X]
    (hX : ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      (Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
        Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
        (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
        (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))) :
    Odd (Nat.card (oThreePrime (Outer X))) :=
  Item49OddChar.odd_card_oThreePrime_outer_of_not_dvd (not_three_dvd_card_outer_list46_three X hX)

theorem oddOThreePrime_oddChar (X : Type) [Group X] [Finite X]
    (hX : (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
        Nonempty (X ≃* projSL 2 (GaloisField p e))) ∨
      (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
        (IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
          Nonempty (X ≃* projSU 3 p e))) ∨
      (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
        (Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
          Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
          (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
          (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))))
    (hq : CFSG.IsQuasisimple X) : Odd (Nat.card (oThreePrime (Outer X))) := by
  rcases hX with h | h | h
  · exact oddOThreePrime_list46_one X h
  · exact oddOThreePrime_list46_two X h hq
  · exact oddOThreePrime_list46_three X h

end Three

end CFSG.RankThree.PartTwo.Sec4
