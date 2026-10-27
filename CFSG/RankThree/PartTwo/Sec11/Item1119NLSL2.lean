module

public import CFSG.RankThree.PartTwo.Sec8.Notation
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoQs
import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofOrder
import CFSG.RankThree.PartTwo.Sec11.Item1119NLArith
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119NL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def IsSL2 (J : Type) [Group J] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), 4 ≤ Nat.card F ∧
    Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F)

theorem theta_le_center_of_isQuasisimple {S : Type} [Group S] [Finite S]
    (hS : CFSG.IsQuasisimple S) (hnt : Nontrivial (S ⧸ aschbacherSolvableCore 3 S)) :
    aschbacherSolvableCore 3 S ≤ Subgroup.center S := by
  have hn : (aschbacherSolvableCore 3 S).Normal := inferInstance
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hS
      hn.isSubnormal with htop | hcen
  · exfalso
    have hsub : Subsingleton (S ⧸ aschbacherSolvableCore 3 S) := ⟨fun a b => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      rw [QuotientGroup.eq, htop]
      exact Subgroup.mem_top _⟩
    exact false_of_nontrivial_of_subsingleton (S ⧸ aschbacherSolvableCore 3 S)
  · exact hcen

theorem isQuasisimple_of_mulEquiv_sl2 {J : Type} [Group J] {F : Type} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.IsQuasisimple J :=
  CFSG.IsQuasisimple.of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.isQuasisimple_specialLinear_two hF)

theorem card_center_le_two_of_mulEquiv {J : Type} [Group J] {F : Type} [Field F] [Finite F]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) : Nat.card (Subgroup.center J) ≤ 2 := by
  have hk : max (Fintype.card (Fin 2)) 1 = 2 := by simp
  haveI : NeZero (max (Fintype.card (Fin 2)) 1) := ⟨by omega⟩
  have hmem : ∀ z : Subgroup.center J,
      e z.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro z
    rw [Subgroup.mem_center_iff]
    intro g
    have hz := Subgroup.mem_center_iff.mp z.2 (e.symm g)
    simpa using congrArg e hz
  have hφ : Function.Injective (fun z : Subgroup.center J =>
      Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F)
        ⟨e z.1, hmem z⟩) := by
    intro z1 z2 h
    have h1 := (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2)
      (R := F)).injective h
    have h2 : e z1.1 = e z2.1 := congrArg Subtype.val h1
    exact Subtype.ext (e.injective h2)
  have hle : Nat.card (Subgroup.center J) ≤
      Nat.card (rootsOfUnity (max (Fintype.card (Fin 2)) 1) F) :=
    Nat.card_le_card_of_injective _ hφ
  have hroot : Nat.card (rootsOfUnity (max (Fintype.card (Fin 2)) 1) F) ≤
      max (Fintype.card (Fin 2)) 1 :=
    card_rootsOfUnity _ _
  exact hle.trans (hroot.trans hk.le)

theorem orderOf_mk_eq_of_three_element {G : Type} [Group G] [Finite G] {L : Subgroup G} {x : G}
    (hxL : x ∈ L) (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) :
    orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) = orderOf x := by
  obtain ⟨k, hk⟩ := hx3
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have key : ∀ {ν : L}, ν ∈ aschbacherSolvableCore 3 L → ν ^ 3 ^ k = 1 → ν = 1 := by
    intro ν hν hpow
    have hpowN : (⟨ν, hν⟩ : aschbacherSolvableCore 3 L) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hpow)
    have h1 : orderOf (⟨ν, hν⟩ : aschbacherSolvableCore 3 L) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one hpowN
    have h2 : orderOf (⟨ν, hν⟩ : aschbacherSolvableCore 3 L) ∣
        Nat.card (aschbacherSolvableCore 3 L) :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (aschbacherSolvableCore 3 L)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3)
    have h3 : orderOf (⟨ν, hν⟩ : aschbacherSolvableCore 3 L) ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd h1 h2
    have h4 : (⟨ν, hν⟩ : aschbacherSolvableCore 3 L) = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
    exact congrArg Subtype.val h4
  have hy : (⟨x, hxL⟩ : L) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [← map_pow (QuotientGroup.mk' (aschbacherSolvableCore 3 L)), QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  constructor
  · intro hn
    have hpow : ((⟨x, hxL⟩ : L) ^ n) ^ 3 ^ k = 1 := by
      rw [pow_right_comm, hy, one_pow]
    have hw : (⟨x, hxL⟩ : L) ^ n = 1 := key hn hpow
    have := congrArg Subtype.val hw
    simpa using this
  · intro hn
    have h1 : (⟨x, hxL⟩ : L) ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [h1]
    exact Subgroup.one_mem _

theorem card_of_isoLThreeMinusPi {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n)
    (h : Sec8.IsoLThreeMinusPi X 2 n) :
    (2 ^ n % 3 = 1 ∧ Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1))) ∨
    (2 ^ n % 3 = 2 ∧ Nat.card X = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1))) := by
  rcases h with ⟨h1, ⟨e⟩⟩ | ⟨h2, ⟨e⟩⟩
  · refine Or.inl ⟨h1, ?_⟩
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec4.Item424Res3.card_projSU_three_two_pow hn h1, mul_assoc]
  · refine Or.inr ⟨h2, ?_⟩
    rw [Nat.card_congr e.toEquiv,
      CFSG.RankThree.PartTwo.Sec4.Item424Res3.card_projSL_three_two_pow hn h2]

theorem three_le_of_large_three_element {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : Sec8.IsoLThreeMinusPi X 2 (3 * m)) {g : X} (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1)
    (hg : 9 < orderOf g) : 3 ≤ m := by
  by_contra hcon
  have hcon' : m < 3 := not_le.mp hcon
  obtain ⟨k, hk⟩ := hg3
  obtain ⟨j, -, hj⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have hlt' : j < 3 := not_le.mp hlt
    have hle : orderOf g ≤ 9 := by
      rw [hj]
      calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 9 := by norm_num
    omega
  have h27 : 27 ∣ orderOf g := by
    rw [hj]
    exact dvd_trans (by norm_num : (27 : ℕ) ∣ 3 ^ 3) (pow_dvd_pow 3 hj3)
  have hNX : 27 ∣ Nat.card X := dvd_trans h27 (orderOf_dvd_natCard g)
  have hcases := card_of_isoLThreeMinusPi (n := 3 * m) (by omega) hX
  interval_cases m
  · rcases hcases with ⟨h1, -⟩ | ⟨-, h2⟩
    · norm_num at h1
    · rw [h2] at hNX
      norm_num at hNX
  · rcases hcases with ⟨-, h1⟩ | ⟨h2, -⟩
    · rw [h1] at hNX
      norm_num at hNX
    · norm_num at h2

theorem false_of_isSL2 {J : Type} [Group J] [Finite J] (hJ : IsSL2 J) {n : ℕ} (hn : 3 ≤ n)
    (hL : Sec8.IsoLThreeMinusPi (J ⧸ aschbacherSolvableCore 3 J) 2 n) : False := by
  obtain ⟨F, _, _, hF4, ⟨e⟩⟩ := hJ
  have hqs : CFSG.IsQuasisimple J := isQuasisimple_of_mulEquiv_sl2 hF4 e
  have hq8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hM := card_of_isoLThreeMinusPi (by omega) hL
  have h3 : 512 ≤ (2 ^ n) ^ 3 :=
    calc 512 = 8 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left hq8 3
  have h2 : 64 ≤ (2 ^ n) ^ 2 :=
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq8 2
  have hM1 : 1 < Nat.card (J ⧸ aschbacherSolvableCore 3 J) := by
    rcases hM with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · have hpos : 0 < ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
        Nat.mul_pos (by omega) (by omega)
      exact lt_of_lt_of_le (by norm_num) (h3.trans (Nat.le_mul_of_pos_right _ hpos))
    · have hpos : 0 < ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) :=
        Nat.mul_pos (by omega) (by omega)
      exact lt_of_lt_of_le (by norm_num) (h3.trans (Nat.le_mul_of_pos_right _ hpos))
  have hnt : Nontrivial (J ⧸ aschbacherSolvableCore 3 J) :=
    Finite.one_lt_card_iff_nontrivial.mp hM1
  have hθ := theta_le_center_of_isQuasisimple hqs hnt
  have hT : Nat.card (aschbacherSolvableCore 3 J) ≤ 2 :=
    (Subgroup.card_le_of_le hθ).trans (card_center_le_two_of_mulEquiv e)
  have hT1 : 1 ≤ Nat.card (aschbacherSolvableCore 3 J) := Nat.card_pos
  have hcardJ : Nat.card J =
      Nat.card (J ⧸ aschbacherSolvableCore 3 J) * Nat.card (aschbacherSolvableCore 3 J) := by
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 J)
  have hSL : Nat.card J = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hT12 : Nat.card (aschbacherSolvableCore 3 J) = 1 ∨
      Nat.card (aschbacherSolvableCore 3 J) = 2 := by omega
  exact false_of_sl2_order (fun k u hk hu h => two_pow_le_of_dvd_pred_mul_succ hk hu h) hn hF4
    hT12 (hM.imp (fun h => h.2) (fun h => h.2)) (by rw [mul_comm, ← hcardJ, hSL])

end CFSG.RankThree.PartTwo.Sec11.Item1119NL

end
