module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125RArith
public import CFSG.RankThree.PartTwo.Sec11.Item1119NLSL2
public import CFSG.RankThree.PartTwo.Sec21.Item229Orders
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

theorem sl2_quot_card {J : Type} [Group J] [Finite J] {F : Type} [Field F] [Finite F]
    (hF4 : 4 ≤ Nat.card F) (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ} (hn : 2 ≤ n)
    (eQ : Nonempty (J ⧸ aschbacherSolvableCore 3 J ≃* projSL 2 (GaloisField 2 n))) :
    Nat.card F = 2 ^ n ∨ (Nat.card F = 5 ∧ n = 2) := by
  obtain ⟨eQ⟩ := eQ
  have hqs : CFSG.IsQuasisimple J := Sec11.Item1119NL.isQuasisimple_of_mulEquiv_sl2 hF4 e
  have hcardQ : Nat.card (J ⧸ aschbacherSolvableCore 3 J) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr eQ.toEquiv]
    exact Sec21.card_projSL_two n (by omega)
  have hm4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hM1 : 1 < Nat.card (J ⧸ aschbacherSolvableCore 3 J) := by
    rw [hcardQ]
    have h1 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h2 : 0 < (2 ^ n) ^ 2 - 1 := by omega
    calc 1 < 2 ^ n := by omega
      _ ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := Nat.le_mul_of_pos_right _ h2
  have hnt : Nontrivial (J ⧸ aschbacherSolvableCore 3 J) :=
    Finite.one_lt_card_iff_nontrivial.mp hM1
  have hθ := Sec11.Item1119NL.theta_le_center_of_isQuasisimple hqs hnt
  have hT : Nat.card (aschbacherSolvableCore 3 J) ≤ 2 :=
    (Subgroup.card_le_of_le hθ).trans (Sec11.Item1119NL.card_center_le_two_of_mulEquiv e)
  have hT1 : 1 ≤ Nat.card (aschbacherSolvableCore 3 J) := Nat.card_pos
  have hcardJ : Nat.card J =
      Nat.card (J ⧸ aschbacherSolvableCore 3 J) * Nat.card (aschbacherSolvableCore 3 J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 J)
  have hSL : Nat.card J = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hT12 : Nat.card (aschbacherSolvableCore 3 J) = 1 ∨
      Nat.card (aschbacherSolvableCore 3 J) = 2 := by omega
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hpF⟩ := CharP.exists F
  haveI := hpF
  haveI : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨k, hp, hk⟩ := FiniteField.card F p
  have hcardF : Nat.card F = p ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
  have hk1 : 1 ≤ (k : ℕ) := k.pos
  have heq : p ^ (k : ℕ) * ((p ^ (k : ℕ)) ^ 2 - 1) =
      Nat.card (aschbacherSolvableCore 3 J) * (2 ^ n * ((2 ^ n) ^ 2 - 1)) := by
    rw [← hcardF, ← hSL, hcardJ, hcardQ, mul_comm]
  rcases sl2_card_cases hp hk1 hn hT12 heq with ⟨rfl, hkn, -⟩ | ⟨rfl, hk1', hn2, -⟩
  · left
    rw [hcardF, hkn]
  · right
    refine ⟨?_, hn2⟩
    rw [hcardF, hk1']
    norm_num

noncomputable def specialLinearGroupMulEquiv {R S : Type} [CommRing R] [CommRing S] (n : ℕ)
    (f : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin n) R ≃* Matrix.SpecialLinearGroup (Fin n) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (f : R →+* S))
    (Matrix.SpecialLinearGroup.map (f.symm : S →+* R))
    (by ext i j; simp) (by ext i j; simp)

noncomputable def sl2_mulEquiv_five {F : Type} [Field F] [Finite F] (h : Nat.card F = 5) :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) := by
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : Fintype.card F = Fintype.card (ZMod 5) := by
    rw [← Nat.card_eq_fintype_card, h, ZMod.card]
  exact specialLinearGroupMulEquiv 2 (FiniteField.ringEquivOfCardEq hc)

end CFSG.RankThree.PartTwo.Sec21.Hering2125
