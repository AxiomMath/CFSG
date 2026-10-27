module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K318E9Q8
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621L3
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621M11
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Sec
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Blueprint
open CFSG.Sporadic.Mathieu (m11a m11b)
open CFSG.LocalAnalysis.UniquenessCase.UC6 (m11U l4X l4Z l4mX l4mZ l4_mk_eq_iff l4X_pow)
open scoped MatrixGroups

namespace E9Q8

@[expose] def HasE9Q8 (X : Type) [Group X] : Prop :=
  ∃ a b i j : X, a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * i = i * b ∧ b * i = i * a ^ 2 ∧
    a * j = j * (a * b) ∧ b * j = j * (a * b ^ 2) ∧ i * i * j = j * (i * i) ∧ a ≠ 1

theorem HasE9Q8.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : HasE9Q8 Y) :
    HasE9Q8 X := by
  obtain ⟨a, b, i, j, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨e.symm a, e.symm b, e.symm i, e.symm j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [← map_mul, ← map_pow, h1, h2, h3, h4, h5, h6, h7, h8, map_one, ne_eq,
      MulEquiv.map_eq_one_iff, h9, not_false_eq_true]

@[expose] def m11B : NativeSporadic.M11 := m11b⁻¹ * m11a * m11b⁻¹ * m11a * m11b * m11a * m11b⁻¹

@[expose] def m11J : NativeSporadic.M11 :=
  m11a * m11b * m11b * m11a * m11b * m11b * m11a * m11b * m11a * m11b * m11b * m11a * m11b *
    m11b * m11a

theorem hasE9Q8_m11 : HasE9Q8 NativeSporadic.M11 := by
  refine ⟨m11U, m11B, m11b, m11J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

open CFSG.Fischer Matrix

@[expose] def l4mI : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, 1, 1; 1, F4.ω * F4.ω, F4.ω; 1, F4.ω, F4.ω * F4.ω]

@[expose] def l4mN : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, F4.ω * F4.ω, F4.ω * F4.ω; F4.ω, F4.ω, F4.ω * F4.ω; F4.ω, F4.ω * F4.ω, F4.ω]

theorem det_l4mI : l4mI.det = 1 := by
  rw [l4mI, Matrix.det_fin_three]
  decide +kernel

theorem det_l4mN : l4mN.det = 1 := by
  rw [l4mN, Matrix.det_fin_three]
  decide +kernel

@[expose] def l4I : SpecialLinearGroup (Fin 3) F4 := ⟨l4mI, det_l4mI⟩

@[expose] def l4N : SpecialLinearGroup (Fin 3) F4 := ⟨l4mN, det_l4mN⟩

theorem l4_mk_mul (A B : SpecialLinearGroup (Fin 3) F4) :
    (QuotientGroup.mk A : PSL(3, F4)) * QuotientGroup.mk B = QuotientGroup.mk (A * B) :=
  (QuotientGroup.mk_mul _ _ _).symm

theorem l4_mk_eq {A B : SpecialLinearGroup (Fin 3) F4}
    (h : ∃ c : F4, c ≠ 0 ∧ (B : Matrix (Fin 3) (Fin 3) F4) = c • (A : Matrix (Fin 3) (Fin 3) F4)) :
    (QuotientGroup.mk A : PSL(3, F4)) = QuotientGroup.mk B :=
  (l4_mk_eq_iff A B).2 h

theorem hasE9Q8_psl_three_four : HasE9Q8 PSL(3, F4) := by
  have hZ3 : l4Z ^ 3 = 1 := by
    rw [pow_three]
    apply Subtype.ext
    change l4mZ * (l4mZ * l4mZ) = 1
    decide +kernel
  refine ⟨QuotientGroup.mk l4X, QuotientGroup.mk l4Z, QuotientGroup.mk l4I,
    QuotientGroup.mk l4N, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [l4_mk_mul]
    refine l4_mk_eq ?_
    change ∃ c : F4, c ≠ 0 ∧ l4mZ * l4mX = c • (l4mX * l4mZ)
    decide +kernel
  · rw [← QuotientGroup.mk_pow, l4X_pow, QuotientGroup.mk_one]
  · rw [← QuotientGroup.mk_pow, hZ3, QuotientGroup.mk_one]
  · simp only [l4_mk_mul]
    refine l4_mk_eq ?_
    change ∃ c : F4, c ≠ 0 ∧ l4mI * l4mZ = c • (l4mX * l4mI)
    decide +kernel
  · simp only [sq, l4_mk_mul]
    refine l4_mk_eq ?_
    change ∃ c : F4, c ≠ 0 ∧ l4mI * (l4mX * l4mX) = c • (l4mZ * l4mI)
    decide +kernel
  · simp only [l4_mk_mul]
    refine l4_mk_eq ?_
    change ∃ c : F4, c ≠ 0 ∧ l4mN * (l4mX * l4mZ) = c • (l4mX * l4mN)
    decide +kernel
  · simp only [sq, l4_mk_mul]
    refine l4_mk_eq ?_
    change ∃ c : F4, c ≠ 0 ∧ l4mN * (l4mX * (l4mZ * l4mZ)) = c • (l4mZ * l4mN)
    decide +kernel
  · simp only [l4_mk_mul]
    refine l4_mk_eq ?_
    change ∃ c : F4, c ≠ 0 ∧ l4mN * (l4mI * l4mI) = c • (l4mI * l4mI * l4mN)
    decide +kernel
  · intro h
    have h' : (QuotientGroup.mk l4X : PSL(3, F4)) = QuotientGroup.mk 1 := h
    rw [l4_mk_eq_iff] at h'
    revert h'
    change ¬ ∃ c : F4, c ≠ 0 ∧ (1 : Matrix (Fin 3) (Fin 3) F4) = c • l4mX
    decide +kernel

theorem hasE9Q8_of_lieModel_psl_three {X : Type} [Group X] (h : LieModel X .PSL 3 2 2) :
    HasE9Q8 X := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hK4, F4.card]
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hcard
  let e' : X ≃* PSL(3, F4) :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)
  exact hasE9Q8_psl_three_four.of_mulEquiv e'

end E9Q8


open CFSG.RepresentationTheory (IsIrreducibleMatrixRep)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

theorem false_of_irreducible_gl4_m11_l34 {q : ℕ} [Fact q.Prime] (_hq2 : q ≠ 2) (hq3 : q ≠ 3)
    {J : Subgroup (GL (Fin 4) (ZMod q))} (_hJ : CFSG.Open.IsQuasisimple ↥J)
    (hirr : IsIrreducibleMatrixRep J.subtype)
    (hX : IsSpor (↥J ⧸ Subgroup.center ↥J) .M11 ∨ LieModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 2) :
    False := by
  have hE : E9Q8.HasE9Q8 (↥J ⧸ center ↥J) := by
    rcases hX with h | h
    · obtain ⟨e⟩ := h
      exact E9Q8.hasE9Q8_m11.of_mulEquiv e
    · exact E9Q8.hasE9Q8_of_lieModel_psl_three h
  obtain ⟨a, b, i, j, hab, ha3, hb3, hia, hib, hja, hjb, hij, ha1⟩ := hE
  have h3 : (3 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1 h')
  refine E9Q8.false_of_e9q8 h3 (by norm_num) ?_ hirr hab ha3 hb3 hia hib hja hjb hij ha1
  intro x y c hxy hcx hcy hc3 hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h34 := UC6.K318.dvd_of_conj_eq_central_mul (s := 3) (j := 1) hxy hcx hcy
    (by rwa [pow_one]) hfix
  omega

end CFSG.LocalAnalysis.UniquenessCase.UCK
