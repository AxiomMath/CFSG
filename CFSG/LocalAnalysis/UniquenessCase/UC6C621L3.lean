module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C621L2
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup Matrix CFSG.Fischer
open scoped MatrixGroups

@[expose] def l4mX : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def l4mZ : Matrix (Fin 3) (Fin 3) F4 := !![1, 0, 0; 0, F4.ω, 0; 0, 0, F4.ω * F4.ω]

@[expose] def l4mF : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, 1, 1; 1, F4.ω, F4.ω * F4.ω; 1, F4.ω * F4.ω, F4.ω]

theorem det_l4mX : l4mX.det = 1 := by
  rw [l4mX, Matrix.det_fin_three]
  decide +kernel

theorem det_l4mZ : l4mZ.det = 1 := by
  rw [l4mZ, Matrix.det_fin_three]
  decide +kernel

theorem det_l4mF : l4mF.det = 1 := by
  rw [l4mF, Matrix.det_fin_three]
  decide +kernel

@[expose] def l4X : SpecialLinearGroup (Fin 3) F4 := ⟨l4mX, det_l4mX⟩

@[expose] def l4Z : SpecialLinearGroup (Fin 3) F4 := ⟨l4mZ, det_l4mZ⟩

@[expose] def l4F : SpecialLinearGroup (Fin 3) F4 := ⟨l4mF, det_l4mF⟩

theorem l4X_pow : l4X ^ 3 = 1 := by
  rw [pow_three]
  apply Subtype.ext
  change l4mX * (l4mX * l4mX) = 1
  decide +kernel

theorem l4_FX : l4F * l4X = l4Z * l4F := by
  apply Subtype.ext
  change l4mF * l4mX = l4mZ * l4mF
  decide +kernel

theorem l4_mk_eq_iff (g h : SpecialLinearGroup (Fin 3) F4) :
    (QuotientGroup.mk g : PSL(3, F4)) = QuotientGroup.mk h ↔
      ∃ c : F4, c ≠ 0 ∧ (h : Matrix (Fin 3) (Fin 3) F4) = c • (g : Matrix (Fin 3) (Fin 3) F4) := by
  rw [psl_mk_eq_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, u.ne_zero, hu⟩
  · rintro ⟨c, hc, hh⟩
    exact ⟨Units.mk0 c hc, hh⟩

theorem card_psl_three_four : Nat.card PSL(3, F4) = 9 * 2240 := by
  have h1 := Nat.card_congr
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F4).toEquiv
  have h2 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := F4) (n := 3)
    (by norm_num)
  have hc : Nat.card F4 = 4 := by rw [Nat.card_eq_fintype_card, F4.card]
  rw [h1, h2, hc, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  norm_num

theorem invNormalizer_psl_three_four : InvNormalizer 3 PSL(3, F4) := by
  have hmk : ∀ A B : SpecialLinearGroup (Fin 3) F4, (QuotientGroup.mk A : PSL(3, F4)) *
      QuotientGroup.mk B = QuotientGroup.mk (A * B) := fun A B => (QuotientGroup.mk_mul _ _ _).symm
  have hXX : l4X * (l4X * l4X) = 1 := by rw [← pow_three]; exact l4X_pow
  refine invNormalizer_of_cycle (u := QuotientGroup.mk l4X) (v := QuotientGroup.mk l4Z)
    (x := QuotientGroup.mk l4F) card_psl_three_four (by norm_num) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← QuotientGroup.mk_pow, l4X_pow, QuotientGroup.mk_one]
  · intro h
    have h' : (QuotientGroup.mk l4X : PSL(3, F4)) = QuotientGroup.mk 1 := h
    rw [l4_mk_eq_iff] at h'
    revert h'
    change ¬ ∃ c : F4, c ≠ 0 ∧ (1 : Matrix (Fin 3) (Fin 3) F4) = c • l4mX
    decide +kernel
  · rw [mul_inv_eq_iff_eq_mul, hmk, hmk, l4_FX]
  · rw [hmk, hmk, l4_mk_eq_iff]
    change ∃ c : F4, c ≠ 0 ∧ l4mZ * l4mX = c • (l4mX * l4mZ)
    decide +kernel
  · intro h
    rw [l4_mk_eq_iff] at h
    revert h
    change ¬ ∃ c : F4, c ≠ 0 ∧ l4mX = c • l4mZ
    decide +kernel
  · intro h
    rw [sq, hmk, l4_mk_eq_iff] at h
    revert h
    change ¬ ∃ c : F4, c ≠ 0 ∧ l4mX * l4mX = c • l4mZ
    decide +kernel
  · have hinv : (QuotientGroup.mk l4X : PSL(3, F4))⁻¹ = QuotientGroup.mk (l4X * l4X) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [hmk, hXX]
      rfl
    rw [mul_inv_eq_iff_eq_mul, hinv]
    simp only [hmk]
    congr 1
    apply Subtype.ext
    change l4mF * l4mF * l4mX = l4mX * l4mX * (l4mF * l4mF)
    decide +kernel

theorem invNormalizer_of_lieModel_psl_three {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) : InvNormalizer 3 X := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  let _ : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hK4, F4.card]
  let φ : K ≃+* F4 := FiniteField.ringEquivOfCardEq hcard
  let e' : X ≃* PSL(3, F4) :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)
  haveI : Finite X := Finite.of_equiv _ e'.symm.toEquiv
  exact invNormalizer_psl_three_four.of_mulEquiv e'.symm

end CFSG.LocalAnalysis.UniquenessCase.UC6
