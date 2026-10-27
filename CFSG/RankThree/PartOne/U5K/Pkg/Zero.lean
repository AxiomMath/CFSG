module

public import CFSG.RankThree.PartOne.U5K.Pkg.Order
public import CFSG.RankThree.PartOne.U5K.Model

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open Polynomial
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Open (ordTwistedA)

theorem card_galoisField_two_zero : Nat.card (GaloisField 2 0) = 2 := by
  have h0 : (X ^ 2 ^ 0 - X : (ZMod 2)[X]) = 0 := by simp
  unfold GaloisField
  rw [h0]
  set L := SplittingField (0 : (ZMod 2)[X])
  have hbt : (⊥ : Subalgebra (ZMod 2) L) = ⊤ := by
    rw [← IsSplittingField.adjoin_rootSet L (0 : (ZMod 2)[X]), Polynomial.rootSet_zero,
      Algebra.adjoin_empty]
  have h1 : Module.finrank (ZMod 2) L = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbt
  have := FiniteField.pow_finrank_eq_natCard 2 L
  rw [h1, pow_one] at this
  exact this.symm

theorem card_projSU_zero_dvd : Nat.card (projSU 5 2 0) ∣ 9999360 := by
  have hF : Nat.card (GaloisField 2 (2 * 0)) = 2 := card_galoisField_two_zero
  have : Fintype (GaloisField 2 (2 * 0)) := Fintype.ofFinite _
  have hF' : Fintype.card (GaloisField 2 (2 * 0)) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF
  have h1 : Nat.card (projSU 5 2 0) ∣ Nat.card (Matrix.ProjGenLinGroup (Fin 5)
      (GaloisField 2 (2 * 0))) := Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (Matrix.ProjGenLinGroup (Fin 5) (GaloisField 2 (2 * 0))) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 5) (GaloisField 2 (2 * 0))) :=
    Subgroup.index_dvd_card _
  have h3 : Nat.card (Matrix.GeneralLinearGroup (Fin 5) (GaloisField 2 (2 * 0))) = 9999360 := by
    rw [Matrix.card_GL_field, hF']
    simp [Fin.prod_univ_succ]
  exact h1.trans (h3 ▸ h2)

theorem two_pow_eleven_dvd_card {b : ℕ} (hb : 2 ≤ b) : 2 ^ 11 ∣ Nat.card (projSU 5 2 b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpos : Nat.card (projSU 5 2 b) ≠ 0 := by
    have : Finite (projSU 5 2 b) := u5_finite b (by omega)
    exact Nat.card_pos.ne'
  rw [card_projSU_five (by omega)] at hpos ⊢
  rw [padicValNat_dvd_iff_le hpos, padicValNat_ordTwistedA_four (by omega)]
  omega

theorem not_mulEquiv_projSU_zero {b : ℕ} (hb : 2 ≤ b) :
    IsEmpty (projSU 5 2 0 ≃* projSU 5 2 b) := ⟨fun e => by
  have h1 : Nat.card (projSU 5 2 0) = Nat.card (projSU 5 2 b) := Nat.card_congr e.toEquiv
  have h3 := two_pow_eleven_dvd_card hb
  rw [← h1] at h3
  exact absurd (h3.trans card_projSU_zero_dvd) (by norm_num)⟩

end CFSG.RankThree.PartOne.U5K.Pkg
