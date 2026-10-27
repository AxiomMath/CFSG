module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.EvenBN.U4.Model.OuterInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.F3Dihedral

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.OL

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.EvenBN.U4 CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (basisMatrixEquiv
  isometry_iff_matrix)
open LinearMap (BilinForm)

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) [CharP K 2]

theorem tfc_isAlt : (Matrix.toBilin' (miyamotoJ4 h.fixedField)).IsAlt := by
  intro v
  rw [Matrix.toBilin'_apply']
  simp only [dotProduct, Matrix.mulVec, miyamotoJ4, Fin.sum_univ_four]
  simp
  linear_combination (v 0 * v 3 + v 1 * v 2) * (CharTwo.two_eq_zero : (2 : h.fixedField) = 0)

theorem tfc_nondeg : (Matrix.toBilin' (miyamotoJ4 h.fixedField)).Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.mpr
    (Matrix.nondegenerate_of_det_ne_zero (det_miyamotoJ4_ne_zero (K := h.fixedField)))

theorem tfc_map_isometryGroup :
    (TauCeti.BilinForm.isometryGroup (Matrix.toBilin' (miyamotoJ4 h.fixedField))).map
      (basisMatrixEquiv (Pi.basisFun h.fixedField (Fin 4))).toMonoidHom = miyamotoSp4 h := by
  ext M
  rw [Subgroup.mem_map_equiv, isometry_iff_matrix (Pi.basisFun h.fixedField (Fin 4)),
    MulEquiv.apply_symm_apply, BilinForm.toMatrix_basisFun, BilinForm.toMatrix'_toBilin']
  rfl

theorem tfc_card_Sp4 :
    Nat.card (miyamotoSp4 h) = (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
  have := h.finite
  rw [← tfc_map_isometryGroup, Subgroup.card_map_of_injective (MulEquiv.injective _),
    SymplecticFlag.card_isometryGroup 2 _ (tfc_isAlt h) (tfc_nondeg h)
      (by rw [Module.finrank_fin_fun]), h.card_fixedField]
  simp [Finset.prod_Icc_succ_top]

theorem tfc_card_FixBar :
    Nat.card (miyamotoFixBar h) = (2 ^ f) ^ 4 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
  rw [← tfc_card_Sp4 h]
  exact (Nat.card_congr (miyamotoSp4EquivFixBar h).toEquiv).symm

theorem tfc_twoPart_eq_of_card {G : Type*} [Group G] {X : Subgroup G} {k m : ℕ} (hm : ¬ 2 ∣ m)
    (e : Nat.card X = 2 ^ k * m) : twoPart X = 2 ^ k := by
  unfold twoPart
  rw [e, Nat.factorization_mul (by positivity) (fun h0 => hm (by rw [h0]; exact dvd_zero 2)),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hm]
  simp

theorem tfc_not_dvd_mul {a b : ℕ} (ha : 2 ∣ a) (hb : 2 ∣ b) (ha0 : 0 < a) (hb0 : 0 < b) :
    ¬ 2 ∣ (a - 1) * (b - 1) := by
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h1 | h1 <;> omega

theorem tfc_twoPart_FixBar : twoPart (miyamotoFixBar h) = (2 ^ f) ^ 4 := by
  have hf := h.one_le
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  have hodd := tfc_not_dvd_mul (Dvd.dvd.pow h2 (by norm_num : 2 ≠ 0))
    (Dvd.dvd.pow h2 (by norm_num : 4 ≠ 0)) (by positivity) (by positivity)
  have e : Nat.card (miyamotoFixBar h) =
      2 ^ (f * 4) * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1)) := by
    rw [tfc_card_FixBar, pow_mul]
  rw [tfc_twoPart_eq_of_card hodd e, pow_mul]

end CFSG.Quasithin.H13.F431.Un.OL
