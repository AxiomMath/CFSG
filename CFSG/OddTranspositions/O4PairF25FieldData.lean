module

public import CFSG.OddTranspositions.O4PairF25Model
public import CFSG.OddTranspositions.O4PairFixedField
public import CFSG.Dihedral.Glauberman.DicksonMaxSubfield
public import CFSG.Walter.PSL2Facts.FieldAut

public section

namespace CFSG.OddTranspositions.QZ

local instance factPrimeFiveData : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

open Polynomial
open CFSG.GorensteinWalter

noncomputable def sqrt3 : K25 := ringEquiv_F25c (AdjoinRoot.root poly25)

theorem sqrt3_sq : sqrt3 ^ 2 = (3 : K25) := by
  have hdvd : poly25 ∣ (X ^ 2 - C 3 : (ZMod 5)[X]) := dvd_refl _
  have h1 : AdjoinRoot.mk poly25 (X ^ 2 - C 3 : (ZMod 5)[X]) = 0 :=
    (AdjoinRoot.mk_eq_zero (f := poly25)).mpr hdvd
  have h2 : AdjoinRoot.mk poly25 (X ^ 2 - C 3 : (ZMod 5)[X]) =
      (AdjoinRoot.root poly25) ^ 2 - AdjoinRoot.mk poly25 (C 3) := by
    rw [map_sub, map_pow, AdjoinRoot.mk_X]
  rw [h2, AdjoinRoot.mk_C] at h1
  have h3 : AdjoinRoot.of poly25 (3 : ZMod 5) = (3 : F25c) :=
    map_natCast (AdjoinRoot.of poly25) 3
  rw [h3] at h1
  have hroot : (AdjoinRoot.root poly25) ^ 2 = (3 : F25c) := sub_eq_zero.mp h1
  calc sqrt3 ^ 2 = ringEquiv_F25c ((AdjoinRoot.root poly25) ^ 2) := by
        rw [sqrt3, map_pow]
    _ = ringEquiv_F25c (3 : F25c) := by rw [hroot]
    _ = (3 : K25) := map_natCast ringEquiv_F25c 3

theorem sqrt3_ne_zero : sqrt3 ≠ 0 := by
  intro h
  have hroot : AdjoinRoot.root poly25 = 0 :=
    ringEquiv_F25c.injective (by
      rw [map_zero]
      simpa [sqrt3] using h)
  have hdvd : poly25 ∣ (X : (ZMod 5)[X]) := by
    have h0 : AdjoinRoot.mk poly25 (X : (ZMod 5)[X]) = 0 := by
      rw [AdjoinRoot.mk_X]
      exact hroot
    exact (AdjoinRoot.mk_eq_zero (f := poly25)).mp h0
  have hne : (X : (ZMod 5)[X]) ≠ 0 := Polynomial.X_ne_zero
  have hle : poly25.natDegree ≤ (X : (ZMod 5)[X]).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hne
  rw [natDegree_poly25, Polynomial.natDegree_X] at hle
  norm_num at hle

theorem frob25_sqrt3 : frob25 sqrt3 = -sqrt3 := by
  have hsq : sqrt3 ^ 2 = (3 : K25) := sqrt3_sq
  have h9 : ((9 : ℕ) : K25) = -1 := by
    have h10 : ((10 : ℕ) : K25) = 0 :=
      (CharP.cast_eq_zero_iff K25 5 10).mpr (by norm_num)
    rw [eq_neg_iff_add_eq_zero]
    calc ((9 : ℕ) : K25) + 1 = ((10 : ℕ) : K25) := by
          rw [← Nat.cast_one, ← Nat.cast_add]
      _ = 0 := h10
  have hsplit : sqrt3 ^ 5 = sqrt3 ^ 4 * sqrt3 := by
    simpa using pow_succ sqrt3 4
  have hfour : sqrt3 ^ 4 = (sqrt3 ^ 2) ^ 2 := by
    simpa using pow_mul sqrt3 2 2
  rw [frob25, frobeniusEquiv_def]
  calc sqrt3 ^ 5 = ((9 : ℕ) : K25) * sqrt3 := by
        rw [hsplit, hfour, hsq]
        norm_num
    _ = (-1 : K25) * sqrt3 := by rw [h9]
    _ = -sqrt3 := by rw [neg_one_mul]

noncomputable def fixedSubfield : Subfield K25 :=
  FixedPoints.subfield (Subgroup.zpowers frob25) K25

theorem mem_fixedSubfield {x : K25} : x ∈ fixedSubfield ↔ frob25 x = x := by
  have h := CFSG.Walter.mem_fixedSubfield_iff frob25 x
  simpa [fixedSubfield] using h

theorem card_fixedSubfield : Nat.card fixedSubfield = 5 := by
  have h :=
    (CFSG.Walter.card_fixedSubfield_galoisField (p := 5) (f := 2) (by norm_num) frob25).2
  rw [orderOf_frob25] at h
  have h' : 5 ^ (2 / 2) = 5 := by norm_num
  rw [h'] at h
  simpa [fixedSubfield] using h

theorem fixedSubfield_eq_primeField :
    (fixedSubfield : Set K25) = Set.range (algebraMap (ZMod 5) K25) := by
  ext x
  constructor
  · intro hx
    have h5 : x ^ 5 = x := by
      have h := mem_fixedSubfield.mp hx
      simpa [frob25, frobenius_def] using h
    exact (pow_five_eq_self_iff x).mp h5
  · rintro ⟨a, rfl⟩
    change (algebraMap (ZMod 5) K25 a) ∈ fixedSubfield
    rw [mem_fixedSubfield]
    have h5 : (algebraMap (ZMod 5) K25 a) ^ 5 = algebraMap (ZMod 5) K25 a :=
      (pow_five_eq_self_iff (algebraMap (ZMod 5) K25 a)).mpr ⟨a, rfl⟩
    simpa [frob25, frobenius_def] using h5

theorem sqrt3_not_mem_fixedSubfield : sqrt3 ∉ fixedSubfield := by
  intro h
  have hfix : frob25 sqrt3 = sqrt3 := mem_fixedSubfield.mp h
  rw [frob25_sqrt3] at hfix
  have hsum : sqrt3 + sqrt3 = 0 := neg_eq_iff_add_eq_zero.mp hfix
  have h2 : (2 : K25) * sqrt3 = 0 := by
    rw [two_mul]
    exact hsum
  rcases mul_eq_zero.mp h2 with hzero | hzero
  · have hdvd : 5 ∣ 2 := (CharP.cast_eq_zero_iff K25 5 2).mp hzero
    norm_num at hdvd
  · exact sqrt3_ne_zero hzero

theorem isSquare_fixedSubfield : ∀ x : fixedSubfield, IsSquare (x : K25) := by
  intro x
  haveI : Fintype K25 := Fintype.ofFinite K25
  by_cases hx0 : (x : K25) = 0
  · rw [hx0]
    exact ⟨0, by norm_num⟩
  · have hchar : ringChar K25 ≠ 2 := by
      have h5 : ringChar K25 = 5 := ringChar.eq K25 5
      rw [h5]
      norm_num
    have hcard : Fintype.card K25 = 25 := by
      rw [← Nat.card_eq_fintype_card]
      exact card_K25
    have hx5 : (x : K25) ^ 5 = (x : K25) := by
      have h := mem_fixedSubfield.mp x.2
      simpa [frob25, frobenius_def] using h
    have hx4 : (x : K25) ^ 4 = 1 := by
      have h : (x : K25) ^ 4 * (x : K25) = 1 * (x : K25) := by
        rw [← pow_succ, hx5, one_mul]
      exact mul_right_cancel₀ hx0 h
    have hx12 : (x : K25) ^ 12 = 1 := by
      rw [show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, hx4, one_pow]
    rw [FiniteField.isSquare_iff hchar hx0, hcard]
    have hdiv : 25 / 2 = 12 := by norm_num
    rw [hdiv]
    exact hx12

theorem card_PGL2_fixedSubfield : Nat.card (PGL2 fixedSubfield) = 120 := by
  rw [CFSG.GorensteinWalter.pgl2_card_formula fixedSubfield, card_fixedSubfield]
  norm_num

theorem card_subfieldSubgroup_fixedSubfield :
    Nat.card (CFSG.Glauberman.Dickson.MaxSubfield.subfieldSubgroup fixedSubfield) = 120 := by
  rw [CFSG.Glauberman.Dickson.MaxSubfield.card_subfieldSubgroup_eq fixedSubfield
    isSquare_fixedSubfield]
  exact card_PGL2_fixedSubfield

end CFSG.OddTranspositions.QZ
