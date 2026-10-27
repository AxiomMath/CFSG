module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Final
public import CFSG.RankThree.PartTwo.Sec8.Hering418RNine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Main
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryTools
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofL3
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec8.Hering418Even
public import CFSG.RankThree.PartTwo.Sec8.Hering418Odd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

private lemma matrix_pow_three_eq_one {F : Type*} [Field F] [CharP F 3]
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M ^ 9 = 1) : M ^ 3 = 1 := by
  have hc : Commute M 1 := Commute.one_right M
  have hN9 : (M - 1) ^ 9 = 0 := by
    have h9 := sub_pow_char_pow_of_commute (p := 3) (n := 2) hc
    norm_num at h9
    rw [h9, hM, sub_self]
  have hnil : IsNilpotent (M - 1) := ⟨9, hN9⟩
  have hcp : (M - 1).charpoly = Polynomial.X ^ 2 := by
    rw [← sub_eq_zero]
    apply IsNilpotent.eq_zero
    simpa using Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
  have hsq : (M - 1) ^ 2 = 0 := by
    have h := Matrix.aeval_self_charpoly (M - 1)
    rw [hcp, Polynomial.aeval_X_pow] at h
    exact h
  have hcube : (M - 1) ^ 3 = 0 := by
    rw [pow_succ, hsq, zero_mul]
  have h3 := sub_pow_char_of_commute (p := 3) hc
  rw [hcube, one_pow] at h3
  exact sub_eq_zero.mp h3.symm

theorem pow_three_eq_one_of_pow_nine_eq_one {F : Type*} [Field F] [CharP F 3]
    (y : projSL 2 F) (h : y ^ 9 = 1) : y ^ 3 = 1 := by
  obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp y.2
  have hdet : Matrix.GeneralLinearGroup.det g = 1 := MonoidHom.mem_ker.mp hg
  have hy9 : Matrix.ProjGenLinGroup.mk (g ^ 9) = 1 := by
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
    rw [map_pow, hgy, h']
  have hc9 : g ^ 9 ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Matrix.ProjGenLinGroup.mk_eq_one.mp hy9
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc9
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hc9
  have hu2 : u ^ 2 = 1 := by
    have h2 := congrArg Matrix.GeneralLinearGroup.det hu
    rw [Matrix.GeneralLinearGroup.det_scalar, map_pow, hdet, one_pow] at h2
    simpa using h2
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) u) g := by
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨u, rfl⟩
    exact (Subgroup.mem_center_iff.mp hz g).symm
  have hu10 : u ^ 9 * u = 1 := by
    rw [← pow_succ, show (9 + 1 : ℕ) = 2 * 5 by norm_num, pow_mul, hu2, one_pow]
  have hh9 : (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) ^ 9 = 1 := by
    rw [hcomm.mul_pow, ← hu, ← map_pow, ← map_mul, hu10, map_one]
  have hh3 : (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) ^ 3 = 1 := by
    apply Units.ext
    have hM9 := congrArg Units.val hh9
    rw [Units.val_pow_eq_pow_val, Units.val_one] at hM9
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact matrix_pow_three_eq_one _ hM9
  have hmk : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) =
      Matrix.ProjGenLinGroup.mk g := by
    rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hgy, ← hmk, ← map_pow, hh3, map_one]

theorem not_nine_dvd_orderOf_of_isOfFinOrder {F : Type*} [Field F] [CharP F 3]
    (x : projSL 2 F) (hx : IsOfFinOrder x) : ¬ 9 ∣ orderOf x := by
  rintro ⟨k, hk⟩
  have hpos : 0 < orderOf x := orderOf_pos_iff.mpr hx
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hdvd : k ∣ orderOf x := ⟨9, by rw [hk, Nat.mul_comm]⟩
  have hy : orderOf (x ^ k) = 9 := by
    rw [orderOf_pow_of_dvd hk0 hdvd, hk, Nat.mul_div_cancel 9 (Nat.pos_of_ne_zero hk0)]
  have hy9 : (x ^ k) ^ 9 = 1 := by
    have := pow_orderOf_eq_one (x ^ k)
    rwa [hy] at this
  have hy3 : (x ^ k) ^ 3 = 1 := pow_three_eq_one_of_pow_nine_eq_one (x ^ k) hy9
  have hdvd3 : orderOf (x ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
  rw [hy] at hdvd3
  norm_num at hdvd3


theorem noNineDvd_quot_of_oneRes {X : Type} [Group X] [Finite X] (hX : IsList46OneRes X) :
    NoNineDvd (X ⧸ Subgroup.center X) := by
  obtain ⟨e, he, h3e, ⟨φ⟩⟩ := hX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (projSL 2 (GaloisField 3 e)) := Finite.of_equiv X φ.toEquiv
  intro x hx
  obtain ⟨x0, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : 9 ∣ orderOf x0 := hx.trans (orderOf_map_dvd (QuotientGroup.mk' _) x0)
  have h2 : orderOf (φ x0) = orderOf x0 := MulEquiv.orderOf_eq φ x0
  exact not_nine_dvd_orderOf_of_isOfFinOrder (φ x0) (isOfFinOrder_of_finite _) (h2 ▸ h1)

section Final


theorem kF418ModelOn_oneRes : KF418ModelOn (fun X _ => IsList46OneRes X) :=
  kF418ModelOn_of_no_nine (fun _ _ n hn hq ht => hasNineQuot_of_isType418 hn hq ht)
    (fun _ _ _ _ hX => noNineDvd_quot_of_oneRes hX)

end Final

end CFSG.RankThree.PartTwo.Sec8.Hering418
