module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
public import Mathlib.FieldTheory.Finite.GaloisField
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootSylow
import CFSG.LieType.Steinberg.Collection
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter CFSG.LieType.Steinberg
open scoped MatrixGroups

theorem isSquare_or_isSquare_neg_of_not_isSquare_neg_one {K : Type*} [Field K] [Finite K]
    (h : ¬ IsSquare (-1 : K)) (t : K) : IsSquare t ∨ IsSquare (-t) := by
  classical
  have := Fintype.ofFinite K
  by_cases ht : IsSquare t
  · exact Or.inl ht
  · right
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact ht ⟨0, by ring⟩
    rw [← quadraticChar_one_iff_isSquare (neg_ne_zero.mpr ht0), neg_eq_neg_one_mul, map_mul,
      quadraticChar_neg_one_iff_not_isSquare.mpr h, quadraticChar_neg_one_iff_not_isSquare.mpr ht]
    norm_num

theorem exists_conj_psl2UpperUnipotent_eq {K : Type*} [Field K] {a : K} (ha : a ≠ 0) (x : K) :
    ∃ d : PSL2 K, d * psl2QuotientMap K (sl2UpperUnipotent x) * d⁻¹ =
      psl2QuotientMap K (sl2UpperUnipotent (a ^ 2 * x)) := by
  let A : SL(2, K) := ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩
  have hA : A ∈ sl2Borel K := (sl2_mem_stabilizer_infinity_iff A).mpr rfl
  refine ⟨psl2QuotientMap K A, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul, sl2Borel_conj_upperUnipotent hA]
  rfl

theorem exists_map_conj_zpowers_eq_zpowers_one {K : Type*} [Field K] [Finite K]
    (h : ¬ IsSquare (-1 : K)) {t : K} (ht : t ≠ 0) : ∃ d : PSL2 K,
      (Subgroup.zpowers (psl2QuotientMap K (sl2UpperUnipotent t))).map
          (MulAut.conj d).toMonoidHom =
        Subgroup.zpowers (psl2QuotientMap K (sl2UpperUnipotent 1)) := by
  rcases isSquare_or_isSquare_neg_of_not_isSquare_neg_one h t with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact ht (by simpa using ha)
    obtain ⟨d, hd⟩ := exists_conj_psl2UpperUnipotent_eq (inv_ne_zero ha0) t
    refine ⟨d, ?_⟩
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hd, ha]
    congr 3
    field_simp
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact ht (by simpa using ha)
    obtain ⟨d, hd⟩ := exists_conj_psl2UpperUnipotent_eq (inv_ne_zero ha0) t
    refine ⟨d, ?_⟩
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hd]
    have hat : a⁻¹ ^ 2 * t = -1 := by
      rw [← neg_neg t, ha]
      field_simp
    rw [hat, ← sl2UpperUnipotent_inv, map_inv, Subgroup.zpowers_inv]

theorem exists_map_conj_le_psl2UpperUnipotentSubgroup {K : Type*} [Field K] [Finite K]
    {p n : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ n) {P : Subgroup (PSL2 K)}
    (hP : IsPGroup p P) :
    ∃ c : PSL2 K, P.map (MulAut.conj c).toMonoidHom ≤ psl2UpperUnipotentSubgroup K := by
  obtain ⟨W, hPW⟩ := hP.exists_le_sylow
  obtain ⟨S, hS⟩ := psl2UpperUnipotent_isSylow K hK
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (PSL2 K) W S
  refine ⟨c, ?_⟩
  rw [← hS, ← hc]
  exact Subgroup.map_mono hPW

theorem eq_map_conj_of_map_conj_eq {G : Type*} [Group G] {P Q : Subgroup G} {a b : G}
    (h : P.map (MulAut.conj a).toMonoidHom = Q.map (MulAut.conj b).toMonoidHom) :
    Q = P.map (MulAut.conj (b⁻¹ * a)).toMonoidHom := by
  rw [map_conj_mul, h, ← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem exists_map_conj_eq_zpowers_of_card_eq_three {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 3 ^ n) (h : ¬ IsSquare (-1 : K)) {P : Subgroup (PSL2 K)}
    (hP : Nat.card P = 3) : ∃ c : PSL2 K, P.map (MulAut.conj c).toMonoidHom =
      Subgroup.zpowers (psl2QuotientMap K (sl2UpperUnipotent 1)) := by
  obtain ⟨c, hc⟩ := exists_map_conj_le_psl2UpperUnipotentSubgroup hK
    (IsPGroup.of_card (n := 1) (by rw [hP, pow_one]))
  have hP' : Nat.card (P.map (MulAut.conj c).toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hP]
  obtain ⟨g, hgP', hg1⟩ : ∃ g ∈ P.map (MulAut.conj c).toMonoidHom, g ≠ 1 := by
    rcases (P.map (MulAut.conj c).toMonoidHom).bot_or_exists_ne_one with hbot | hex
    · rw [hbot, Subgroup.card_bot] at hP'
      norm_num at hP'
    · exact hex
  have hzp : P.map (MulAut.conj c).toMonoidHom = Subgroup.zpowers g := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgP') ?_).symm
    have hdvd : orderOf g ∣ 3 := hP' ▸ Subgroup.orderOf_dvd_natCard _ hgP'
    rw [hP', Nat.card_zpowers]
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h3.ge
  obtain ⟨t, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff g).mp (hc hgP')
  have ht : t ≠ 0 := by
    rintro rfl
    exact hg1 (by rw [sl2UpperUnipotent_zero, map_one])
  obtain ⟨d, hd⟩ := exists_map_conj_zpowers_eq_zpowers_one h ht
  exact ⟨d * c, by rw [map_conj_mul, hzp, hd]⟩

theorem exists_conj_eq_of_card_eq_three_psl2 {K : Type*} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K % 4 = 3) {P Q : Subgroup (PSL2 K)} (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3) : ∃ x : PSL2 K, Q = P.map (MulAut.conj x).toMonoidHom := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have hcard : Nat.card K = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hsq : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, not_not, ← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨a, ha⟩ := exists_map_conj_eq_zpowers_of_card_eq_three hcard hsq hP
  obtain ⟨b, hb⟩ := exists_map_conj_eq_zpowers_of_card_eq_three hcard hsq hQ
  exact ⟨_, eq_map_conj_of_map_conj_eq (ha.trans hb.symm)⟩

theorem exists_conj_eq_of_card_eq_three_psl2_27 {P Q : Subgroup (PSL2 (GaloisField 3 3))}
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) :
    ∃ x : PSL2 (GaloisField 3 3), Q = P.map (MulAut.conj x).toMonoidHom :=
  exists_conj_eq_of_card_eq_three_psl2 (by rw [GaloisField.card 3 3 (by norm_num)]; norm_num) hP hQ

theorem eq_map_conj_of_map_mulEquiv_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {P Q : Subgroup X} {y : Y}
    (hy : Q.map e.toMonoidHom = (P.map e.toMonoidHom).map (MulAut.conj y).toMonoidHom) :
    Q = P.map (MulAut.conj (e.symm y)).toMonoidHom := by
  refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
  rw [hy, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext z
  simp [MulAut.conj_apply]

theorem exists_conj_eq_of_card_eq_three_of_mulEquiv_psl2_27 {X : Type*} [Group X]
    (e : X ≃* PSL2 (GaloisField 3 3)) {P Q : Subgroup X} (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3) : ∃ x : X, Q = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨y, hy⟩ := exists_conj_eq_of_card_eq_three_psl2_27
    (P := P.map e.toMonoidHom) (Q := Q.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hP])
    (by rw [Subgroup.card_map_of_injective e.injective, hQ])
  exact ⟨e.symm y, eq_map_conj_of_map_mulEquiv_eq e hy⟩

end CFSG.RankThree.PartTwo.KFacts
