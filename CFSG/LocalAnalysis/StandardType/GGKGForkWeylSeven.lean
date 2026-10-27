module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwNFix
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTorus
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat wordW)
open scoped Matrix

private theorem ggKGW7_weylMat_apply {τ : Tag} (v : WeylGroup τ) (i j : Fin τ.rank) :
    weylMat v i j = (v • (Pi.single j 1 : Fin τ.rank → ℤ)) i := rfl

private theorem ggKGW7_weylMat_mul {τ : Tag} (v w : WeylGroup τ) :
    weylMat (v * w) = weylMat v * weylMat w := by
  ext i j
  rw [ggKGW7_weylMat_apply, mul_smul, ← weylMat_mulVec w, ← weylMat_mulVec v,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

private theorem ggKGW7_weylMat_one {τ : Tag} : weylMat (1 : WeylGroup τ) = 1 := by
  ext i j
  rw [ggKGW7_weylMat_apply, one_smul, Matrix.one_apply, Pi.single_apply]

private theorem ggKGW7_weylMat_injective {τ : Tag} :
    Function.Injective (weylMat (τ := τ)) := by
  intro v w h
  refine ext_single fun i => ?_
  rw [← weylMat_mulVec v, ← weylMat_mulVec w, h]

private theorem ggKGW7_Atw_one {τ : Tag} : Atw (1 : WeylGroup τ) = 1 := by
  rw [Atw, inv_one, ggKGW7_weylMat_one, Matrix.transpose_one]

private theorem ggKGW7_Atw_mul {τ : Tag} (v w : WeylGroup τ) :
    Atw (v * w) = Atw v * Atw w := by
  rw [Atw, Atw, Atw, mul_inv_rev, ggKGW7_weylMat_mul, Matrix.transpose_mul]

private theorem ggKGW7_Atw_injective {τ : Tag} :
    Function.Injective (Atw (τ := τ)) := by
  intro v w h
  have h' : weylMat v⁻¹ = weylMat w⁻¹ := by
    have := congrArg Matrix.transpose h
    simpa only [Atw, Matrix.transpose_transpose] using this
  exact inv_injective (ggKGW7_weylMat_injective h')

private noncomputable def ggKGW7_AtwHom (τ : Tag) :
    WeylGroup τ →* Matrix (Fin τ.rank) (Fin τ.rank) ℤ where
  toFun := Atw
  map_one' := ggKGW7_Atw_one
  map_mul' := ggKGW7_Atw_mul

private theorem ggKGW7_mactC_pow {C : Type} [CommGroup C] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (k : ℕ) (a : Fin r → C) :
    mactC (M ^ k) a = (mactC M)^[k] a := by
  induction k generalizing a with
  | zero => rw [pow_zero, mactC_one, Function.iterate_zero_apply]
  | succ k ih => rw [pow_succ, mactC_mul, ih, Function.iterate_succ_apply]

private theorem ggKGW7_fix_pow {C : Type} [CommGroup C] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (k : ℕ) {a : Fin r → C}
    (ha : mactC M a = a) : mactC (M ^ k) a = a := by
  rw [ggKGW7_mactC_pow]
  exact Function.iterate_fixed ha k

private theorem ggKGW7_fix_iff_zpow {τ : Tag} {C : Type} [CommGroup C] {p : ℕ} (hp : p.Prime)
    {c : WeylGroup τ} (hc : orderOf c = p)
    {h : WeylGroup τ} (hh : h ∈ Subgroup.zpowers c) (hh1 : h ≠ 1) (a : Fin τ.rank → C) :
    mactC (Atw h) a = a ↔ mactC (Atw c) a = a := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at hh
  simp only [Finset.mem_image, Finset.mem_range] at hh
  obtain ⟨k, hklt, hk⟩ := hh
  have hkltp : k < p := by simpa [hc] using hklt
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hh1 hk.symm
  have hkgcd : k.gcd (orderOf c) = 1 := by
    rw [hc, Nat.gcd_comm]
    exact hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk0) hkltp)
  have hc_mem : c ∈ Subgroup.zpowers (c ^ k) := mem_zpowers_pow_iff.2 hkgcd
  rw [mem_zpowers_iff_mem_range_orderOf] at hc_mem
  simp only [Finset.mem_image, Finset.mem_range] at hc_mem
  obtain ⟨j, _, hj⟩ := hc_mem
  have hAtw_h : Atw h = (Atw c) ^ k := by
    rw [← hk]
    exact map_pow (ggKGW7_AtwHom τ) c k
  have hAtw_c : Atw c = (Atw h) ^ j := by
    calc Atw c = Atw ((c ^ k) ^ j) := by rw [hj]
      _ = (Atw (c ^ k)) ^ j := map_pow (ggKGW7_AtwHom τ) (c ^ k) j
      _ = (Atw h) ^ j := by rw [hk]
  constructor
  · intro ha
    have h' := ggKGW7_fix_pow (Atw h) j ha
    rwa [← hAtw_c] at h'
  · intro ha
    have h' := ggKGW7_fix_pow (Atw c) k ha
    rwa [← hAtw_h] at h'

private theorem ggKGW7_card_le_conj {τ : Tag} {C : Type} [CommGroup C] [Finite C]
    (y h : WeylGroup τ) :
    Nat.card {a : Fin τ.rank → C // mactC (Atw (y * h * y⁻¹)) a = a} ≤
    Nat.card {a : Fin τ.rank → C // mactC (Atw h) a = a} := by
  have hAtw : Atw (y * h * y⁻¹) = Atw y * Atw h * Atw y⁻¹ := by
    rw [ggKGW7_Atw_mul, ggKGW7_Atw_mul]
  have hAA' : Atw y * Atw y⁻¹ = 1 := by
    rw [← ggKGW7_Atw_mul, mul_inv_cancel, ggKGW7_Atw_one]
  have hA'A : Atw y⁻¹ * Atw y = 1 := by
    rw [← ggKGW7_Atw_mul, inv_mul_cancel, ggKGW7_Atw_one]
  have hleft : Function.LeftInverse (mactC (C := C) (Atw y))
      (mactC (C := C) (Atw y⁻¹)) := fun x => by
    rw [← mactC_mul, hAA', mactC_one]
  have hconj : ∀ x : Fin τ.rank → C,
      mactC (Atw (y * h * y⁻¹)) x =
        mactC (Atw y) (mactC (Atw h) (mactC (Atw y⁻¹) x)) := by
    intro x
    rw [hAtw, mactC_mul, mactC_mul]
  refine Nat.card_le_card_of_injective
    (fun a : {a : Fin τ.rank → C // mactC (Atw (y * h * y⁻¹)) a = a} =>
      (⟨mactC (Atw y⁻¹) a.1, ?_⟩ : {a : Fin τ.rank → C // mactC (Atw h) a = a})) ?_
  · have hx : mactC (Atw y) (mactC (Atw h) (mactC (Atw y⁻¹) a.1)) = a.1 := by
      rw [← hconj]
      exact a.2
    have h2 := congrArg (mactC (C := C) (Atw y⁻¹)) hx
    rw [← mactC_mul, hA'A, mactC_one] at h2
    exact h2
  · intro a b hab
    have h1 : mactC (Atw y⁻¹) a.1 = mactC (Atw y⁻¹) b.1 := congrArg Subtype.val hab
    apply Subtype.ext
    calc a.1 = mactC (Atw y) (mactC (Atw y⁻¹) a.1) := (hleft a.1).symm
      _ = mactC (Atw y) (mactC (Atw y⁻¹) b.1) := by rw [h1]
      _ = b.1 := hleft b.1

private theorem ggKGW7_exists_conj {τ : Tag} {p : ℕ} (hp : p.Prime) (c : WeylGroup τ)
    (hc : orderOf c = p)
    (hfac : (Nat.card (WeylGroup τ)).factorization p = 1)
    (w : WeylGroup τ) (hw : orderOf w = p) :
    ∃ y : WeylGroup τ, y⁻¹ * w * y ∈ Subgroup.zpowers c := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcw : Nat.card (Subgroup.zpowers c) =
      p ^ (Nat.card (WeylGroup τ)).factorization p := by
    rw [Nat.card_zpowers, hc, hfac, pow_one]
  have hww : Nat.card (Subgroup.zpowers w) =
      p ^ (Nat.card (WeylGroup τ)).factorization p := by
    rw [Nat.card_zpowers, hw, hfac, pow_one]
  let Pc : Sylow p (WeylGroup τ) := Sylow.ofCard (Subgroup.zpowers c) hcw
  let Pw : Sylow p (WeylGroup τ) := Sylow.ofCard (Subgroup.zpowers w) hww
  haveI : MulAction.IsPretransitive (WeylGroup τ) (Sylow p (WeylGroup τ)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (WeylGroup τ) Pc Pw
  refine ⟨y, ?_⟩
  have hmap : (Pw : Subgroup (WeylGroup τ)) =
      (Subgroup.zpowers c).map (MulAut.conj y).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Subgroup.pointwise_smul_def]
    rfl
  have hw_mem : w ∈ (Pw : Subgroup (WeylGroup τ)) := by
    simpa only [Pw, Sylow.coe_ofCard] using Subgroup.mem_zpowers w
  rw [hmap, Subgroup.mem_map] at hw_mem
  obtain ⟨h, hhc, hhconj⟩ := hw_mem
  have hwh : y⁻¹ * w * y = h := by
    have h1 : (MulAut.conj y) h = w := hhconj
    rw [← h1, MulAut.conj_apply]
    group
  rw [hwh]
  exact hhc

private def ggKGW7_M7_E7_5 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ 1, 0,  1,  1,  1,  1, 0;
      0, 1,  0,  1,  1,  1, 0;
      0, 0, -1, -1, -1, -1, 0;
      0, 0,  1,  0,  0,  0, 0;
      0, 0,  0,  1,  0,  0, 0;
      0, 0,  0,  0,  1,  0, 0;
      0, 0,  0,  0,  0,  1, 1 ]

private def ggKGW7_M_E7_5 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := ggKGW7_M7_E7_5

private def ggKGW7_c_E7_5 : WeylGroup Tag.E7 := wordW Tag.E7 [2, 3, 4, 5]

private theorem ggKGW7_Atw_c_E7_5 :
    Atw ggKGW7_c_E7_5 = ggKGW7_M_E7_5 := by
  rw [ggKGW7_c_E7_5, Atw_wordW]
  decide +kernel

private theorem ggKGW7_M_E7_5_pow : ggKGW7_M_E7_5 ^ 5 = 1 := by
  decide +kernel

private theorem ggKGW7_M_E7_5_ne_one : ggKGW7_M_E7_5 ≠ 1 := by
  decide +kernel

private theorem ggKGW7_orderOf_c_E7_5 :
    orderOf ggKGW7_c_E7_5 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply ggKGW7_Atw_injective
    have h : Atw (ggKGW7_c_E7_5 ^ 5) = (Atw ggKGW7_c_E7_5) ^ 5 :=
      map_pow (ggKGW7_AtwHom Tag.E7) ggKGW7_c_E7_5 5
    rw [h, ggKGW7_Atw_c_E7_5, ggKGW7_M_E7_5_pow, ggKGW7_Atw_one]
  · intro h
    have h1 : Atw ggKGW7_c_E7_5 = 1 := by rw [h, ggKGW7_Atw_one]
    rw [ggKGW7_Atw_c_E7_5] at h1
    exact ggKGW7_M_E7_5_ne_one h1

private theorem ggKGW7_fixed_vals_E7_5 {C : Type} [CommGroup C]
    (a : Fin 7 → C) (ha : mactC ggKGW7_M7_E7_5 a = a) :
    a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = 1 := by
  have h6 := congrFun ha 6
  have h5 := congrFun ha 5
  have h4 := congrFun ha 4
  have h3 := congrFun ha 3
  simp [mactC, ggKGW7_M7_E7_5, Fin.prod_univ_seven] at h6 h5 h4 h3
  have ha5 : a 5 = 1 := by
    have h := congrArg (fun x => x * (a 6)⁻¹) h6
    simpa [mul_assoc] using h
  refine ⟨?_, ?_, ?_, ha5⟩
  · rw [h3, h4, h5]; exact ha5
  · rw [h4, h5]; exact ha5
  · rw [h5]; exact ha5

private theorem ggKGW7_card_c_E7_5
    {C : Type} [CommGroup C] (hC : Nat.card C = 5) :
    Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw ggKGW7_c_E7_5) a = a} ≤ 5 ^ 4 := by
  rw [ggKGW7_Atw_c_E7_5]
  change Nat.card {a : Fin 7 → C // mactC ggKGW7_M7_E7_5 a = a} ≤ 5 ^ 4
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hle : Nat.card {a : Fin 7 → C // mactC ggKGW7_M7_E7_5 a = a} ≤
      Nat.card (C × C × C) := by
    refine Nat.card_le_card_of_injective (fun a => (a.1 0, a.1 1, a.1 6)) ?_
    intro a b hab
    apply Subtype.ext
    have ha := ggKGW7_fixed_vals_E7_5 a.1 a.2
    have hb := ggKGW7_fixed_vals_E7_5 b.1 b.2
    have h0 : a.1 0 = b.1 0 := congrArg (fun t => t.1) hab
    have h1 : a.1 1 = b.1 1 := congrArg (fun t => t.2.1) hab
    have h6 : a.1 6 = b.1 6 := congrArg (fun t => t.2.2) hab
    funext i
    fin_cases i <;> simp_all
  calc Nat.card {a : Fin 7 → C // mactC ggKGW7_M7_E7_5 a = a} ≤ Nat.card (C × C × C) := hle
    _ ≤ 5 ^ 4 := by rw [Nat.card_prod, Nat.card_prod, hC]; norm_num

private def ggKGW7_M7_E7_7 : Matrix (Fin 7) (Fin 7) ℤ :=
  !![ -1, 0, -1, -1, -1, -1, -1;
       0, 1,  0,  1,  1,  1,  1;
       1, 0,  0,  0,  0,  0,  0;
       0, 0,  1,  0,  0,  0,  0;
       0, 0,  0,  1,  0,  0,  0;
       0, 0,  0,  0,  1,  0,  0;
       0, 0,  0,  0,  0,  1,  0 ]

private def ggKGW7_M_E7_7 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ := ggKGW7_M7_E7_7

private def ggKGW7_c_E7_7 : WeylGroup Tag.E7 := wordW Tag.E7 [0, 2, 3, 4, 5, 6]

private theorem ggKGW7_Atw_c_E7_7 :
    Atw ggKGW7_c_E7_7 = ggKGW7_M_E7_7 := by
  rw [ggKGW7_c_E7_7, Atw_wordW]
  decide +kernel

private theorem ggKGW7_M_E7_7_pow : ggKGW7_M_E7_7 ^ 7 = 1 := by
  decide +kernel

private theorem ggKGW7_M_E7_7_ne_one : ggKGW7_M_E7_7 ≠ 1 := by
  decide +kernel

private theorem ggKGW7_orderOf_c_E7_7 :
    orderOf ggKGW7_c_E7_7 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply ggKGW7_Atw_injective
    have h : Atw (ggKGW7_c_E7_7 ^ 7) = (Atw ggKGW7_c_E7_7) ^ 7 :=
      map_pow (ggKGW7_AtwHom Tag.E7) ggKGW7_c_E7_7 7
    rw [h, ggKGW7_Atw_c_E7_7, ggKGW7_M_E7_7_pow, ggKGW7_Atw_one]
  · intro h
    have h1 : Atw ggKGW7_c_E7_7 = 1 := by rw [h, ggKGW7_Atw_one]
    rw [ggKGW7_Atw_c_E7_7] at h1
    exact ggKGW7_M_E7_7_ne_one h1

private theorem ggKGW7_fixed_vals_E7_7 {C : Type} [CommGroup C] (hC : Nat.card C = 7)
    (a : Fin 7 → C) (ha : mactC ggKGW7_M7_E7_7 a = a) :
    a 0 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = 1 ∧ a 6 = 1 := by
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have h2 := congrFun ha 2
  have h3 := congrFun ha 3
  have h4 := congrFun ha 4
  have h5 := congrFun ha 5
  have h6 := congrFun ha 6
  have h1 := congrFun ha 1
  simp [mactC, ggKGW7_M7_E7_7, Fin.prod_univ_seven] at h2 h3 h4 h5 h6 h1
  have ha2 : a 2 = a 0 := h2.symm
  have ha3 : a 3 = a 0 := by rw [← h3, ha2]
  have ha4 : a 4 = a 0 := by rw [← h4, ha3]
  have ha5 : a 5 = a 0 := by rw [← h5, ha4]
  have ha6 : a 6 = a 0 := by rw [← h6, ha5]
  have hprod : a 3 * a 4 * a 5 * a 6 = 1 := by
    have hh : a 1 * (a 3 * (a 4 * (a 5 * a 6))) = a 1 * 1 := by
      rw [mul_one]
      simpa only [mul_assoc] using h1
    have h2' : a 3 * (a 4 * (a 5 * a 6)) = 1 := mul_left_cancel hh
    simpa only [mul_assoc] using h2'
  have hpow4 : a 0 ^ 4 = 1 := by
    have h := hprod
    rw [ha3, ha4, ha5, ha6] at h
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h
  have hpow7 : a 0 ^ 7 = 1 := by
    haveI : Fintype C := Fintype.ofFinite C
    have h := pow_card_eq_one (G := C) (x := a 0)
    rwa [← Nat.card_eq_fintype_card, hC] at h
  have hdvd : orderOf (a 0) ∣ 1 := by
    have h4 : orderOf (a 0) ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hpow4
    have h7 : orderOf (a 0) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hpow7
    have := Nat.dvd_gcd h4 h7
    simpa using this
  have ha0 : a 0 = 1 := by
    have h1 : orderOf (a 0) = 1 := Nat.dvd_one.mp hdvd
    exact orderOf_eq_one_iff.mp h1
  exact ⟨ha0, ha2.trans ha0, ha3.trans ha0, ha4.trans ha0, ha5.trans ha0, ha6.trans ha0⟩

private theorem ggKGW7_card_c_E7_7
    {C : Type} [CommGroup C] (hC : Nat.card C = 7) :
    Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw ggKGW7_c_E7_7) a = a} ≤ 7 ^ 2 := by
  rw [ggKGW7_Atw_c_E7_7]
  change Nat.card {a : Fin 7 → C // mactC ggKGW7_M7_E7_7 a = a} ≤ 7 ^ 2
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hle : Nat.card {a : Fin 7 → C // mactC ggKGW7_M7_E7_7 a = a} ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun a => a.1 1) ?_
    intro a b hab
    apply Subtype.ext
    have ha := ggKGW7_fixed_vals_E7_7 hC a.1 a.2
    have hb := ggKGW7_fixed_vals_E7_7 hC b.1 b.2
    have h1 : a.1 1 = b.1 1 := hab
    funext i
    fin_cases i <;> simp_all
  calc Nat.card {a : Fin 7 → C // mactC ggKGW7_M7_E7_7 a = a} ≤ Nat.card C := hle
    _ ≤ 7 ^ 2 := by rw [hC]; norm_num

private def ggKGW7_M8_E8_7 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![ 1, 0,  1,  1,  1,  1,  1,  1;
      0, 1,  0,  1,  1,  1,  1,  1;
      0, 0, -1, -1, -1, -1, -1, -1;
      0, 0,  1,  0,  0,  0,  0,  0;
      0, 0,  0,  1,  0,  0,  0,  0;
      0, 0,  0,  0,  1,  0,  0,  0;
      0, 0,  0,  0,  0,  1,  0,  0;
      0, 0,  0,  0,  0,  0,  1,  0 ]

private def ggKGW7_M_E8_7 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := ggKGW7_M8_E8_7

private def ggKGW7_c_E8_7 : WeylGroup Tag.E8 := wordW Tag.E8 [2, 3, 4, 5, 6, 7]

private theorem ggKGW7_Atw_c_E8_7 :
    Atw ggKGW7_c_E8_7 = ggKGW7_M_E8_7 := by
  rw [ggKGW7_c_E8_7, Atw_wordW]
  decide +kernel

private theorem ggKGW7_M_E8_7_pow : ggKGW7_M_E8_7 ^ 7 = 1 := by
  decide +kernel

private theorem ggKGW7_M_E8_7_ne_one : ggKGW7_M_E8_7 ≠ 1 := by
  decide +kernel

private theorem ggKGW7_orderOf_c_E8_7 :
    orderOf ggKGW7_c_E8_7 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply ggKGW7_Atw_injective
    have h : Atw (ggKGW7_c_E8_7 ^ 7) = (Atw ggKGW7_c_E8_7) ^ 7 :=
      map_pow (ggKGW7_AtwHom Tag.E8) ggKGW7_c_E8_7 7
    rw [h, ggKGW7_Atw_c_E8_7, ggKGW7_M_E8_7_pow, ggKGW7_Atw_one]
  · intro h
    have h1 : Atw ggKGW7_c_E8_7 = 1 := by rw [h, ggKGW7_Atw_one]
    rw [ggKGW7_Atw_c_E8_7] at h1
    exact ggKGW7_M_E8_7_ne_one h1

private theorem ggKGW7_fixed_vals_E8_7 {C : Type} [CommGroup C]
    (a : Fin 8 → C) (ha : mactC ggKGW7_M8_E8_7 a = a) :
    a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = 1 ∧ a 6 = 1 ∧ a 7 = 1 := by
  have h7 := congrFun ha 7
  have h6 := congrFun ha 6
  have h5 := congrFun ha 5
  have h4 := congrFun ha 4
  have h3 := congrFun ha 3
  have h1 := congrFun ha 1
  have h0 := congrFun ha 0
  simp [mactC, ggKGW7_M8_E8_7, Fin.prod_univ_eight] at h7 h6 h5 h4 h3 h1 h0
  have ha3 : a 3 = a 2 := h3.symm
  have ha4 : a 4 = a 2 := by rw [← h4, ha3]
  have ha5 : a 5 = a 2 := by rw [← h5, ha4]
  have ha6 : a 6 = a 2 := by rw [← h6, ha5]
  have ha7 : a 7 = a 2 := by rw [← h7, ha6]
  have hprod5 : a 3 * a 4 * a 5 * a 6 * a 7 = 1 := by
    have hh : a 1 * (a 3 * (a 4 * (a 5 * (a 6 * a 7)))) = a 1 * 1 := by
      rw [mul_one]
      simpa only [mul_assoc] using h1
    have h2' : a 3 * (a 4 * (a 5 * (a 6 * a 7))) = 1 := mul_left_cancel hh
    simpa only [mul_assoc] using h2'
  have hprod6 : a 2 * a 3 * a 4 * a 5 * a 6 * a 7 = 1 := by
    have hh : a 0 * (a 2 * (a 3 * (a 4 * (a 5 * (a 6 * a 7))))) = a 0 * 1 := by
      rw [mul_one]
      simpa only [mul_assoc] using h0
    have h2' : a 2 * (a 3 * (a 4 * (a 5 * (a 6 * a 7)))) = 1 := mul_left_cancel hh
    simpa only [mul_assoc] using h2'
  have hpow5 : a 2 ^ 5 = 1 := by
    have h := hprod5
    rw [ha3, ha4, ha5, ha6, ha7] at h
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h
  have hpow6 : a 2 ^ 6 = 1 := by
    have h := hprod6
    rw [ha3, ha4, ha5, ha6, ha7] at h
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h
  have hdvd : orderOf (a 2) ∣ 1 := by
    have h5 : orderOf (a 2) ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hpow5
    have h6 : orderOf (a 2) ∣ 6 := orderOf_dvd_iff_pow_eq_one.mpr hpow6
    have := Nat.dvd_gcd h5 h6
    simpa using this
  have ha2 : a 2 = 1 := by
    have h1 : orderOf (a 2) = 1 := Nat.dvd_one.mp hdvd
    exact orderOf_eq_one_iff.mp h1
  exact ⟨ha2, ha3.trans ha2, ha4.trans ha2, ha5.trans ha2, ha6.trans ha2, ha7.trans ha2⟩

private theorem ggKGW7_card_c_E8_7
    {C : Type} [CommGroup C] (hC : Nat.card C = 7) :
    Nat.card {a : Fin Tag.E8.rank → C // mactC (Atw ggKGW7_c_E8_7) a = a} ≤ 7 ^ 3 := by
  rw [ggKGW7_Atw_c_E8_7]
  change Nat.card {a : Fin 8 → C // mactC ggKGW7_M8_E8_7 a = a} ≤ 7 ^ 3
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hle : Nat.card {a : Fin 8 → C // mactC ggKGW7_M8_E8_7 a = a} ≤ Nat.card (C × C) := by
    refine Nat.card_le_card_of_injective (fun a => (a.1 0, a.1 1)) ?_
    intro a b hab
    apply Subtype.ext
    have ha := ggKGW7_fixed_vals_E8_7 a.1 a.2
    have hb := ggKGW7_fixed_vals_E8_7 b.1 b.2
    have h0 : a.1 0 = b.1 0 := congrArg Prod.fst hab
    have h1 : a.1 1 = b.1 1 := congrArg Prod.snd hab
    funext i
    fin_cases i <;> simp_all
  calc Nat.card {a : Fin 8 → C // mactC ggKGW7_M8_E8_7 a = a} ≤ Nat.card (C × C) := hle
    _ ≤ 7 ^ 3 := by rw [Nat.card_prod, hC]; norm_num


theorem weylE7_five_fixed
    {C : Type} [CommGroup C] (hC : Nat.card C = 5) {w : WeylGroup Tag.E7} (hw : orderOf w = 5) :
    Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw w) a = a} ≤ 5 ^ 4 := by
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hp : Nat.Prime 5 := by norm_num
  have hfac : (Nat.card (WeylGroup Tag.E7)).factorization 5 = 1 := by
    rw [card_weylGroup_E7']
    decide +kernel
  obtain ⟨y, hy⟩ := ggKGW7_exists_conj (τ := Tag.E7) hp ggKGW7_c_E7_5 ggKGW7_orderOf_c_E7_5
    hfac w hw
  set h : WeylGroup Tag.E7 := y⁻¹ * w * y with hh_def
  have hh_mem : h ∈ Subgroup.zpowers ggKGW7_c_E7_5 := by rw [hh_def]; exact hy
  have hw_eq : w = y * h * y⁻¹ := by rw [hh_def]; group
  have hh1 : h ≠ 1 := by
    intro h1
    have hone : w = 1 := by rw [hw_eq, h1, mul_one, mul_inv_cancel]
    rw [hone, orderOf_one] at hw
    norm_num at hw
  rw [hw_eq]
  calc Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw (y * h * y⁻¹)) a = a}
      ≤ Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw h) a = a} :=
        ggKGW7_card_le_conj y h
    _ = Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw ggKGW7_c_E7_5) a = a} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin Tag.E7.rank → C))
          (p := fun a => mactC (Atw h) a = a)
          (q := fun a => mactC (Atw ggKGW7_c_E7_5) a = a)
          fun a => ggKGW7_fix_iff_zpow hp ggKGW7_orderOf_c_E7_5 hh_mem hh1 a)
    _ ≤ 5 ^ 4 := ggKGW7_card_c_E7_5 hC

theorem weylE7_seven_fixed
    {C : Type} [CommGroup C] (hC : Nat.card C = 7) {w : WeylGroup Tag.E7} (hw : orderOf w = 7) :
    Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw w) a = a} ≤ 7 ^ 2 := by
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hp : Nat.Prime 7 := by norm_num
  have hfac : (Nat.card (WeylGroup Tag.E7)).factorization 7 = 1 := by
    rw [card_weylGroup_E7']
    decide +kernel
  obtain ⟨y, hy⟩ := ggKGW7_exists_conj (τ := Tag.E7) hp ggKGW7_c_E7_7 ggKGW7_orderOf_c_E7_7
    hfac w hw
  set h : WeylGroup Tag.E7 := y⁻¹ * w * y with hh_def
  have hh_mem : h ∈ Subgroup.zpowers ggKGW7_c_E7_7 := by rw [hh_def]; exact hy
  have hw_eq : w = y * h * y⁻¹ := by rw [hh_def]; group
  have hh1 : h ≠ 1 := by
    intro h1
    have hone : w = 1 := by rw [hw_eq, h1, mul_one, mul_inv_cancel]
    rw [hone, orderOf_one] at hw
    norm_num at hw
  rw [hw_eq]
  calc Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw (y * h * y⁻¹)) a = a}
      ≤ Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw h) a = a} :=
        ggKGW7_card_le_conj y h
    _ = Nat.card {a : Fin Tag.E7.rank → C // mactC (Atw ggKGW7_c_E7_7) a = a} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin Tag.E7.rank → C))
          (p := fun a => mactC (Atw h) a = a)
          (q := fun a => mactC (Atw ggKGW7_c_E7_7) a = a)
          fun a => ggKGW7_fix_iff_zpow hp ggKGW7_orderOf_c_E7_7 hh_mem hh1 a)
    _ ≤ 7 ^ 2 := ggKGW7_card_c_E7_7 hC

theorem weylE8_seven_fixed
    {C : Type} [CommGroup C] (hC : Nat.card C = 7) {w : WeylGroup Tag.E8} (hw : orderOf w = 7) :
    Nat.card {a : Fin Tag.E8.rank → C // mactC (Atw w) a = a} ≤ 7 ^ 3 := by
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hp : Nat.Prime 7 := by norm_num
  have hfac : (Nat.card (WeylGroup Tag.E8)).factorization 7 = 1 := by
    rw [card_weylGroup_E8']
    decide +kernel
  obtain ⟨y, hy⟩ := ggKGW7_exists_conj (τ := Tag.E8) hp ggKGW7_c_E8_7 ggKGW7_orderOf_c_E8_7
    hfac w hw
  set h : WeylGroup Tag.E8 := y⁻¹ * w * y with hh_def
  have hh_mem : h ∈ Subgroup.zpowers ggKGW7_c_E8_7 := by rw [hh_def]; exact hy
  have hw_eq : w = y * h * y⁻¹ := by rw [hh_def]; group
  have hh1 : h ≠ 1 := by
    intro h1
    have hone : w = 1 := by rw [hw_eq, h1, mul_one, mul_inv_cancel]
    rw [hone, orderOf_one] at hw
    norm_num at hw
  rw [hw_eq]
  calc Nat.card {a : Fin Tag.E8.rank → C // mactC (Atw (y * h * y⁻¹)) a = a}
      ≤ Nat.card {a : Fin Tag.E8.rank → C // mactC (Atw h) a = a} :=
        ggKGW7_card_le_conj y h
    _ = Nat.card {a : Fin Tag.E8.rank → C // mactC (Atw ggKGW7_c_E8_7) a = a} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin Tag.E8.rank → C))
          (p := fun a => mactC (Atw h) a = a)
          (q := fun a => mactC (Atw ggKGW7_c_E8_7) a = a)
          fun a => ggKGW7_fix_iff_zpow hp ggKGW7_orderOf_c_E8_7 hh_mem hh1 a)
    _ ≤ 7 ^ 3 := ggKGW7_card_c_E8_7 hC

end CFSG.StandardType

end
