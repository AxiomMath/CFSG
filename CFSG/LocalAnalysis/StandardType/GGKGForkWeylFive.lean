module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcCentTwNFix
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Index
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTorus
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat wordW)
open scoped Matrix

private theorem ggKGW5_weylMat_apply {τ : Tag} (v : WeylGroup τ) (i j : Fin τ.rank) :
    weylMat v i j = (v • (Pi.single j 1 : Fin τ.rank → ℤ)) i := rfl

private theorem ggKGW5_weylMat_mul {τ : Tag} (v w : WeylGroup τ) :
    weylMat (v * w) = weylMat v * weylMat w := by
  ext i j
  rw [ggKGW5_weylMat_apply, mul_smul, ← weylMat_mulVec w, ← weylMat_mulVec v,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

private theorem ggKGW5_weylMat_one {τ : Tag} : weylMat (1 : WeylGroup τ) = 1 := by
  ext i j
  rw [ggKGW5_weylMat_apply, one_smul, Matrix.one_apply, Pi.single_apply]

private theorem ggKGW5_weylMat_injective {τ : Tag} :
    Function.Injective (weylMat (τ := τ)) := by
  intro v w h
  refine ext_single fun i => ?_
  rw [← weylMat_mulVec v, ← weylMat_mulVec w, h]

private theorem ggKGW5_Atw_one {τ : Tag} : Atw (1 : WeylGroup τ) = 1 := by
  rw [Atw, inv_one, ggKGW5_weylMat_one, Matrix.transpose_one]

private theorem ggKGW5_Atw_mul {τ : Tag} (v w : WeylGroup τ) :
    Atw (v * w) = Atw v * Atw w := by
  rw [Atw, Atw, Atw, mul_inv_rev, ggKGW5_weylMat_mul, Matrix.transpose_mul]

private theorem ggKGW5_Atw_injective {τ : Tag} :
    Function.Injective (Atw (τ := τ)) := by
  intro v w h
  have h' : weylMat v⁻¹ = weylMat w⁻¹ := by
    have := congrArg Matrix.transpose h
    simpa only [Atw, Matrix.transpose_transpose] using this
  exact inv_injective (ggKGW5_weylMat_injective h')

private noncomputable def ggKGW5_AtwHom (τ : Tag) :
    WeylGroup τ →* Matrix (Fin τ.rank) (Fin τ.rank) ℤ where
  toFun := Atw
  map_one' := ggKGW5_Atw_one
  map_mul' := ggKGW5_Atw_mul

private def ggKGW5_M6 : Matrix (Fin 6) (Fin 6) ℤ :=
  !![ -1, 0, -1, -1, -1, 0;
      0, 1, 0, 1, 1, 0;
      1, 0, 0, 0, 0, 0;
      0, 0, 1, 0, 0, 0;
      0, 0, 0, 1, 0, 0;
      0, 0, 0, 0, 1, 1 ]

private def ggKGW5_M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ := ggKGW5_M6

private def ggKGW5_c : WeylGroup Tag.E6 := wordW Tag.E6 [0, 2, 3, 4]

private theorem ggKGW5_Atw_c :
    Atw ggKGW5_c = ggKGW5_M := by
  rw [ggKGW5_c, Atw_wordW]
  decide +kernel

private theorem ggKGW5_M_pow_five : ggKGW5_M ^ 5 = 1 := by
  decide +kernel

private theorem ggKGW5_M_ne_one : ggKGW5_M ≠ 1 := by
  decide +kernel

private theorem ggKGW5_orderOf_c :
    orderOf ggKGW5_c = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply ggKGW5_Atw_injective
    have h : Atw (ggKGW5_c ^ 5) = (Atw ggKGW5_c) ^ 5 :=
      map_pow (ggKGW5_AtwHom Tag.E6) ggKGW5_c 5
    rw [h, ggKGW5_Atw_c, ggKGW5_M_pow_five, ggKGW5_Atw_one]
  · intro h
    have h1 : Atw ggKGW5_c = 1 := by rw [h, ggKGW5_Atw_one]
    rw [ggKGW5_Atw_c] at h1
    exact ggKGW5_M_ne_one h1

private theorem ggKGW5_mactC_pow {C : Type} [CommGroup C] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (k : ℕ) (a : Fin r → C) :
    mactC (M ^ k) a = (mactC M)^[k] a := by
  induction k generalizing a with
  | zero => rw [pow_zero, mactC_one, Function.iterate_zero_apply]
  | succ k ih => rw [pow_succ, mactC_mul, ih, Function.iterate_succ_apply]

private theorem ggKGW5_fix_pow {C : Type} [CommGroup C] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℤ) (k : ℕ) {a : Fin r → C}
    (ha : mactC M a = a) : mactC (M ^ k) a = a := by
  rw [ggKGW5_mactC_pow]
  exact Function.iterate_fixed ha k

private theorem ggKGW5_fixed_vals {C : Type} [CommGroup C]
    (a : Fin 6 → C) (ha : mactC ggKGW5_M6 a = a) :
    a 0 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 := by
  have h2 := congrFun ha 2
  have h3 := congrFun ha 3
  have h4 := congrFun ha 4
  have h5 := congrFun ha 5
  simp [mactC, ggKGW5_M6, Fin.prod_univ_six] at h2 h3 h4 h5
  exact ⟨by rw [h2, h3, h4, h5], by rw [h3, h4, h5], by rw [h4, h5], h5⟩

private theorem ggKGW5_fix_iff_zpow
    {C : Type} [CommGroup C] {h : WeylGroup Tag.E6}
    (hh : h ∈ Subgroup.zpowers ggKGW5_c) (hh1 : h ≠ 1) (a : Fin Tag.E6.rank → C) :
    mactC (Atw h) a = a ↔ mactC (Atw ggKGW5_c) a = a := by
  classical
  have hordc : orderOf ggKGW5_c = 5 := ggKGW5_orderOf_c
  rw [mem_zpowers_iff_mem_range_orderOf] at hh
  simp only [Finset.mem_image, Finset.mem_range] at hh
  obtain ⟨k, hklt, hk⟩ := hh
  have hklt5 : k < 5 := by simpa [hordc] using hklt
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hh1 hk.symm
  have hkgcd : k.gcd (orderOf ggKGW5_c) = 1 := by
    rw [hordc]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    interval_cases k <;> decide
  have hc_mem : ggKGW5_c ∈ Subgroup.zpowers (ggKGW5_c ^ k) :=
    mem_zpowers_pow_iff.2 hkgcd
  rw [mem_zpowers_iff_mem_range_orderOf] at hc_mem
  simp only [Finset.mem_image, Finset.mem_range] at hc_mem
  obtain ⟨j, _, hj⟩ := hc_mem
  have hAtw_h : Atw h = (Atw ggKGW5_c) ^ k := by
    rw [← hk]
    exact map_pow (ggKGW5_AtwHom Tag.E6) ggKGW5_c k
  have hAtw_c : Atw ggKGW5_c = (Atw h) ^ j := by
    calc Atw ggKGW5_c = Atw ((ggKGW5_c ^ k) ^ j) := by rw [hj]
      _ = (Atw (ggKGW5_c ^ k)) ^ j := map_pow (ggKGW5_AtwHom Tag.E6) (ggKGW5_c ^ k) j
      _ = (Atw h) ^ j := by rw [hk]
  constructor
  · intro ha
    have h' := ggKGW5_fix_pow (Atw h) j ha
    rwa [← hAtw_c] at h'
  · intro ha
    have h' := ggKGW5_fix_pow (Atw ggKGW5_c) k ha
    rwa [← hAtw_h] at h'

private theorem ggKGW5_card_le_conj {C : Type} [CommGroup C] [Finite C]
    (y h : WeylGroup Tag.E6) :
    Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw (y * h * y⁻¹)) a = a} ≤
    Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw h) a = a} := by
  have hAtw : Atw (y * h * y⁻¹) = Atw y * Atw h * Atw y⁻¹ := by
    rw [ggKGW5_Atw_mul, ggKGW5_Atw_mul]
  have hAA' : Atw y * Atw y⁻¹ = 1 := by
    rw [← ggKGW5_Atw_mul, mul_inv_cancel, ggKGW5_Atw_one]
  have hA'A : Atw y⁻¹ * Atw y = 1 := by
    rw [← ggKGW5_Atw_mul, inv_mul_cancel, ggKGW5_Atw_one]
  have hleft : Function.LeftInverse (mactC (C := C) (Atw y))
      (mactC (C := C) (Atw y⁻¹)) := fun x => by
    rw [← mactC_mul, hAA', mactC_one]
  have hconj : ∀ x : Fin Tag.E6.rank → C,
      mactC (Atw (y * h * y⁻¹)) x =
        mactC (Atw y) (mactC (Atw h) (mactC (Atw y⁻¹) x)) := by
    intro x
    rw [hAtw, mactC_mul, mactC_mul]
  refine Nat.card_le_card_of_injective
    (fun a : {a : Fin Tag.E6.rank → C // mactC (Atw (y * h * y⁻¹)) a = a} =>
      (⟨mactC (Atw y⁻¹) a.1, ?_⟩ : {a : Fin Tag.E6.rank → C // mactC (Atw h) a = a})) ?_
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

private theorem ggKGW5_exists_conj
    (w : WeylGroup Tag.E6) (hw : orderOf w = 5) :
    ∃ y : WeylGroup Tag.E6, y⁻¹ * w * y ∈ Subgroup.zpowers ggKGW5_c := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hordc : orderOf ggKGW5_c = 5 := ggKGW5_orderOf_c
  have hcard : Nat.card (WeylGroup Tag.E6) = 51840 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.card_weylGroup_E6
  have hfac : (Nat.card (WeylGroup Tag.E6)).factorization 5 = 1 := by
    rw [hcard]
    decide +kernel
  have hcw : Nat.card (Subgroup.zpowers ggKGW5_c) =
      5 ^ (Nat.card (WeylGroup Tag.E6)).factorization 5 := by
    rw [Nat.card_zpowers, hordc, hfac]
    norm_num
  have hww : Nat.card (Subgroup.zpowers w) =
      5 ^ (Nat.card (WeylGroup Tag.E6)).factorization 5 := by
    rw [Nat.card_zpowers, hw, hfac]
    norm_num
  let Pc : Sylow 5 (WeylGroup Tag.E6) := Sylow.ofCard (Subgroup.zpowers ggKGW5_c) hcw
  let Pw : Sylow 5 (WeylGroup Tag.E6) := Sylow.ofCard (Subgroup.zpowers w) hww
  haveI : MulAction.IsPretransitive (WeylGroup Tag.E6) (Sylow 5 (WeylGroup Tag.E6)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) Pc Pw
  refine ⟨y, ?_⟩
  have hmap : (Pw : Subgroup (WeylGroup Tag.E6)) =
      (Subgroup.zpowers ggKGW5_c).map (MulAut.conj y).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Subgroup.pointwise_smul_def]
    rfl
  have hw_mem : w ∈ (Pw : Subgroup (WeylGroup Tag.E6)) := by
    simpa only [Pw, Sylow.coe_ofCard] using Subgroup.mem_zpowers w
  rw [hmap, Subgroup.mem_map] at hw_mem
  obtain ⟨h, hhc, hhconj⟩ := hw_mem
  have hwh : y⁻¹ * w * y = h := by
    have h1 : (MulAut.conj y) h = w := hhconj
    rw [← h1, MulAut.conj_apply]
    group
  rw [hwh]
  exact hhc

private theorem ggKGW5_card_c
    {C : Type} [CommGroup C] (hC : Nat.card C = 5) :
    Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw ggKGW5_c) a = a} ≤ 5 ^ 3 := by
  rw [ggKGW5_Atw_c]
  change Nat.card {a : Fin 6 → C // mactC ggKGW5_M6 a = a} ≤ 5 ^ 3
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  have hle : Nat.card {a : Fin 6 → C // mactC ggKGW5_M6 a = a} ≤ Nat.card (C × C) := by
    refine Nat.card_le_card_of_injective (fun a => (a.1 1, a.1 5)) ?_
    intro a b hab
    apply Subtype.ext
    have ha := ggKGW5_fixed_vals a.1 a.2
    have hb := ggKGW5_fixed_vals b.1 b.2
    have h1 : a.1 1 = b.1 1 := congrArg Prod.fst hab
    have h5 : a.1 5 = b.1 5 := congrArg Prod.snd hab
    funext i
    fin_cases i <;> simp_all
  calc Nat.card {a : Fin 6 → C // mactC ggKGW5_M6 a = a} ≤ Nat.card (C × C) := hle
    _ = Nat.card C * Nat.card C := Nat.card_prod C C
    _ ≤ 5 ^ 3 := by rw [hC]; norm_num

theorem weylE6_five_fixed
    {C : Type} [CommGroup C] (hC : Nat.card C = 5) {w : WeylGroup Tag.E6}
    (hw : orderOf w = 5) :
    Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw w) a = a} ≤ 5 ^ 3 := by
  haveI hfinC : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; norm_num)
  obtain ⟨y, hy⟩ := ggKGW5_exists_conj w hw
  set h : WeylGroup Tag.E6 := y⁻¹ * w * y with hh_def
  have hh_mem : h ∈ Subgroup.zpowers ggKGW5_c := by rw [hh_def]; exact hy
  have hw_eq : w = y * h * y⁻¹ := by rw [hh_def]; group
  have hh1 : h ≠ 1 := by
    intro h1
    have hone : w = 1 := by rw [hw_eq, h1, mul_one, mul_inv_cancel]
    rw [hone, orderOf_one] at hw
    norm_num at hw
  rw [hw_eq]
  calc Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw (y * h * y⁻¹)) a = a}
      ≤ Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw h) a = a} :=
        ggKGW5_card_le_conj y h
    _ = Nat.card {a : Fin Tag.E6.rank → C // mactC (Atw ggKGW5_c) a = a} :=
        Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin Tag.E6.rank → C))
          (p := fun a => mactC (Atw h) a = a)
          (q := fun a => mactC (Atw ggKGW5_c) a = a)
          fun a => ggKGW5_fix_iff_zpow hh_mem hh1 a)
    _ ≤ 5 ^ 3 := ggKGW5_card_c hC

end CFSG.StandardType

end
