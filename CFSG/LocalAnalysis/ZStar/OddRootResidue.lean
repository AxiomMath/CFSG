module

public import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import CFSG.LocalAnalysis.ZStar.PadicBlockField
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.RingTheory.PicardGroup

public section

namespace CFSG

namespace ZStar.OddRootResidue

open ZStar.PadicBlockField

noncomputable section

abbrev O2 := PadicComplexInt 2

abbrev Residue2 := IsLocalRing.ResidueField O2

private theorem residue2_valuation_two :
    Valued.v (2 : TwoAdicComplex) = 1 / (2 : NNReal) := by
  calc
    Valued.v (2 : TwoAdicComplex) =
        Valued.v ((2 : PadicAlgCl 2) : TwoAdicComplex) := by
      congr 1
      exact (PadicComplex.coe_natCast 2 2).symm
    _ = Valued.v (2 : PadicAlgCl 2) :=
      PadicComplex.valuation_extends 2 (2 : PadicAlgCl 2)
    _ = 1 / (2 : NNReal) := PadicAlgCl.valuation_p 2

private theorem residue2_coe_natCast_two :
    (((2 : ℕ) : O2) : TwoAdicComplex) = (2 : TwoAdicComplex) := by
  push_cast; rfl

private theorem residue2_not_valuation_inv_two_le_one :
    ¬ Valued.v ((2 : TwoAdicComplex)⁻¹) ≤ 1 := by
  rw [map_inv₀, residue2_valuation_two]
  norm_num

private theorem residue2_charP : CharP Residue2 2 := by
  rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
  rw [← map_natCast (IsLocalRing.residue O2)]
  apply (IsLocalRing.residue_eq_zero_iff ((2 : ℕ) : O2)).2
  apply ValuationSubring.coe_mem_nonunits_iff.mp
  rw [ValuationSubring.mem_nonunits_iff_or]
  right
  rw [residue2_coe_natCast_two]
  change (2 : TwoAdicComplex)⁻¹ ∉ PadicComplexInt 2
  unfold PadicComplexInt
  rw [Valuation.mem_valuationSubring_iff]
  exact residue2_not_valuation_inv_two_le_one

instance : CharP Residue2 2 := residue2_charP

@[expose] noncomputable def padicIntToO2 : ℤ_[2] →+* O2 where
  toFun x := ⟨padicIntToComplex x, by
    change Valued.v
      ((algebraMap ℚ_[2] TwoAdicComplex) (x : ℚ_[2])) ≤ 1
    let y : PadicAlgCl 2 :=
      (algebraMap ℚ_[2] (PadicAlgCl 2)) (x : ℚ_[2])
    have hy : (algebraMap ℚ_[2] TwoAdicComplex) (x : ℚ_[2]) =
        (y : TwoAdicComplex) := by
      exact IsScalarTower.algebraMap_apply ℚ_[2] (PadicAlgCl 2)
        TwoAdicComplex (x : ℚ_[2])
    rw [hy, PadicComplex.valuation_extends 2 y,
      PadicAlgCl.valuation_def]
    change ‖(algebraMap ℚ_[2] (PadicAlgCl 2)) (x : ℚ_[2])‖₊ ≤ 1
    rw [show ‖(algebraMap ℚ_[2] (PadicAlgCl 2)) (x : ℚ_[2])‖₊ =
        ‖(x : ℚ_[2])‖₊ by
      apply NNReal.eq
      exact PadicAlgCl.norm_extends 2 (x : ℚ_[2])]
    exact_mod_cast PadicInt.norm_le_one x⟩
  map_one' := by
    apply Subtype.ext
    exact map_one padicIntToComplex
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul padicIntToComplex x y
  map_zero' := by
    apply Subtype.ext
    exact map_zero padicIntToComplex
  map_add' x y := by
    apply Subtype.ext
    exact map_add padicIntToComplex x y

@[simp]
theorem padicIntToO2_coe (x : ℤ_[2]) :
    ((padicIntToO2 x : O2) : TwoAdicComplex) = padicIntToComplex x :=
  rfl

theorem algebraMap_comp_padicIntToO2 :
    (algebraMap O2 TwoAdicComplex).comp padicIntToO2 =
      padicIntToComplex := by
  ext x
  rfl

theorem norm_padicIntToO2 (x : ℤ_[2]) :
    ‖((padicIntToO2 x : O2) : TwoAdicComplex)‖ = ‖x‖ := by
  change ‖((algebraMap ℚ_[2] (PadicAlgCl 2)) (x : ℚ_[2]) :
    TwoAdicComplex)‖ = ‖x‖
  rw [PadicComplex.norm_extends']
  rfl

private theorem valuation_padicIntToO2 (x : ℤ_[2]) :
    Valued.v (((padicIntToO2 x : O2) : TwoAdicComplex)) = ‖x‖₊ := by
  change Valued.v
    ((algebraMap ℚ_[2] TwoAdicComplex) (x : ℚ_[2])) = ‖x‖₊
  let y : PadicAlgCl 2 :=
    (algebraMap ℚ_[2] (PadicAlgCl 2)) (x : ℚ_[2])
  have hy : (algebraMap ℚ_[2] TwoAdicComplex) (x : ℚ_[2]) =
      (y : TwoAdicComplex) := by
    exact IsScalarTower.algebraMap_apply ℚ_[2] (PadicAlgCl 2)
      TwoAdicComplex (x : ℚ_[2])
  rw [hy, PadicComplex.valuation_extends 2 y,
    PadicAlgCl.valuation_def]
  change ‖(algebraMap ℚ_[2] (PadicAlgCl 2)) (x : ℚ_[2])‖₊ = ‖x‖₊
  apply NNReal.eq
  exact PadicAlgCl.norm_extends 2 (x : ℚ_[2])

private theorem padicIntToO2_mem_maximalIdeal {x : ℤ_[2]}
    (hx : x ∈ IsLocalRing.maximalIdeal ℤ_[2]) :
    padicIntToO2 x ∈ IsLocalRing.maximalIdeal O2 := by
  rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
  have hxnorm : ‖x‖ < 1 := PadicInt.mem_nonunits.mp hx
  change ¬ IsUnit (padicIntToO2 x)
  apply (Valuation.Integer.not_isUnit_iff_valuation_lt_one).2
  change Valued.v (((padicIntToO2 x : O2) : TwoAdicComplex)) < 1
  rw [valuation_padicIntToO2]
  exact_mod_cast hxnorm

@[expose] noncomputable def zmod2ToResidue : ZMod 2 →+* Residue2 :=
  ZMod.castHom (dvd_refl 2) Residue2

theorem residue_padicIntToO2 (x : ℤ_[2]) :
    IsLocalRing.residue O2 (padicIntToO2 x) =
      zmod2ToResidue (PadicInt.toZMod x) := by
  have hspec := PadicInt.toZMod_spec x
  have hmax := padicIntToO2_mem_maximalIdeal hspec
  have hzero :
      IsLocalRing.residue O2
          (padicIntToO2 (x - (PadicInt.toZMod x).cast)) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 hmax
  rw [map_sub, map_sub] at hzero
  apply sub_eq_zero.mp hzero |>.trans
  unfold zmod2ToResidue
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val]
  simp

theorem residue_comp_padicIntToO2 :
    (IsLocalRing.residue O2).comp padicIntToO2 =
      zmod2ToResidue.comp PadicInt.toZMod := by
  ext x
  exact residue_padicIntToO2 x

theorem toZModPow_one_eq_toZMod :
    (PadicInt.toZModPow 1 : ℤ_[2] →+* ZMod 2) = PadicInt.toZMod := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZModPow, pow_one, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]

@[expose] def rootOfUnityToO2 {m : ℕ} (z : TwoAdicComplex)
    (hm : m ≠ 0) (hz : z ^ m = 1) : O2 :=
  ⟨z, by
    have hvpow : Valued.v z ^ m = 1 := by
      rw [← map_pow, hz, map_one]
    have hv : Valued.v z = 1 :=
      (pow_eq_one_iff_of_nonneg bot_le hm).mp hvpow
    exact hv.le⟩

@[simp]
theorem rootOfUnityToO2_coe {m : ℕ} (z : TwoAdicComplex)
    (hm : m ≠ 0) (hz : z ^ m = 1) :
    ((rootOfUnityToO2 z hm hz : O2) : TwoAdicComplex) = z :=
  rfl

theorem exists_primitiveRoot_o2 (m : ℕ) [NeZero m] :
    ∃ z : O2, IsPrimitiveRoot z m := by
  obtain ⟨z, hz⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot TwoAdicComplex m
  let zO : O2 := rootOfUnityToO2 z (NeZero.ne m) hz.pow_eq_one
  refine ⟨zO, ?_⟩
  apply hz.of_map_of_injective (f := algebraMap O2 TwoAdicComplex)
  exact FaithfulSMul.algebraMap_injective O2 TwoAdicComplex

theorem odd_natCast_residue2 {m : ℕ} (hm : Odd m) :
    (m : Residue2) = 1 := by
  obtain ⟨r, rfl⟩ := hm
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have htwo : (2 : Residue2) = 0 :=
    CharP.cast_eq_zero Residue2 2
  rw [htwo, zero_mul, zero_add, Nat.cast_one]

private theorem residue_ne_one_of_odd_order {m : ℕ} (hm : Odd m)
    {z : O2} (hzpow : z ^ m = 1) (hzne : z ≠ 1) :
    IsLocalRing.residue O2 z ≠ 1 := by
  intro hzres
  have hgeom : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have hprod := mul_geom_sum z m
    rw [hzpow, sub_self] at hprod
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hzne)
  have hgeom_res := congrArg (IsLocalRing.residue O2) hgeom
  have hmzero : (m : Residue2) = 0 := by
    simpa only [map_sum, map_pow, map_zero, hzres, one_pow,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using hgeom_res
  exact one_ne_zero ((odd_natCast_residue2 hm).symm.trans hmzero)

theorem residue_pow_ne_one_of_primitive_odd {m : ℕ} (hm : Odd m)
    {z : O2} (hz : IsPrimitiveRoot z m) (a : Fin m)
    (ha : (a : ℕ) ≠ 0) :
    IsLocalRing.residue O2 (z ^ (a : ℕ)) ≠ 1 := by
  apply residue_ne_one_of_odd_order hm
  · calc
      (z ^ (a : ℕ)) ^ m = (z ^ m) ^ (a : ℕ) := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      _ = 1 := by rw [hz.pow_eq_one, one_pow]
  · intro hpow
    have hdiv : m ∣ (a : ℕ) := (hz.pow_eq_one_iff_dvd (a : ℕ)).mp hpow
    have hazero : (a : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdiv a.isLt
    exact ha hazero

end

end ZStar.OddRootResidue

end CFSG
