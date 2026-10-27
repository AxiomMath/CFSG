module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.GroupTheory.PGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix III, Lemma 1
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixIII

open scoped commutatorElement

universe u v w

/-- Appendix III, Lemma 1(a). The polar map is written multiplicatively on
the elementary abelian groups P/W and W. -/
public theorem lemma1a_square_induces_quadratic
    {P : Type u} [Group P] [Finite P]
    (_hP_two : IsPGroup 2 P)
    (W : Subgroup P)
    (hW_center : W ≤ Subgroup.center P) :
    letI : W.Normal := ⟨fun w hw g => by
      simpa [mul_assoc, Subgroup.mem_center_iff.mp (hW_center hw) g] using hw⟩
    ∀ (hW_elementary :
        (∀ x : W, x ^ 2 = 1) ∧ ∀ x y : W, x * y = y * x)
      (hV_elementary :
        (∀ x : P ⧸ W, x ^ 2 = 1) ∧
          ∀ x y : P ⧸ W, x * y = y * x),
      ∃ q : (P ⧸ W) → W,
      q 1 = 1 ∧
      (∀ x : P, ((q (QuotientGroup.mk' W x) : W) : P) = x ^ 2) ∧
      (∀ x₁ x₂ y : P ⧸ W,
        q ((x₁ * x₂) * y) * (q (x₁ * x₂))⁻¹ * (q y)⁻¹ =
          (q (x₁ * y) * (q x₁)⁻¹ * (q y)⁻¹) *
            (q (x₂ * y) * (q x₂)⁻¹ * (q y)⁻¹)) ∧
      ∀ x y₁ y₂ : P ⧸ W,
        q (x * (y₁ * y₂)) * (q x)⁻¹ * (q (y₁ * y₂))⁻¹ =
          (q (x * y₁) * (q x)⁻¹ * (q y₁)⁻¹) *
            (q (x * y₂) * (q x)⁻¹ * (q y₂)⁻¹) := by
  letI : W.Normal := ⟨fun w hw g => by
    simpa [mul_assoc, Subgroup.mem_center_iff.mp (hW_center hw) g] using hw⟩
  dsimp
  intro hW_elementary hV_elementary
  let repr : P ⧸ W → P := fun x =>
    Classical.choose (QuotientGroup.mk'_surjective W x)
  have hrepr (x : P ⧸ W) : QuotientGroup.mk' W (repr x) = x :=
    Classical.choose_spec (QuotientGroup.mk'_surjective W x)
  have hsquare_mem (x : P) : x ^ 2 ∈ W := by
    apply (QuotientGroup.eq_one_iff (N := W) (x ^ 2)).mp
    simpa using hV_elementary.1 (QuotientGroup.mk' W x)
  let q : P ⧸ W → W := fun x => ⟨repr x ^ 2, hsquare_mem (repr x)⟩
  have hq_mk (x : P) :
      ((q (QuotientGroup.mk' W x) : W) : P) = x ^ 2 := by
    change repr (QuotientGroup.mk' W x) ^ 2 = x ^ 2
    obtain ⟨z, hzW, hz⟩ :=
      (QuotientGroup.mk'_eq_mk' (N := W)).mp (hrepr (QuotientGroup.mk' W x))
    have hz_sq : z ^ 2 = 1 := by
      simpa using congrArg W.subtype (hW_elementary.1 ⟨z, hzW⟩)
    have hrz : Commute (repr (QuotientGroup.mk' W x)) z :=
      Subgroup.mem_center_iff.mp (hW_center hzW) _
    calc
      repr (QuotientGroup.mk' W x) ^ 2 =
          repr (QuotientGroup.mk' W x) ^ 2 * z ^ 2 := by rw [hz_sq, mul_one]
      _ = (repr (QuotientGroup.mk' W x) * z) ^ 2 := (hrz.mul_pow 2).symm
      _ = x ^ 2 := by rw [hz]
  have hcomm_mem (x y : P) : ⁅x, y⁆ ∈ W := by
    apply (QuotientGroup.eq_one_iff (N := W) ⁅x, y⁆).mp
    change QuotientGroup.mk' W ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (hV_elementary.2 (QuotientGroup.mk' W x) (QuotientGroup.mk' W y))
  have hcomm_mul_left (x₁ x₂ y : P) :
      ⁅x₁ * x₂, y⁆ = ⁅x₁, y⁆ * ⁅x₂, y⁆ := by
    have hformula :
        ⁅x₁ * x₂, y⁆ = x₁ * ⁅x₂, y⁆ * x₁⁻¹ * ⁅x₁, y⁆ := by
      simp only [commutatorElement_def, mul_inv_rev]
      group
    rw [hformula]
    have hx₁c : Commute x₁ ⁅x₂, y⁆ :=
      Subgroup.mem_center_iff.mp (hW_center (hcomm_mem x₂ y)) x₁
    rw [hx₁c.eq]
    simp only [mul_assoc, mul_inv_cancel_left]
    exact Subgroup.mem_center_iff.mp
      (hW_center (hcomm_mem x₁ y)) ⁅x₂, y⁆
  have hcomm_mul_right (x y₁ y₂ : P) :
      ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by
    have hformula :
        ⁅x, y₁ * y₂⁆ = ⁅x, y₁⁆ * y₁ * ⁅x, y₂⁆ * y₁⁻¹ := by
      simp only [commutatorElement_def, mul_inv_rev]
      group
    rw [hformula]
    have hy₁c : Commute y₁ ⁅x, y₂⁆ :=
      Subgroup.mem_center_iff.mp (hW_center (hcomm_mem x y₂)) y₁
    calc
      ⁅x, y₁⁆ * y₁ * ⁅x, y₂⁆ * y₁⁻¹ =
          ⁅x, y₁⁆ * (y₁ * ⁅x, y₂⁆) * y₁⁻¹ := by group
      _ = ⁅x, y₁⁆ * (⁅x, y₂⁆ * y₁) * y₁⁻¹ := by rw [hy₁c.eq]
      _ = ⁅x, y₁⁆ * ⁅x, y₂⁆ := by group
  have hmul_sq (x y : P) :
      (x * y) ^ 2 = ⁅x, y⁆ * x ^ 2 * y ^ 2 := by
    have hxy : x * y = ⁅x, y⁆ * y * x := by
      simp [commutatorElement_def, mul_assoc]
    have hx2y : Commute (x ^ 2) y :=
      (Subgroup.mem_center_iff.mp (hW_center (hsquare_mem x)) y).symm
    calc
      (x * y) ^ 2 = (x * y) * x * y := by rw [pow_two]; group
      _ = (⁅x, y⁆ * y * x) * x * y := by rw [hxy]
      _ = ⁅x, y⁆ * y * (x ^ 2) * y := by rw [pow_two]; group
      _ = ⁅x, y⁆ * (y * x ^ 2) * y := by group
      _ = ⁅x, y⁆ * (x ^ 2 * y) * y := by rw [hx2y.eq.symm]
      _ = ⁅x, y⁆ * x ^ 2 * y ^ 2 := by simp only [pow_two, mul_assoc]
  have hpolar_eq_comm (x y : P) :
      (x * y) ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ = ⁅x, y⁆ := by
    rw [hmul_sq]
    have hxy2 : Commute (x ^ 2) (y ^ 2) :=
      (Subgroup.mem_center_iff.mp (hW_center (hsquare_mem x)) (y ^ 2)).symm
    calc
      ⁅x, y⁆ * x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ =
          ⁅x, y⁆ * x ^ 2 * (y ^ 2 * (x ^ 2)⁻¹) * (y ^ 2)⁻¹ := by group
      _ = ⁅x, y⁆ * x ^ 2 * ((x ^ 2)⁻¹ * y ^ 2) * (y ^ 2)⁻¹ := by
        rw [hxy2.inv_left.eq.symm]
      _ = ⁅x, y⁆ := by group
  have hpolar_left_P (x₁ x₂ y : P) :
      ((x₁ * x₂) * y) ^ 2 * ((x₁ * x₂) ^ 2)⁻¹ * (y ^ 2)⁻¹ =
        (x₁ * y) ^ 2 * (x₁ ^ 2)⁻¹ * (y ^ 2)⁻¹ *
          ((x₂ * y) ^ 2 * (x₂ ^ 2)⁻¹ * (y ^ 2)⁻¹) := by
    rw [hpolar_eq_comm, hpolar_eq_comm, hpolar_eq_comm]
    exact hcomm_mul_left x₁ x₂ y
  have hpolar_right_P (x y₁ y₂ : P) :
      (x * (y₁ * y₂)) ^ 2 * (x ^ 2)⁻¹ * ((y₁ * y₂) ^ 2)⁻¹ =
        (x * y₁) ^ 2 * (x ^ 2)⁻¹ * (y₁ ^ 2)⁻¹ *
          ((x * y₂) ^ 2 * (x ^ 2)⁻¹ * (y₂ ^ 2)⁻¹) := by
    rw [hpolar_eq_comm, hpolar_eq_comm, hpolar_eq_comm]
    exact hcomm_mul_right x y₁ y₂
  refine ⟨q, ?_, hq_mk, ?_, ?_⟩
  · apply Subtype.ext
    simpa using hq_mk 1
  · intro x₁ x₂ y
    refine QuotientGroup.induction_on x₁ ?_
    intro a
    refine QuotientGroup.induction_on x₂ ?_
    intro b
    refine QuotientGroup.induction_on y ?_
    intro c
    change q (QuotientGroup.mk' W ((a * b) * c)) *
        (q (QuotientGroup.mk' W (a * b)))⁻¹ *
          (q (QuotientGroup.mk' W c))⁻¹ =
      (q (QuotientGroup.mk' W (a * c)) *
          (q (QuotientGroup.mk' W a))⁻¹ *
            (q (QuotientGroup.mk' W c))⁻¹) *
        (q (QuotientGroup.mk' W (b * c)) *
          (q (QuotientGroup.mk' W b))⁻¹ *
            (q (QuotientGroup.mk' W c))⁻¹)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hq_mk] using hpolar_left_P a b c
  · intro x y₁ y₂
    refine QuotientGroup.induction_on x ?_
    intro a
    refine QuotientGroup.induction_on y₁ ?_
    intro b
    refine QuotientGroup.induction_on y₂ ?_
    intro c
    change q (QuotientGroup.mk' W (a * (b * c))) *
        (q (QuotientGroup.mk' W a))⁻¹ *
          (q (QuotientGroup.mk' W (b * c)))⁻¹ =
      (q (QuotientGroup.mk' W (a * b)) *
          (q (QuotientGroup.mk' W a))⁻¹ *
            (q (QuotientGroup.mk' W b))⁻¹) *
        (q (QuotientGroup.mk' W (a * c)) *
          (q (QuotientGroup.mk' W a))⁻¹ *
            (q (QuotientGroup.mk' W c))⁻¹)
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hq_mk] using hpolar_right_P a b c

/-- Appendix III, Lemma 1(c). Two central extensions are isomorphic over the
specified maps exactly when their quadratic maps commute with those maps. -/
public theorem lemma1c_central_extensions_equivalent_iff
    {V : Type v} {W : Type w} {V' : Type v} {W' : Type w}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [AddCommGroup V'] [Module (ZMod 2) V'] [FiniteDimensional (ZMod 2) V']
    [AddCommGroup W'] [Module (ZMod 2) W'] [FiniteDimensional (ZMod 2) W']
    {P : Type u} [Group P] {P' : Type u} [Group P']
    (iota : Multiplicative W →* P) (pi : P →* Multiplicative V)
    (iota' : Multiplicative W' →* P') (pi' : P' →* Multiplicative V')
    (q : QuadraticMap (ZMod 2) V W)
    (q' : QuadraticMap (ZMod 2) V' W')
    (hiota : Function.Injective iota) (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker) (hcentral : iota.range ≤ Subgroup.center P)
    (hiota' : Function.Injective iota') (hpi' : Function.Surjective pi')
    (hexact' : iota'.range = pi'.ker)
    (hcentral' : iota'.range ≤ Subgroup.center P')
    (hsquare : ∀ x : P,
      iota (Multiplicative.ofAdd (q (pi x).toAdd)) = x ^ 2)
    (hsquare' : ∀ x : P',
      iota' (Multiplicative.ofAdd (q' (pi' x).toAdd)) = x ^ 2)
    (f : V ≃ₗ[ZMod 2] V') (g : W ≃ₗ[ZMod 2] W') :
    (∃ e : P ≃* P',
      (∀ x : P, (pi' (e x)).toAdd = f (pi x).toAdd) ∧
      ∀ z : Multiplicative W,
        e (iota z) = iota' (Multiplicative.ofAdd (g z.toAdd))) ↔
      ∀ x : V, g (q x) = q' (f x) := by
  constructor
  · rintro ⟨e, he_pi, he_iota⟩ x
    obtain ⟨a, ha⟩ := hpi (Multiplicative.ofAdd x)
    have ha_toAdd : (pi a).toAdd = x :=
      congrArg Multiplicative.toAdd ha
    change Multiplicative.ofAdd (g (q x)) =
      Multiplicative.ofAdd (q' (f x))
    apply hiota'
    calc
      iota' (Multiplicative.ofAdd (g (q x))) =
          e (iota (Multiplicative.ofAdd (q x))) := (he_iota _).symm
      _ = e (iota (Multiplicative.ofAdd (q (pi a).toAdd))) := by rw [ha_toAdd]
      _ = e (a ^ 2) := by rw [hsquare a]
      _ = e a ^ 2 := map_pow e a 2
      _ = iota' (Multiplicative.ofAdd (q' (pi' (e a)).toAdd)) :=
        (hsquare' (e a)).symm
      _ = iota' (Multiplicative.ofAdd (q' (f x))) := by
        rw [he_pi a, ha_toAdd]
  · intro hq
    let basis := Module.finBasis (ZMod 2) V
    let xLift : Fin (Module.finrank (ZMod 2) V) → P := fun i =>
      Classical.choose (hpi (Multiplicative.ofAdd (basis i)))
    let yLift : Fin (Module.finrank (ZMod 2) V) → P' := fun i =>
      Classical.choose (hpi' (Multiplicative.ofAdd (f (basis i))))
    have hxLift_pi (i : Fin (Module.finrank (ZMod 2) V)) :
        pi (xLift i) = Multiplicative.ofAdd (basis i) := by
      exact Classical.choose_spec (hpi (Multiplicative.ofAdd (basis i)))
    have hyLift_pi (i : Fin (Module.finrank (ZMod 2) V)) :
        pi' (yLift i) = Multiplicative.ofAdd (f (basis i)) := by
      exact Classical.choose_spec (hpi' (Multiplicative.ofAdd (f (basis i))))
    let basisWord (v : V) : P :=
      (List.ofFn fun i : Fin (Module.finrank (ZMod 2) V) =>
        xLift i ^ (basis.repr v i).val).prod
    let basisWord' (v : V) : P' :=
      (List.ofFn fun i : Fin (Module.finrank (ZMod 2) V) =>
        yLift i ^ (basis.repr v i).val).prod
    have hbasisWord_pi (v : V) : (pi (basisWord v)).toAdd = v := by
      simp only [basisWord, map_list_prod, List.map_ofFn, Function.comp_apply,
        map_pow, hxLift_pi, toAdd_list_sum, toAdd_pow, List.sum_ofFn]
      simpa only [toAdd_ofAdd,
        ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val] using
        basis.sum_repr v
    have hbasisWord'_pi (v : V) : (pi' (basisWord' v)).toAdd = f v := by
      simp only [basisWord', map_list_prod, List.map_ofFn, Function.comp_apply,
        map_pow, hyLift_pi, toAdd_list_sum, toAdd_pow, List.sum_ofFn]
      simpa only [toAdd_ofAdd, map_sum, map_smul,
        ← Nat.cast_smul_eq_nsmul (ZMod 2),
        ZMod.natCast_zmod_val] using congrArg f (basis.sum_repr v)
    let residue (x : P) : P := (basisWord (pi x).toAdd)⁻¹ * x
    let residue' (x : P') : P' :=
      (basisWord' (f.symm (pi' x).toAdd))⁻¹ * x
    have hresidue_mem (x : P) : residue x ∈ iota.range := by
      rw [hexact, MonoidHom.mem_ker]
      change (pi (residue x)).toAdd = 0
      simp [residue, hbasisWord_pi]
    have hresidue'_mem (x : P') : residue' x ∈ iota'.range := by
      rw [hexact', MonoidHom.mem_ker]
      change (pi' (residue' x)).toAdd = 0
      simp [residue', hbasisWord'_pi]
    let kernelCoord (x : P) : Multiplicative W :=
      Classical.choose (hresidue_mem x)
    let kernelCoord' (x : P') : Multiplicative W' :=
      Classical.choose (hresidue'_mem x)
    have hkernelCoord (x : P) : iota (kernelCoord x) = residue x := by
      exact Classical.choose_spec (hresidue_mem x)
    have hkernelCoord' (x : P') : iota' (kernelCoord' x) = residue' x := by
      exact Classical.choose_spec (hresidue'_mem x)
    have hnormalForm (x : P) :
        basisWord (pi x).toAdd * iota (kernelCoord x) = x := by
      rw [hkernelCoord]
      dsimp only [residue]
      group
    have hnormalForm' (x : P') :
        basisWord' (f.symm (pi' x).toAdd) * iota' (kernelCoord' x) = x := by
      rw [hkernelCoord']
      dsimp only [residue']
      group
    have hsquare_lifts (i : Fin (Module.finrank (ZMod 2) V)) :
        xLift i ^ 2 = iota (Multiplicative.ofAdd (q (basis i))) ∧
        yLift i ^ 2 =
          iota' (Multiplicative.ofAdd (g (q (basis i)))) := by
      constructor
      · simpa only [hxLift_pi, toAdd_ofAdd] using
          (hsquare (xLift i)).symm
      · calc
          yLift i ^ 2 =
              iota' (Multiplicative.ofAdd (q' (pi' (yLift i)).toAdd)) :=
            (hsquare' (yLift i)).symm
          _ = iota' (Multiplicative.ofAdd (q' (f (basis i)))) := by
            simp [hyLift_pi]
          _ = iota' (Multiplicative.ofAdd (g (q (basis i)))) :=
            congrArg (fun w => iota' (Multiplicative.ofAdd w)) (hq (basis i)).symm
    have hcommutator_eq_polar (x y : P) :
        ⁅x, y⁆ = iota (Multiplicative.ofAdd
          (QuadraticMap.polar q (pi x).toAdd (pi y).toAdd)) := by
      have hsquare_mem (a : P) : a ^ 2 ∈ iota.range :=
        ⟨Multiplicative.ofAdd (q (pi a).toAdd), hsquare a⟩
      have hmul_sq (a b : P) :
          (a * b) ^ 2 = ⁅a, b⁆ * a ^ 2 * b ^ 2 := by
        have hab : a * b = ⁅a, b⁆ * b * a := by
          simp [commutatorElement_def, mul_assoc]
        have ha2b : Commute (a ^ 2) b :=
          (Subgroup.mem_center_iff.mp (hcentral (hsquare_mem a)) b).symm
        calc
          (a * b) ^ 2 = (a * b) * a * b := by rw [pow_two]; group
          _ = (⁅a, b⁆ * b * a) * a * b := by rw [hab]
          _ = ⁅a, b⁆ * b * (a ^ 2) * b := by rw [pow_two]; group
          _ = ⁅a, b⁆ * (b * a ^ 2) * b := by group
          _ = ⁅a, b⁆ * (a ^ 2 * b) * b := by rw [ha2b.eq.symm]
          _ = ⁅a, b⁆ * a ^ 2 * b ^ 2 := by
            simp only [pow_two, mul_assoc]
      have hpolar_eq_comm (a b : P) :
          (a * b) ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ = ⁅a, b⁆ := by
        rw [hmul_sq]
        have hab2 : Commute (a ^ 2) (b ^ 2) :=
          (Subgroup.mem_center_iff.mp (hcentral (hsquare_mem a)) (b ^ 2)).symm
        calc
          ⁅a, b⁆ * a ^ 2 * b ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ =
              ⁅a, b⁆ * a ^ 2 * (b ^ 2 * (a ^ 2)⁻¹) * (b ^ 2)⁻¹ := by
            group
          _ = ⁅a, b⁆ * a ^ 2 * ((a ^ 2)⁻¹ * b ^ 2) * (b ^ 2)⁻¹ := by
            rw [hab2.inv_left.eq.symm]
          _ = ⁅a, b⁆ := by group
      rw [← hpolar_eq_comm x y, ← hsquare (x * y), ← hsquare x, ← hsquare y]
      simp only [← map_inv, ← map_mul]
      congr 1
      simp [QuadraticMap.polar, div_eq_mul_inv]
    have hcommutator_eq_polar' (x y : P') :
        ⁅x, y⁆ = iota' (Multiplicative.ofAdd
          (QuadraticMap.polar q' (pi' x).toAdd (pi' y).toAdd)) := by
      have hsquare_mem (a : P') : a ^ 2 ∈ iota'.range :=
        ⟨Multiplicative.ofAdd (q' (pi' a).toAdd), hsquare' a⟩
      have hmul_sq (a b : P') :
          (a * b) ^ 2 = ⁅a, b⁆ * a ^ 2 * b ^ 2 := by
        have hab : a * b = ⁅a, b⁆ * b * a := by
          simp [commutatorElement_def, mul_assoc]
        have ha2b : Commute (a ^ 2) b :=
          (Subgroup.mem_center_iff.mp (hcentral' (hsquare_mem a)) b).symm
        calc
          (a * b) ^ 2 = (a * b) * a * b := by rw [pow_two]; group
          _ = (⁅a, b⁆ * b * a) * a * b := by rw [hab]
          _ = ⁅a, b⁆ * b * (a ^ 2) * b := by rw [pow_two]; group
          _ = ⁅a, b⁆ * (b * a ^ 2) * b := by group
          _ = ⁅a, b⁆ * (a ^ 2 * b) * b := by rw [ha2b.eq.symm]
          _ = ⁅a, b⁆ * a ^ 2 * b ^ 2 := by
            simp only [pow_two, mul_assoc]
      have hpolar_eq_comm (a b : P') :
          (a * b) ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ = ⁅a, b⁆ := by
        rw [hmul_sq]
        have hab2 : Commute (a ^ 2) (b ^ 2) :=
          (Subgroup.mem_center_iff.mp (hcentral' (hsquare_mem a)) (b ^ 2)).symm
        calc
          ⁅a, b⁆ * a ^ 2 * b ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ =
              ⁅a, b⁆ * a ^ 2 * (b ^ 2 * (a ^ 2)⁻¹) * (b ^ 2)⁻¹ := by
            group
          _ = ⁅a, b⁆ * a ^ 2 * ((a ^ 2)⁻¹ * b ^ 2) * (b ^ 2)⁻¹ := by
            rw [hab2.inv_left.eq.symm]
          _ = ⁅a, b⁆ := by group
      rw [← hpolar_eq_comm x y, ← hsquare' (x * y), ← hsquare' x, ← hsquare' y]
      simp only [← map_inv, ← map_mul]
      congr 1
      simp [QuadraticMap.polar, div_eq_mul_inv]
    have hpolar_compatible (v₁ v₂ : V) :
        g (QuadraticMap.polar q v₁ v₂) =
          QuadraticMap.polar q' (f v₁) (f v₂) := by
      simp [QuadraticMap.polar, hq]
    have hcommutator_lifts (i j : Fin (Module.finrank (ZMod 2) V)) :
        ⁅xLift i, xLift j⁆ =
            iota (Multiplicative.ofAdd (QuadraticMap.polar q (basis i) (basis j))) ∧
        ⁅yLift i, yLift j⁆ =
            iota' (Multiplicative.ofAdd
              (g (QuadraticMap.polar q (basis i) (basis j)))) := by
      constructor
      · simpa [hxLift_pi] using hcommutator_eq_polar (xLift i) (xLift j)
      · calc
          ⁅yLift i, yLift j⁆ = iota' (Multiplicative.ofAdd
              (QuadraticMap.polar q' (pi' (yLift i)).toAdd
                (pi' (yLift j)).toAdd)) := hcommutator_eq_polar' (yLift i) (yLift j)
          _ = iota' (Multiplicative.ofAdd
              (QuadraticMap.polar q' (f (basis i)) (f (basis j)))) := by
            simp [hyLift_pi]
          _ = iota' (Multiplicative.ofAdd
              (g (QuadraticMap.polar q (basis i) (basis j)))) :=
            congrArg (fun w => iota' (Multiplicative.ofAdd w))
              (hpolar_compatible (basis i) (basis j)).symm
    have hpow_mul_compatible
        (i : Fin (Module.finrank (ZMod 2) V)) (a b : ZMod 2) :
        ∃ z : Multiplicative W,
          xLift i ^ a.val * xLift i ^ b.val =
              xLift i ^ (a + b).val * iota z ∧
          yLift i ^ a.val * yLift i ^ b.val =
              yLift i ^ (a + b).val *
                iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      have hcases (c : ZMod 2) : c = 0 ∨ c = 1 := by
        by_cases hc : c.val = 0
        · left
          apply ZMod.val_injective 2
          simpa using hc
        · right
          apply ZMod.val_injective 2
          rw [ZMod.val_one 2]
          have hc_lt : c.val < 2 := ZMod.val_lt c
          omega
      have h11 : (1 : ZMod 2) + 1 = 0 := by
        change (2 : ZMod 2) = 0
        exact ZMod.natCast_self 2
      rcases hcases a with rfl | rfl <;> rcases hcases b with rfl | rfl
      · exact ⟨1, by simp, by simp⟩
      · exact ⟨1, by simp [ZMod.val_one 2], by simp [ZMod.val_one 2]⟩
      · exact ⟨1, by simp [ZMod.val_one 2], by simp [ZMod.val_one 2]⟩
      · refine ⟨Multiplicative.ofAdd (q (basis i)), ?_, ?_⟩
        · simpa [h11, ZMod.val_one 2, pow_two] using (hsquare_lifts i).1
        · simpa [h11, ZMod.val_one 2, pow_two] using (hsquare_lifts i).2
    let word (l : List (Fin (Module.finrank (ZMod 2) V))) (v : V) : P :=
      (l.map fun i => xLift i ^ (basis.repr v i).val).prod
    let word' (l : List (Fin (Module.finrank (ZMod 2) V))) (v : V) : P' :=
      (l.map fun i => yLift i ^ (basis.repr v i).val).prod
    have hword_pi_compatible
        (l : List (Fin (Module.finrank (ZMod 2) V))) (v : V) :
        (pi' (word' l v)).toAdd = f (pi (word l v)).toAdd := by
      induction l with
      | nil => simp [word, word']
      | cons i l ih =>
          change (pi' (yLift i ^ (basis.repr v i).val * word' l v)).toAdd =
            f (pi (xLift i ^ (basis.repr v i).val * word l v)).toAdd
          simp [ih, hxLift_pi, hyLift_pi]
    have hcommutator_compatible
        (x : P) (x' : P') (y : P) (y' : P')
        (hx : (pi' x').toAdd = f (pi x).toAdd)
        (hy : (pi' y').toAdd = f (pi y).toAdd) :
        ∃ z : Multiplicative W,
          ⁅x, y⁆ = iota z ∧
          ⁅x', y'⁆ = iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      let z := Multiplicative.ofAdd
        (QuadraticMap.polar q (pi x).toAdd (pi y).toAdd)
      refine ⟨z, ?_, ?_⟩
      · simpa [z] using hcommutator_eq_polar x y
      · calc
          ⁅x', y'⁆ = iota' (Multiplicative.ofAdd
              (QuadraticMap.polar q' (pi' x').toAdd (pi' y').toAdd)) :=
            hcommutator_eq_polar' x' y'
          _ = iota' (Multiplicative.ofAdd
              (QuadraticMap.polar q' (f (pi x).toAdd) (f (pi y).toAdd))) := by
            rw [hx, hy]
          _ = iota' (Multiplicative.ofAdd
              (g (QuadraticMap.polar q (pi x).toAdd (pi y).toAdd))) :=
            congrArg (fun w => iota' (Multiplicative.ofAdd w))
              (hpolar_compatible (pi x).toAdd (pi y).toAdd).symm
          _ = iota' (Multiplicative.ofAdd (g z.toAdd)) := by rfl
    have hmove_compatible
        (x : P) (x' : P') (y : P) (y' : P')
        (hx : (pi' x').toAdd = f (pi x).toAdd)
        (hy : (pi' y').toAdd = f (pi y).toAdd) :
        ∃ z : Multiplicative W,
          x * y = y * x * iota z ∧
          x' * y' = y' * x' *
            iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      obtain ⟨z, hz, hz'⟩ := hcommutator_compatible x x' y y' hx hy
      refine ⟨z, ?_, ?_⟩
      · have hzc : Commute (iota z) (y * x) :=
          (Subgroup.mem_center_iff.mp (hcentral ⟨z, rfl⟩) (y * x)).symm
        calc
          x * y = ⁅x, y⁆ * y * x := by
            simp [commutatorElement_def, mul_assoc]
          _ = iota z * (y * x) := by rw [hz]; group
          _ = (y * x) * iota z := hzc.eq
      · have hzc : Commute (iota' (Multiplicative.ofAdd (g z.toAdd))) (y' * x') :=
          (Subgroup.mem_center_iff.mp
            (hcentral' ⟨Multiplicative.ofAdd (g z.toAdd), rfl⟩) (y' * x')).symm
        calc
          x' * y' = ⁅x', y'⁆ * y' * x' := by
            simp [commutatorElement_def, mul_assoc]
          _ = iota' (Multiplicative.ofAdd (g z.toAdd)) * (y' * x') := by
            rw [hz']
            group
          _ = (y' * x') * iota' (Multiplicative.ofAdd (g z.toAdd)) := hzc.eq
    have hlift_pow_pi_compatible
        (i : Fin (Module.finrank (ZMod 2) V)) (a : ZMod 2) :
        (pi' (yLift i ^ a.val)).toAdd =
          f (pi (xLift i ^ a.val)).toAdd := by
      simp [hxLift_pi, hyLift_pi]
    have hg_mul (z₁ z₂ : Multiplicative W) :
        Multiplicative.ofAdd (g (z₁ * z₂).toAdd) =
          Multiplicative.ofAdd (g z₁.toAdd) *
            Multiplicative.ofAdd (g z₂.toAdd) := by
      rw [← ofAdd_add]
      exact congrArg Multiplicative.ofAdd (g.map_add z₁.toAdd z₂.toAdd)
    have hword_mul_compatible
        (l : List (Fin (Module.finrank (ZMod 2) V))) (v₁ v₂ : V) :
        ∃ z : Multiplicative W,
          word l v₁ * word l v₂ = word l (v₁ + v₂) * iota z ∧
          word' l v₁ * word' l v₂ = word' l (v₁ + v₂) *
            iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      induction l with
      | nil => exact ⟨1, by simp [word], by simp [word']⟩
      | cons i l ih =>
          obtain ⟨zTail, hTail, hTail'⟩ := ih
          obtain ⟨zPow, hPow, hPow'⟩ := hpow_mul_compatible i
            (basis.repr v₁ i) (basis.repr v₂ i)
          obtain ⟨zMove, hMove, hMove'⟩ := hmove_compatible
            (word l v₁) (word' l v₁)
            (xLift i ^ (basis.repr v₂ i).val)
            (yLift i ^ (basis.repr v₂ i).val)
            (hword_pi_compatible l v₁)
            (hlift_pow_pi_compatible i (basis.repr v₂ i))
          have hcoord : basis.repr (v₁ + v₂) i =
              basis.repr v₁ i + basis.repr v₂ i := by
            simp
          refine ⟨zPow * zTail * zMove, ?_, ?_⟩
          · have hcentralPow : Commute (iota zPow) (word l (v₁ + v₂)) :=
              (Subgroup.mem_center_iff.mp
                (hcentral ⟨zPow, rfl⟩) (word l (v₁ + v₂))).symm
            have hcentralMove : Commute (iota zMove) (word l v₂) :=
              (Subgroup.mem_center_iff.mp
                (hcentral ⟨zMove, rfl⟩) (word l v₂)).symm
            change
              (xLift i ^ (basis.repr v₁ i).val * word l v₁) *
                  (xLift i ^ (basis.repr v₂ i).val * word l v₂) =
                (xLift i ^ (basis.repr (v₁ + v₂) i).val *
                  word l (v₁ + v₂)) * iota (zPow * zTail * zMove)
            rw [hcoord]
            calc
              (xLift i ^ (basis.repr v₁ i).val * word l v₁) *
                    (xLift i ^ (basis.repr v₂ i).val * word l v₂) =
                  xLift i ^ (basis.repr v₁ i).val *
                    (word l v₁ * xLift i ^ (basis.repr v₂ i).val) *
                      word l v₂ := by group
              _ = xLift i ^ (basis.repr v₁ i).val *
                    (xLift i ^ (basis.repr v₂ i).val * word l v₁ * iota zMove) *
                      word l v₂ := by rw [hMove]
              _ = (xLift i ^ (basis.repr v₁ i).val *
                    xLift i ^ (basis.repr v₂ i).val) *
                      (word l v₁ * word l v₂) * iota zMove := by
                calc
                  xLift i ^ (basis.repr v₁ i).val *
                        (xLift i ^ (basis.repr v₂ i).val * word l v₁ *
                          iota zMove) * word l v₂ =
                      (xLift i ^ (basis.repr v₁ i).val *
                        xLift i ^ (basis.repr v₂ i).val) *
                          (word l v₁ * (iota zMove * word l v₂)) := by group
                  _ = (xLift i ^ (basis.repr v₁ i).val *
                        xLift i ^ (basis.repr v₂ i).val) *
                          (word l v₁ * (word l v₂ * iota zMove)) := by
                    rw [hcentralMove.eq]
                  _ = (xLift i ^ (basis.repr v₁ i).val *
                        xLift i ^ (basis.repr v₂ i).val) *
                          (word l v₁ * word l v₂) * iota zMove := by group
              _ = (xLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                    iota zPow) *
                      (word l (v₁ + v₂) * iota zTail) * iota zMove := by
                rw [hPow, hTail]
              _ = (xLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                    word l (v₁ + v₂)) * iota (zPow * zTail * zMove) := by
                rw [map_mul, map_mul]
                calc
                  (xLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        iota zPow) *
                        (word l (v₁ + v₂) * iota zTail) * iota zMove =
                      xLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        (iota zPow * word l (v₁ + v₂)) *
                          iota zTail * iota zMove := by group
                  _ = xLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        (word l (v₁ + v₂) * iota zPow) *
                          iota zTail * iota zMove := by
                    rw [hcentralPow.eq]
                  _ = (xLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        word l (v₁ + v₂)) *
                          (iota zPow * iota zTail * iota zMove) := by group
          · have hcentralPow : Commute
                (iota' (Multiplicative.ofAdd (g zPow.toAdd)))
                (word' l (v₁ + v₂)) :=
              (Subgroup.mem_center_iff.mp
                (hcentral' ⟨Multiplicative.ofAdd (g zPow.toAdd), rfl⟩)
                  (word' l (v₁ + v₂))).symm
            have hcentralMove : Commute
                (iota' (Multiplicative.ofAdd (g zMove.toAdd)))
                (word' l v₂) :=
              (Subgroup.mem_center_iff.mp
                (hcentral' ⟨Multiplicative.ofAdd (g zMove.toAdd), rfl⟩)
                  (word' l v₂)).symm
            change
              (yLift i ^ (basis.repr v₁ i).val * word' l v₁) *
                  (yLift i ^ (basis.repr v₂ i).val * word' l v₂) =
                (yLift i ^ (basis.repr (v₁ + v₂) i).val *
                  word' l (v₁ + v₂)) *
                    iota' (Multiplicative.ofAdd (g (zPow * zTail * zMove).toAdd))
            rw [hcoord]
            calc
              (yLift i ^ (basis.repr v₁ i).val * word' l v₁) *
                    (yLift i ^ (basis.repr v₂ i).val * word' l v₂) =
                  yLift i ^ (basis.repr v₁ i).val *
                    (word' l v₁ * yLift i ^ (basis.repr v₂ i).val) *
                      word' l v₂ := by group
              _ = yLift i ^ (basis.repr v₁ i).val *
                    (yLift i ^ (basis.repr v₂ i).val * word' l v₁ *
                      iota' (Multiplicative.ofAdd (g zMove.toAdd))) *
                        word' l v₂ := by rw [hMove']
              _ = (yLift i ^ (basis.repr v₁ i).val *
                    yLift i ^ (basis.repr v₂ i).val) *
                      (word' l v₁ * word' l v₂) *
                        iota' (Multiplicative.ofAdd (g zMove.toAdd)) := by
                calc
                  yLift i ^ (basis.repr v₁ i).val *
                        (yLift i ^ (basis.repr v₂ i).val * word' l v₁ *
                          iota' (Multiplicative.ofAdd (g zMove.toAdd))) *
                            word' l v₂ =
                      (yLift i ^ (basis.repr v₁ i).val *
                        yLift i ^ (basis.repr v₂ i).val) *
                          (word' l v₁ *
                            (iota' (Multiplicative.ofAdd (g zMove.toAdd)) *
                              word' l v₂)) := by group
                  _ = (yLift i ^ (basis.repr v₁ i).val *
                        yLift i ^ (basis.repr v₂ i).val) *
                          (word' l v₁ *
                            (word' l v₂ *
                              iota' (Multiplicative.ofAdd (g zMove.toAdd)))) := by
                    rw [hcentralMove.eq]
                  _ = (yLift i ^ (basis.repr v₁ i).val *
                        yLift i ^ (basis.repr v₂ i).val) *
                          (word' l v₁ * word' l v₂) *
                            iota' (Multiplicative.ofAdd (g zMove.toAdd)) := by group
              _ = (yLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                    iota' (Multiplicative.ofAdd (g zPow.toAdd))) *
                      (word' l (v₁ + v₂) *
                        iota' (Multiplicative.ofAdd (g zTail.toAdd))) *
                          iota' (Multiplicative.ofAdd (g zMove.toAdd)) := by
                rw [hPow', hTail']
              _ = (yLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                    word' l (v₁ + v₂)) *
                      iota' (Multiplicative.ofAdd (g (zPow * zTail * zMove).toAdd)) := by
                rw [hg_mul (zPow * zTail) zMove, hg_mul zPow zTail,
                  map_mul, map_mul]
                calc
                  (yLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        iota' (Multiplicative.ofAdd (g zPow.toAdd))) *
                        (word' l (v₁ + v₂) *
                          iota' (Multiplicative.ofAdd (g zTail.toAdd))) *
                            iota' (Multiplicative.ofAdd (g zMove.toAdd)) =
                      yLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        (iota' (Multiplicative.ofAdd (g zPow.toAdd)) *
                          word' l (v₁ + v₂)) *
                            iota' (Multiplicative.ofAdd (g zTail.toAdd)) *
                              iota' (Multiplicative.ofAdd (g zMove.toAdd)) := by group
                  _ = yLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        (word' l (v₁ + v₂) *
                          iota' (Multiplicative.ofAdd (g zPow.toAdd))) *
                            iota' (Multiplicative.ofAdd (g zTail.toAdd)) *
                              iota' (Multiplicative.ofAdd (g zMove.toAdd)) := by
                    rw [hcentralPow.eq]
                  _ = (yLift i ^ (basis.repr v₁ i + basis.repr v₂ i).val *
                        word' l (v₁ + v₂)) *
                          (iota' (Multiplicative.ofAdd (g zPow.toAdd)) *
                            iota' (Multiplicative.ofAdd (g zTail.toAdd)) *
                              iota' (Multiplicative.ofAdd (g zMove.toAdd))) := by group
    have hbasisWord_mul_compatible (v₁ v₂ : V) :
        ∃ z : Multiplicative W,
          basisWord v₁ * basisWord v₂ = basisWord (v₁ + v₂) * iota z ∧
          basisWord' v₁ * basisWord' v₂ =
            basisWord' (v₁ + v₂) *
              iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      simpa [basisWord, basisWord', word, word', List.ofFn_eq_map] using
        hword_mul_compatible
          (List.finRange (Module.finrank (ZMod 2) V)) v₁ v₂
    let mapFun : P → P' := fun x =>
      basisWord' (pi x).toAdd *
        iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd))
    let mapInv : P' → P := fun x =>
      basisWord (f.symm (pi' x).toAdd) *
        iota (Multiplicative.ofAdd (g.symm (kernelCoord' x).toAdd))
    have hmap_mul (x y : P) : mapFun (x * y) = mapFun x * mapFun y := by
      have hpi_mul : (pi (x * y)).toAdd = (pi x).toAdd + (pi y).toAdd := by
        simp
      obtain ⟨z, hword, hword'⟩ :=
        hbasisWord_mul_compatible (pi x).toAdd (pi y).toAdd
      have hcentralKernel : Commute (iota (kernelCoord x))
          (basisWord (pi y).toAdd) :=
        (Subgroup.mem_center_iff.mp
          (hcentral ⟨kernelCoord x, rfl⟩) (basisWord (pi y).toAdd)).symm
      have hkernelCoord_mul :
          kernelCoord (x * y) = z * kernelCoord x * kernelCoord y := by
        apply hiota
        apply mul_left_cancel (a := basisWord (pi (x * y)).toAdd)
        calc
          basisWord (pi (x * y)).toAdd * iota (kernelCoord (x * y)) =
              x * y := hnormalForm (x * y)
          _ = (basisWord (pi x).toAdd * iota (kernelCoord x)) *
                (basisWord (pi y).toAdd * iota (kernelCoord y)) := by
            rw [hnormalForm x, hnormalForm y]
          _ = (basisWord (pi x).toAdd * basisWord (pi y).toAdd) *
                (iota (kernelCoord x) * iota (kernelCoord y)) := by
            calc
              (basisWord (pi x).toAdd * iota (kernelCoord x)) *
                    (basisWord (pi y).toAdd * iota (kernelCoord y)) =
                  basisWord (pi x).toAdd *
                    (iota (kernelCoord x) * basisWord (pi y).toAdd) *
                      iota (kernelCoord y) := by group
              _ = basisWord (pi x).toAdd *
                    (basisWord (pi y).toAdd * iota (kernelCoord x)) *
                      iota (kernelCoord y) := by
                rw [hcentralKernel.eq]
              _ = (basisWord (pi x).toAdd * basisWord (pi y).toAdd) *
                    (iota (kernelCoord x) * iota (kernelCoord y)) := by group
          _ = (basisWord ((pi x).toAdd + (pi y).toAdd) * iota z) *
                (iota (kernelCoord x) * iota (kernelCoord y)) := by
            rw [hword]
          _ = basisWord (pi (x * y)).toAdd *
                iota (z * kernelCoord x * kernelCoord y) := by
            rw [hpi_mul, map_mul, map_mul]
            group
      have hcentralKernel' : Commute
          (iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)))
          (basisWord' (pi y).toAdd) :=
        (Subgroup.mem_center_iff.mp
          (hcentral' ⟨Multiplicative.ofAdd (g (kernelCoord x).toAdd), rfl⟩)
            (basisWord' (pi y).toAdd)).symm
      change
        basisWord' (pi (x * y)).toAdd *
            iota' (Multiplicative.ofAdd (g (kernelCoord (x * y)).toAdd)) =
          (basisWord' (pi x).toAdd *
              iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd))) *
            (basisWord' (pi y).toAdd *
              iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd)))
      rw [hpi_mul, hkernelCoord_mul, hg_mul (z * kernelCoord x) (kernelCoord y),
        hg_mul z (kernelCoord x), map_mul, map_mul]
      calc
        basisWord' ((pi x).toAdd + (pi y).toAdd) *
              (iota' (Multiplicative.ofAdd (g z.toAdd)) *
                iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)) *
                  iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd))) =
            (basisWord' ((pi x).toAdd + (pi y).toAdd) *
              iota' (Multiplicative.ofAdd (g z.toAdd))) *
                (iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)) *
                  iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd))) := by group
        _ = (basisWord' (pi x).toAdd * basisWord' (pi y).toAdd) *
              (iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)) *
                iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd))) := by
          rw [hword']
        _ = (basisWord' (pi x).toAdd *
              iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd))) *
                (basisWord' (pi y).toAdd *
                  iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd))) := by
          calc
            (basisWord' (pi x).toAdd * basisWord' (pi y).toAdd) *
                  (iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)) *
                    iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd))) =
                basisWord' (pi x).toAdd *
                  (basisWord' (pi y).toAdd *
                    iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd))) *
                      iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd)) := by group
            _ = basisWord' (pi x).toAdd *
                  (iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)) *
                    basisWord' (pi y).toAdd) *
                      iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd)) := by
              rw [hcentralKernel'.eq.symm]
            _ = (basisWord' (pi x).toAdd *
                  iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd))) *
                    (basisWord' (pi y).toAdd *
                      iota' (Multiplicative.ofAdd (g (kernelCoord y).toAdd))) := by group
    have hpi_iota (z : Multiplicative W) : pi (iota z) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← hexact]
      exact ⟨z, rfl⟩
    have hpi_iota' (z : Multiplicative W') : pi' (iota' z) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← hexact']
      exact ⟨z, rfl⟩
    have hmapFun_pi (x : P) :
        (pi' (mapFun x)).toAdd = f (pi x).toAdd := by
      change (pi' (basisWord' (pi x).toAdd *
        iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)))).toAdd =
          f (pi x).toAdd
      rw [map_mul, hpi_iota']
      simpa using hbasisWord'_pi (pi x).toAdd
    have hmapInv_pi (x : P') :
        (pi (mapInv x)).toAdd = f.symm (pi' x).toAdd := by
      change (pi (basisWord (f.symm (pi' x).toAdd) *
        iota (Multiplicative.ofAdd (g.symm (kernelCoord' x).toAdd)))).toAdd =
          f.symm (pi' x).toAdd
      rw [map_mul, hpi_iota]
      simpa using hbasisWord_pi (f.symm (pi' x).toAdd)
    have hmapFun_kernel (x : P) :
        kernelCoord' (mapFun x) =
          Multiplicative.ofAdd (g (kernelCoord x).toAdd) := by
      apply hiota'
      have hEq := hnormalForm' (mapFun x)
      rw [hmapFun_pi] at hEq
      simp only [LinearEquiv.symm_apply_apply] at hEq
      change basisWord' (pi x).toAdd * iota' (kernelCoord' (mapFun x)) =
        basisWord' (pi x).toAdd *
          iota' (Multiplicative.ofAdd (g (kernelCoord x).toAdd)) at hEq
      exact mul_left_cancel hEq
    have hmapInv_kernel (x : P') :
        kernelCoord (mapInv x) =
          Multiplicative.ofAdd (g.symm (kernelCoord' x).toAdd) := by
      apply hiota
      have hEq := hnormalForm (mapInv x)
      rw [hmapInv_pi] at hEq
      change basisWord (f.symm (pi' x).toAdd) *
          iota (kernelCoord (mapInv x)) =
        basisWord (f.symm (pi' x).toAdd) *
          iota (Multiplicative.ofAdd (g.symm (kernelCoord' x).toAdd)) at hEq
      exact mul_left_cancel hEq
    have hmap_left (x : P) : mapInv (mapFun x) = x := by
      change basisWord (f.symm (pi' (mapFun x)).toAdd) *
          iota (Multiplicative.ofAdd
            (g.symm (kernelCoord' (mapFun x)).toAdd)) = x
      rw [hmapFun_pi, hmapFun_kernel]
      simpa using hnormalForm x
    have hmap_right (x : P') : mapFun (mapInv x) = x := by
      change basisWord' (pi (mapInv x)).toAdd *
          iota' (Multiplicative.ofAdd
            (g (kernelCoord (mapInv x)).toAdd)) = x
      rw [hmapInv_pi, hmapInv_kernel]
      simpa using hnormalForm' x
    have hmap_bijective : Function.Bijective mapFun := by
      constructor
      · intro x y hxy
        have h := congrArg mapInv hxy
        rw [hmap_left x, hmap_left y] at h
        exact h
      · intro y
        exact ⟨mapInv y, hmap_right y⟩
    have hmap_pi (x : P) :
        (pi' (mapFun x)).toAdd = f (pi x).toAdd := by
      exact hmapFun_pi x
    have hkernelCoord_iota (z : Multiplicative W) :
        kernelCoord (iota z) = z := by
      apply hiota
      have hEq := hnormalForm (iota z)
      rw [hpi_iota] at hEq
      simpa [basisWord] using hEq
    have hmap_iota (z : Multiplicative W) :
        mapFun (iota z) =
          iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      change basisWord' (pi (iota z)).toAdd *
          iota' (Multiplicative.ofAdd (g (kernelCoord (iota z)).toAdd)) =
        iota' (Multiplicative.ofAdd (g z.toAdd))
      rw [hpi_iota, hkernelCoord_iota]
      simp [basisWord']
    let eHom : P →* P' := MonoidHom.mk' mapFun hmap_mul
    have heHom_bijective : Function.Bijective eHom := by
      simpa [eHom] using hmap_bijective
    let e : P ≃* P' := MulEquiv.ofBijective eHom heHom_bijective
    have he_pi (x : P) : (pi' (e x)).toAdd = f (pi x).toAdd := by
      change (pi' (mapFun x)).toAdd = f (pi x).toAdd
      exact hmap_pi x
    have he_iota (z : Multiplicative W) :
        e (iota z) = iota' (Multiplicative.ofAdd (g z.toAdd)) := by
      change mapFun (iota z) = iota' (Multiplicative.ofAdd (g z.toAdd))
      exact hmap_iota z
    exact ⟨e, he_pi, he_iota⟩
/-- Appendix III, Lemma 1(d). Automorphisms acting trivially on the kernel and
quotient are parametrized additively by Hom(V,W). -/
public theorem lemma1d_extension_kernel_automorphisms
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {P : Type u} [Group P]
    (iota : Multiplicative W →* P) (pi : P →* Multiplicative V)
    (hiota : Function.Injective iota) (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P) :
    ∃ encode : (V →ₗ[ZMod 2] W) → MulAut P,
      Function.Injective encode ∧
      encode 0 = 1 ∧
      (∀ f g, encode (f + g) = encode f * encode g) ∧
      (∀ f x, pi (encode f x) = pi x) ∧
      (∀ f z, encode f (iota z) = iota z) ∧
      ∀ alpha : MulAut P,
        (∀ x, pi (alpha x) = pi x) →
        (∀ z, alpha (iota z) = iota z) →
        ∃! f, encode f = alpha := by
  have hpi_iota (z : Multiplicative W) : pi (iota z) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← hexact]
    exact ⟨z, rfl⟩
  let twist (f : V →ₗ[ZMod 2] W) (x : P) : P :=
    x * iota (Multiplicative.ofAdd (f (pi x).toAdd))
  have htwist_pi (f : V →ₗ[ZMod 2] W) (x : P) :
      pi (twist f x) = pi x := by
    change pi (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) = pi x
    rw [map_mul, hpi_iota, mul_one]
  have htwist_mul (f : V →ₗ[ZMod 2] W) (x y : P) :
      twist f (x * y) = twist f x * twist f y := by
    have hcentralFx : Commute
        (iota (Multiplicative.ofAdd (f (pi x).toAdd))) y :=
      (Subgroup.mem_center_iff.mp
        (hcentral ⟨Multiplicative.ofAdd (f (pi x).toAdd), rfl⟩) y).symm
    change
      x * y * iota (Multiplicative.ofAdd (f ((pi (x * y)).toAdd))) =
        (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
          (y * iota (Multiplicative.ofAdd (f (pi y).toAdd)))
    rw [map_mul]
    change
      x * y * iota (Multiplicative.ofAdd
          (f ((pi x).toAdd + (pi y).toAdd))) =
        (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
          (y * iota (Multiplicative.ofAdd (f (pi y).toAdd)))
    rw [map_add]
    change
      x * y * iota
          (Multiplicative.ofAdd (f (pi x).toAdd) *
            Multiplicative.ofAdd (f (pi y).toAdd)) =
        (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
          (y * iota (Multiplicative.ofAdd (f (pi y).toAdd)))
    rw [map_mul]
    calc
      x * y *
            (iota (Multiplicative.ofAdd (f (pi x).toAdd)) *
              iota (Multiplicative.ofAdd (f (pi y).toAdd))) =
          x * (y * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
            iota (Multiplicative.ofAdd (f (pi y).toAdd)) := by group
      _ = x * (iota (Multiplicative.ofAdd (f (pi x).toAdd)) * y) *
            iota (Multiplicative.ofAdd (f (pi y).toAdd)) := by
        rw [hcentralFx.eq]
      _ = (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
            (y * iota (Multiplicative.ofAdd (f (pi y).toAdd))) := by group
  have htwist_involutive (f : V →ₗ[ZMod 2] W) :
      Function.Involutive (twist f) := by
    intro x
    change twist f x *
        iota (Multiplicative.ofAdd (f (pi (twist f x)).toAdd)) = x
    rw [htwist_pi]
    change
      (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
          iota (Multiplicative.ofAdd (f (pi x).toAdd)) = x
    calc
      (x * iota (Multiplicative.ofAdd (f (pi x).toAdd))) *
            iota (Multiplicative.ofAdd (f (pi x).toAdd)) =
          x * (iota (Multiplicative.ofAdd (f (pi x).toAdd)) *
            iota (Multiplicative.ofAdd (f (pi x).toAdd))) := by group
      _ = x * iota (Multiplicative.ofAdd
            (f (pi x).toAdd + f (pi x).toAdd)) := by
        rw [← map_mul]
        rfl
      _ = x := by
        rw [ZModModule.add_self]
        simp
  let encode : (V →ₗ[ZMod 2] W) → MulAut P := fun f =>
    { toFun := twist f
      invFun := twist f
      left_inv := htwist_involutive f
      right_inv := htwist_involutive f
      map_mul' := htwist_mul f }
  have hencode_injective : Function.Injective encode := by
    intro f g hfg
    apply LinearMap.ext
    intro v
    obtain ⟨x, hx⟩ := hpi (Multiplicative.ofAdd v)
    have happ := DFunLike.congr_fun hfg x
    change twist f x = twist g x at happ
    change
      x * iota (Multiplicative.ofAdd (f (pi x).toAdd)) =
        x * iota (Multiplicative.ofAdd (g (pi x).toAdd)) at happ
    have hiotaEq :
        iota (Multiplicative.ofAdd (f (pi x).toAdd)) =
          iota (Multiplicative.ofAdd (g (pi x).toAdd)) :=
      mul_left_cancel happ
    have hOfAdd : Multiplicative.ofAdd (f v) = Multiplicative.ofAdd (g v) := by
      apply hiota
      simpa [hx] using hiotaEq
    simpa using congrArg Multiplicative.toAdd hOfAdd
  have hencode_zero : encode 0 = 1 := by
    apply MulEquiv.ext
    intro x
    change twist 0 x = x
    simp [twist]
  have hencode_add (f g : V →ₗ[ZMod 2] W) :
      encode (f + g) = encode f * encode g := by
    apply MulEquiv.ext
    intro x
    change twist (f + g) x = twist f (twist g x)
    change
      x * iota (Multiplicative.ofAdd ((f + g) (pi x).toAdd)) =
        twist g x *
          iota (Multiplicative.ofAdd (f (pi (twist g x)).toAdd))
    rw [htwist_pi]
    change
      x * iota (Multiplicative.ofAdd
          (f (pi x).toAdd + g (pi x).toAdd)) =
        (x * iota (Multiplicative.ofAdd (g (pi x).toAdd))) *
          iota (Multiplicative.ofAdd (f (pi x).toAdd))
    change
      x * iota
          (Multiplicative.ofAdd (f (pi x).toAdd) *
            Multiplicative.ofAdd (g (pi x).toAdd)) =
        (x * iota (Multiplicative.ofAdd (g (pi x).toAdd))) *
          iota (Multiplicative.ofAdd (f (pi x).toAdd))
    rw [map_mul]
    have hcomm : Commute
        (iota (Multiplicative.ofAdd (f (pi x).toAdd)))
        (iota (Multiplicative.ofAdd (g (pi x).toAdd))) :=
      (Subgroup.mem_center_iff.mp
        (hcentral ⟨Multiplicative.ofAdd (f (pi x).toAdd), rfl⟩)
          (iota (Multiplicative.ofAdd (g (pi x).toAdd)))).symm
    rw [hcomm.eq]
    group
  have hencode_pi (f : V →ₗ[ZMod 2] W) (x : P) :
      pi (encode f x) = pi x := by
    exact htwist_pi f x
  have hencode_iota (f : V →ₗ[ZMod 2] W) (z : Multiplicative W) :
      encode f (iota z) = iota z := by
    change twist f (iota z) = iota z
    change iota z *
        iota (Multiplicative.ofAdd (f (pi (iota z)).toAdd)) = iota z
    rw [hpi_iota]
    simp
  have hclassify (alpha : MulAut P)
      (halpha_pi : ∀ x, pi (alpha x) = pi x)
      (halpha_iota : ∀ z, alpha (iota z) = iota z) :
      ∃! f, encode f = alpha := by
    have hdelta_mem (x : P) : x⁻¹ * alpha x ∈ iota.range := by
      rw [hexact, MonoidHom.mem_ker]
      simp [halpha_pi]
    let delta (x : P) : Multiplicative W :=
      Classical.choose (hdelta_mem x)
    have hdelta (x : P) : iota (delta x) = x⁻¹ * alpha x :=
      Classical.choose_spec (hdelta_mem x)
    have halpha_delta (x : P) : alpha x = x * iota (delta x) := by
      rw [hdelta]
      group
    have hdelta_mul (x y : P) : delta (x * y) = delta x * delta y := by
      apply hiota
      have hcentralDelta : Commute (iota (delta x)) y⁻¹ :=
        (Subgroup.mem_center_iff.mp
          (hcentral ⟨delta x, rfl⟩) y⁻¹).symm
      calc
        iota (delta (x * y)) = (x * y)⁻¹ * alpha (x * y) :=
          hdelta (x * y)
        _ = y⁻¹ * x⁻¹ * (alpha x * alpha y) := by
          rw [map_mul, mul_inv_rev]
        _ = y⁻¹ * (x⁻¹ * alpha x) * alpha y := by group
        _ = y⁻¹ * iota (delta x) * alpha y := by rw [hdelta x]
        _ = iota (delta x) * y⁻¹ * alpha y := by
          rw [hcentralDelta.eq.symm]
        _ = iota (delta x) * (y⁻¹ * alpha y) := by group
        _ = iota (delta x) * iota (delta y) := by rw [hdelta y]
        _ = iota (delta x * delta y) := (map_mul iota _ _).symm
    let deltaHom : P →* Multiplicative W := MonoidHom.mk' delta hdelta_mul
    have hdeltaHom_apply (x : P) : deltaHom x = delta x := rfl
    have hdelta_iota (z : Multiplicative W) : deltaHom (iota z) = 1 := by
      apply hiota
      change iota (delta (iota z)) = iota 1
      rw [hdelta, halpha_iota]
      simp
    have hdelta_eq_of_pi_eq {x y : P} (hxy : pi x = pi y) :
        deltaHom x = deltaHom y := by
      have hmem : x⁻¹ * y ∈ iota.range := by
        rw [hexact, MonoidHom.mem_ker]
        simp [hxy]
      obtain ⟨z, hz⟩ := hmem
      have hquot : (deltaHom x)⁻¹ * deltaHom y = 1 := by
        calc
          (deltaHom x)⁻¹ * deltaHom y = deltaHom (x⁻¹ * y) := by
            rw [map_mul, map_inv]
          _ = deltaHom (iota z) := by rw [hz]
          _ = 1 := hdelta_iota z
      calc
        deltaHom x = deltaHom x * 1 := (mul_one _).symm
        _ = deltaHom x * ((deltaHom x)⁻¹ * deltaHom y) := by rw [hquot]
        _ = deltaHom y := by group
    let repr (v : V) : P := Classical.choose (hpi (Multiplicative.ofAdd v))
    have hrepr (v : V) : pi (repr v) = Multiplicative.ofAdd v :=
      Classical.choose_spec (hpi (Multiplicative.ofAdd v))
    let linearFun (v : V) : W := (deltaHom (repr v)).toAdd
    have hlinearFun_add (v w : V) :
        linearFun (v + w) = linearFun v + linearFun w := by
      have hEq : deltaHom (repr (v + w)) = deltaHom (repr v * repr w) := by
        apply hdelta_eq_of_pi_eq
        rw [hrepr, map_mul, hrepr, hrepr]
        rfl
      rw [map_mul] at hEq
      simpa [linearFun] using congrArg Multiplicative.toAdd hEq
    have hlinearFun_zero : linearFun 0 = 0 := by
      have hEq : deltaHom (repr 0) = deltaHom 1 := by
        apply hdelta_eq_of_pi_eq
        simp [hrepr]
      simpa [linearFun] using congrArg Multiplicative.toAdd hEq
    have hscalar_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
      by_cases hc : c.val = 0
      · left
        apply ZMod.val_injective 2
        simpa using hc
      · right
        apply ZMod.val_injective 2
        rw [ZMod.val_one 2]
        have hc_lt : c.val < 2 := ZMod.val_lt c
        omega
    have hlinearFun_smul (c : ZMod 2) (v : V) :
        linearFun (c • v) = c • linearFun v := by
      rcases hscalar_cases c with rfl | rfl
      · simp [hlinearFun_zero]
      · simp
    let descended : V →ₗ[ZMod 2] W :=
      { toFun := linearFun
        map_add' := hlinearFun_add
        map_smul' := hlinearFun_smul }
    have hdescended_delta (x : P) :
        Multiplicative.ofAdd (descended (pi x).toAdd) = deltaHom x := by
      change deltaHom (repr (pi x).toAdd) = deltaHom x
      apply hdelta_eq_of_pi_eq
      rw [hrepr]
      rfl
    have hencode_alpha : encode descended = alpha := by
      apply MulEquiv.ext
      intro x
      change twist descended x = alpha x
      change x * iota (Multiplicative.ofAdd (descended (pi x).toAdd)) =
        alpha x
      rw [hdescended_delta]
      exact (halpha_delta x).symm
    refine ⟨descended, hencode_alpha, ?_⟩
    intro f hf
    apply hencode_injective
    exact hf.trans hencode_alpha.symm
  exact ⟨encode, hencode_injective, hencode_zero, hencode_add,
    hencode_pi, hencode_iota, hclassify⟩

end PFAppendixIII
end CFSG.BenderSuzuki
