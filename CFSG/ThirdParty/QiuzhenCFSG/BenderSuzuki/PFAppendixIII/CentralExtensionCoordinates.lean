module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basis

namespace CFSG
end CFSG
open CFSG

/-!
# Coordinates for binary central extensions

This module formalizes the ordered-basis collection argument used implicitly
in Peterfalvi Appendix III, Lemma 1(c).
-/

open scoped BigOperators
open scoped commutatorElement

namespace CFSG.BenderSuzuki
namespace PFAppendixIII

private def word {P : Type*} [Group P]
    (x : ℕ → P) (a : ℕ → ZMod 2) (k : ℕ) : P :=
  ((List.range k).map fun i => x i ^ (a i).val).prod

private def cross {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2) (j k : ℕ) : P :=
  ((List.range k).map fun i => ⁅x j, x i⁆ ^ (a j * b i).val).prod

private def defect {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2) (k : ℕ) : P :=
  ((List.range k).map fun j =>
    (x j ^ 2) ^ (a j * b j).val *
      ((List.range j).map fun i =>
        ⁅x j, x i⁆ ^ (a j * b i).val).prod).prod

private lemma word_succ {P : Type*} [Group P]
    (x : ℕ → P) (a : ℕ → ZMod 2) (k : ℕ) :
    word x a (k + 1) = word x a k * x k ^ (a k).val := by
  simp [word, List.range_succ]

private lemma cross_succ {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2) (j k : ℕ) :
    cross x a b j (k + 1) =
      cross x a b j k * ⁅x j, x k⁆ ^ (a j * b k).val := by
  simp [cross, List.range_succ]

private lemma defect_succ {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2) (k : ℕ) :
    defect x a b (k + 1) = defect x a b k *
      ((x k ^ 2) ^ (a k * b k).val * cross x a b k k) := by
  simp [defect, cross, List.range_succ]

private lemma bit_pow_mul_bit_pow {P : Type*} [Group P]
    (x : P) (a b : ZMod 2) :
    x ^ a.val * x ^ b.val =
      x ^ (a + b).val * (x ^ 2) ^ (a * b).val := by
  rw [ZMod.val_add, ZMod.val_mul]
  have ha := a.val_lt
  have hb := b.val_lt
  interval_cases haa : a.val <;> interval_cases hbb : b.val <;>
    norm_num [haa, hbb, pow_two]

private lemma bit_pow_mul_bit_pow_swap {P : Type*} [Group P]
    (x y : P) (a b : ZMod 2)
    (hc : ⁅x, y⁆ ∈ Subgroup.center P) :
    x ^ a.val * y ^ b.val =
      y ^ b.val * x ^ a.val * ⁅x, y⁆ ^ (a * b).val := by
  have hxy : x * y = y * x * ⁅x, y⁆ := by
    calc
      x * y = ⁅x, y⁆ * (y * x) := by
        simp [commutatorElement_def]
      _ = (y * x) * ⁅x, y⁆ :=
        (Subgroup.mem_center_iff.mp hc (y * x)).symm
  rw [ZMod.val_mul]
  have ha := a.val_lt
  have hb := b.val_lt
  interval_cases haa : a.val <;> interval_cases hbb : b.val <;>
    norm_num [haa, hbb, hxy]

private lemma cross_mem_center {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2)
    (hclass : ∀ i j, ⁅x i, x j⁆ ∈ Subgroup.center P) (j k : ℕ) :
    cross x a b j k ∈ Subgroup.center P := by
  rw [cross]
  apply list_prod_mem
  rintro y hy
  simp only [List.mem_map] at hy
  rcases hy with ⟨i, hi, rfl⟩
  exact (Subgroup.center P).pow_mem (hclass j i) _

private lemma defect_mem_center {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2)
    (hsq : ∀ i, x i ^ 2 ∈ Subgroup.center P)
    (hclass : ∀ i j, ⁅x i, x j⁆ ∈ Subgroup.center P) (k : ℕ) :
    defect x a b k ∈ Subgroup.center P := by
  rw [defect]
  apply list_prod_mem
  rintro y hy
  simp only [List.mem_map] at hy
  rcases hy with ⟨j, hj, rfl⟩
  apply (Subgroup.center P).mul_mem
  · exact (Subgroup.center P).pow_mem (hsq j) _
  · apply list_prod_mem
    rintro y hy
    simp only [List.mem_map] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact (Subgroup.center P).pow_mem (hclass j i) _

private lemma move_word {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2)
    (hclass : ∀ i j, ⁅x i, x j⁆ ∈ Subgroup.center P) :
    ∀ j k, x j ^ (a j).val * word x b k =
      word x b k * x j ^ (a j).val * cross x a b j k := by
  intro j k
  induction k with
  | zero => simp [word, cross]
  | succ k ih =>
      rw [word_succ, cross_succ]
      have hcross_center := cross_mem_center x a b hclass j k
      have hswap := bit_pow_mul_bit_pow_swap
        (x j) (x k) (a j) (b k) (hclass j k)
      have hcY : Commute (cross x a b j k) (x k ^ (b k).val) :=
        (Subgroup.mem_center_iff.mp hcross_center _).symm
      have hcommC : Commute
          (⁅x j, x k⁆ ^ (a j * b k).val) (cross x a b j k) :=
        (Subgroup.mem_center_iff.mp
          ((Subgroup.center P).pow_mem (hclass j k) _) _).symm
      calc
        x j ^ (a j).val * (word x b k * x k ^ (b k).val) =
            (x j ^ (a j).val * word x b k) * x k ^ (b k).val := by
          rw [mul_assoc]
        _ = (word x b k * x j ^ (a j).val * cross x a b j k) *
              x k ^ (b k).val := by rw [ih]
        _ = word x b k * (x j ^ (a j).val * x k ^ (b k).val) *
              cross x a b j k := by
          simp only [mul_assoc]
          rw [hcY.eq]
        _ = word x b k *
              (x k ^ (b k).val * x j ^ (a j).val *
                ⁅x j, x k⁆ ^ (a j * b k).val) * cross x a b j k := by
          rw [hswap]
        _ = (word x b k * x k ^ (b k).val) * x j ^ (a j).val *
              (cross x a b j k * ⁅x j, x k⁆ ^ (a j * b k).val) := by
          simp only [mul_assoc]
          rw [hcommC.eq]

private theorem word_mul_word {P : Type*} [Group P]
    (x : ℕ → P) (a b : ℕ → ZMod 2)
    (hsq : ∀ i, x i ^ 2 ∈ Subgroup.center P)
    (hclass : ∀ i j, ⁅x i, x j⁆ ∈ Subgroup.center P) :
    ∀ k, word x a k * word x b k =
      word x (a + b) k * defect x a b k := by
  intro k
  induction k with
  | zero => simp [word, defect]
  | succ k ih =>
      rw [word_succ, word_succ, word_succ, defect_succ]
      have hdef_center := defect_mem_center x a b hsq hclass k
      have hcross_center := cross_mem_center x a b hclass k k
      have hbit := bit_pow_mul_bit_pow (x k) (a k) (b k)
      have hmove := move_word x a b hclass k k
      have hcX : Commute (cross x a b k k) (x k ^ (b k).val) :=
        (Subgroup.mem_center_iff.mp hcross_center _).symm
      have hdA : Commute (defect x a b k) (x k ^ (a k).val) :=
        (Subgroup.mem_center_iff.mp hdef_center _).symm
      have hdB : Commute (defect x a b k) (x k ^ (b k).val) :=
        (Subgroup.mem_center_iff.mp hdef_center _).symm
      have hdiag : (x k ^ 2) ^ (a k * b k).val ∈ Subgroup.center P :=
        (Subgroup.center P).pow_mem (hsq k) _
      have hdiagD : Commute ((x k ^ 2) ^ (a k * b k).val)
          (defect x a b k) :=
        (Subgroup.mem_center_iff.mp hdiag _).symm
      calc
        (word x a k * x k ^ (a k).val) *
            (word x b k * x k ^ (b k).val) =
          (word x a k * word x b k) *
            (x k ^ (a k).val * x k ^ (b k).val) * cross x a b k k := by
              calc
                _ = word x a k *
                    ((x k ^ (a k).val * word x b k) * x k ^ (b k).val) := by
                      simp only [mul_assoc]
                _ = word x a k *
                    (((word x b k * x k ^ (a k).val) * cross x a b k k) *
                      x k ^ (b k).val) := by rw [hmove]
                _ = _ := by
                  simp only [mul_assoc]
                  rw [hcX.eq]
        _ = (word x (a + b) k * defect x a b k) *
            (x k ^ (a k).val * x k ^ (b k).val) * cross x a b k k := by
              rw [ih]
        _ = word x (a + b) k *
            (x k ^ (a k).val * x k ^ (b k).val) *
              (defect x a b k * cross x a b k k) := by
                simp only [mul_assoc]
                rw [← mul_assoc (defect x a b k) (x k ^ (a k).val)]
                rw [hdA.eq]
                simp only [mul_assoc]
                rw [← mul_assoc (defect x a b k) (x k ^ (b k).val)]
                rw [hdB.eq]
                simp only [mul_assoc]
        _ = word x (a + b) k *
            (x k ^ ((a + b) k).val * (x k ^ 2) ^ (a k * b k).val) *
              (defect x a b k * cross x a b k k) := by
                rw [show (a + b) k = a k + b k by rfl, hbit]
        _ = (word x (a + b) k * x k ^ ((a + b) k).val) *
            (defect x a b k *
              ((x k ^ 2) ^ (a k * b k).val * cross x a b k k)) := by
                simp only [mul_assoc]
                rw [← mul_assoc ((x k ^ 2) ^ (a k * b k).val)]
                rw [hdiagD.eq]
                simp only [mul_assoc]

private lemma ofAdd_zmod2_smul {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] (c : ZMod 2) (w : W) :
    Multiplicative.ofAdd (c • w) = Multiplicative.ofAdd w ^ c.val := by
  apply Multiplicative.toAdd.injective
  change c • w = c.val • w
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]

private theorem exists_quadratic_refinement
    {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hB_self : ∀ x : V, B x x = 0) :
    ∃ f : V → W, f 0 = 0 ∧
      ∀ x y : V, f (x + y) = f x + f y + B x y := by
  classical
  let d := Module.finrank (ZMod 2) V
  let basis : Module.Basis (Fin d) (ZMod 2) V :=
    Module.finBasis (ZMod 2) V
  have hadd_self (z : W) : z + z = 0 := by
    nth_rw 2 [← ZModModule.neg_eq_self z]
    exact add_neg_cancel z
  have hB_symm (x y : V) : B x y = B y x := by
    have hsum : B x y + B y x = 0 := by
      have h := hB_self (x + y)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hB_self, hB_self] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      B x y = B x y + (B y x + B y x) := by
        rw [hadd_self, add_zero]
      _ = (B x y + B y x) + B y x := by abel
      _ = B y x := by rw [hsum, zero_add]
  let A : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W :=
    basis.constr (S := ZMod 2) fun i =>
      basis.constr (S := ZMod 2) fun j =>
        if i < j then B (basis i) (basis j) else 0
  have hA_basis (i j : Fin d) :
      A (basis i) (basis j) =
        if i < j then B (basis i) (basis j) else 0 := by
    change
      (basis.constr (S := ZMod 2) fun i =>
        basis.constr (S := ZMod 2) fun j =>
          if i < j then B (basis i) (basis j) else 0)
        (basis i) (basis j) = _
    rw [basis.constr_basis, basis.constr_basis]
  have hA_polar : A + LinearMap.flip A = B := by
    apply basis.ext
    intro i
    apply basis.ext
    intro j
    simp only [LinearMap.add_apply, LinearMap.flip_apply]
    rw [hA_basis, hA_basis]
    by_cases hij : i = j
    · subst j
      simp [hB_self]
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hnji : ¬j < i := not_lt_of_ge hij.le
        simp [hij, hnji]
      · have hnij : ¬i < j := not_lt_of_ge hji.le
        simp [hji, hnij, hB_symm]
  let f : V → W := fun x => A x x
  refine ⟨f, by simp [f], ?_⟩
  intro x y
  have hp := LinearMap.congr_fun (LinearMap.congr_fun hA_polar x) y
  change A x y + A y x = B x y at hp
  change A (x + y) (x + y) = A x x + A y y + B x y
  calc
    A (x + y) (x + y) =
        A x x + A y x + (A x y + A y y) := by
          simp only [map_add, LinearMap.add_apply]
    _ = A x x + A y y + B x y := by rw [← hp]; abel

/-- A central extension of finite-dimensional binary vector spaces admits
ordered coordinates whose multiplication defect is bilinear. -/
public theorem exists_bilinear_coordinates_of_central_extension
    {V W P : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [Group P]
    (iota : Multiplicative W →* P) (pi : P →* Multiplicative V)
    (hiota : Function.Injective iota) (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P)
    (q : V → W)
    (hsquare : ∀ x : P,
      iota (Multiplicative.ofAdd (q (pi x).toAdd)) = x ^ 2) :
    ∃ (pairLift : V → W → P) (cocycle : V → V → W),
      (∀ a b c, cocycle (a + b) c = cocycle a c + cocycle b c) ∧
      (∀ a b c, cocycle a (b + c) = cocycle a b + cocycle a c) ∧
      (∀ a, cocycle a a = q a) ∧
      pairLift 0 0 = 1 ∧
      (∀ x : P, ∃ a z, x = pairLift a z) ∧
      (∀ a z b w, pairLift a z = pairLift b w → a = b ∧ z = w) ∧
      (∀ a z b w,
        pairLift a z * pairLift b w =
          pairLift (a + b) (z + w + cocycle a b)) ∧
      (∀ a z, pi (pairLift a z) = Multiplicative.ofAdd a) ∧
      ∀ z, pairLift 0 z = iota (Multiplicative.ofAdd z) := by
  classical
  let iotaKer : Multiplicative W →* pi.ker :=
    iota.codRestrict pi.ker fun z => by
      rw [← hexact]
      exact ⟨z, rfl⟩
  have hiotaKer : Function.Bijective iotaKer := by
    constructor
    · intro z w hzw
      apply hiota
      exact congrArg Subtype.val hzw
    · rintro ⟨p, hp⟩
      have hp' : p ∈ iota.range := by simpa [hexact] using hp
      rcases hp' with ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  let kernelEquiv : Multiplicative W ≃* pi.ker :=
    MulEquiv.ofBijective iotaKer hiotaKer
  let d := Module.finrank (ZMod 2) V
  let basis : Module.Basis (Fin d) (ZMod 2) V := Module.finBasis (ZMod 2) V
  let basisN : ℕ → V := fun i => if hi : i < d then basis ⟨i, hi⟩ else 0
  let lift : ℕ → P := fun i => Classical.choose (hpi (Multiplicative.ofAdd (basisN i)))
  have hlift (i : ℕ) : pi (lift i) = Multiplicative.ofAdd (basisN i) :=
    Classical.choose_spec (hpi (Multiplicative.ofAdd (basisN i)))
  let coeff : V → ℕ → ZMod 2 := fun v i =>
    if hi : i < d then basis.repr v ⟨i, hi⟩ else 0
  let sec : V → P := fun v => word lift (coeff v) d
  have hpi_word (v : V) : ∀ k,
      (pi (word lift (coeff v) k)).toAdd =
        ∑ i ∈ Finset.range k, (coeff v i).val • basisN i := by
    intro k
    induction k with
    | zero => simp [word]
    | succ k ih =>
        calc
          (pi (word lift (coeff v) (k + 1))).toAdd =
              (pi (word lift (coeff v) k)).toAdd +
                (pi (lift k ^ (coeff v k).val)).toAdd := by
                  rw [word_succ, map_mul]
                  rfl
          _ = (∑ i ∈ Finset.range k, (coeff v i).val • basisN i) +
                (coeff v k).val • basisN k := by
                  rw [ih, map_pow, hlift]
                  rfl
          _ = ∑ i ∈ Finset.range (k + 1),
                (coeff v i).val • basisN i := by
                  rw [Finset.sum_range_succ]
  have hpi_sec (v : V) : pi (sec v) = Multiplicative.ofAdd v := by
    apply Multiplicative.toAdd.injective
    calc
      (pi (sec v)).toAdd =
          ∑ i ∈ Finset.range d, (coeff v i).val • basisN i := by
        exact hpi_word v d
      _ = ∑ i : Fin d, basis.repr v i • basis i := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        have hid : i < d := Finset.mem_range.mp hi
        simp only [coeff, basisN, hid, ↓reduceDIte]
        rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
      _ = v := basis.sum_repr v
  have hcoeff_add (a b : V) : coeff (a + b) = coeff a + coeff b := by
    funext i
    by_cases hi : i < d
    · simp [coeff, hi]
    · simp [coeff, hi]
  have hsec_zero : sec 0 = 1 := by
    simp [sec, word, coeff]
  have hpi_iota (z : Multiplicative W) : pi (iota z) = 1 := by
    change iota z ∈ pi.ker
    rw [← hexact]
    exact ⟨z, rfl⟩
  have hsq_ker (i : ℕ) : pi (lift i ^ 2) = 1 := by
    rw [map_pow, hlift]
    apply Multiplicative.toAdd.injective
    change 2 • basisN i = 0
    exact ZModModule.char_nsmul_eq_zero 2 (basisN i)
  have hcomm_ker (j i : ℕ) : pi ⁅lift j, lift i⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hsq_center (i : ℕ) : lift i ^ 2 ∈ Subgroup.center P := by
    apply hcentral
    rw [hexact]
    exact hsq_ker i
  have hcomm_center (j i : ℕ) : ⁅lift j, lift i⁆ ∈ Subgroup.center P := by
    apply hcentral
    rw [hexact]
    exact hcomm_ker j i
  let sqCoord : ℕ → W := fun i =>
    (kernelEquiv.symm ⟨lift i ^ 2, hsq_ker i⟩).toAdd
  let commCoord : ℕ → ℕ → W := fun j i =>
    (kernelEquiv.symm ⟨⁅lift j, lift i⁆, hcomm_ker j i⟩).toAdd
  have hiota_sq (i : ℕ) :
      iota (Multiplicative.ofAdd (sqCoord i)) = lift i ^ 2 := by
    have h := kernelEquiv.apply_symm_apply ⟨lift i ^ 2, hsq_ker i⟩
    exact congrArg Subtype.val h
  have hiota_comm (j i : ℕ) :
      iota (Multiplicative.ofAdd (commCoord j i)) = ⁅lift j, lift i⁆ := by
    have h := kernelEquiv.apply_symm_apply
      ⟨⁅lift j, lift i⁆, hcomm_ker j i⟩
    exact congrArg Subtype.val h
  let cocycle : V → V → W := fun a b =>
    ((List.range d).map fun j =>
      (coeff a j * coeff b j) • sqCoord j +
        ((List.range j).map fun i =>
          (coeff a j * coeff b i) • commCoord j i).sum).sum
  have hcocycle_add_left (a b c : V) :
      cocycle (a + b) c = cocycle a c + cocycle b c := by
    simp [cocycle, hcoeff_add, add_mul, add_smul, List.sum_map_add,
      add_assoc]
    ; abel
  have hcocycle_add_right (a b c : V) :
      cocycle a (b + c) = cocycle a b + cocycle a c := by
    simp [cocycle, hcoeff_add, mul_add, add_smul, List.sum_map_add,
      add_assoc]
    ; abel
  have hiota_cocycle (a b : V) :
      iota (Multiplicative.ofAdd (cocycle a b)) =
        defect lift (coeff a) (coeff b) d := by
    have hcomm_list (j : ℕ) : ∀ l : List ℕ,
        iota (Multiplicative.ofAdd
          ((l.map fun i => (coeff a j * coeff b i) • commCoord j i).sum)) =
          (l.map fun i =>
            ⁅lift j, lift i⁆ ^ (coeff a j * coeff b i).val).prod := by
      intro l
      induction l with
      | nil => simp
      | cons i l ih =>
          simp only [List.map_cons, List.sum_cons, List.prod_cons]
          rw [show Multiplicative.ofAdd
                ((coeff a j * coeff b i) • commCoord j i +
                  (l.map fun i => (coeff a j * coeff b i) • commCoord j i).sum) =
              Multiplicative.ofAdd ((coeff a j * coeff b i) • commCoord j i) *
                Multiplicative.ofAdd
                  ((l.map fun i => (coeff a j * coeff b i) • commCoord j i).sum) by rfl,
            map_mul, ofAdd_zmod2_smul, map_pow, hiota_comm, ih]
    have houter : ∀ l : List ℕ,
        iota (Multiplicative.ofAdd
          ((l.map fun j =>
            (coeff a j * coeff b j) • sqCoord j +
              ((List.range j).map fun i =>
                (coeff a j * coeff b i) • commCoord j i).sum).sum)) =
          (l.map fun j =>
            (lift j ^ 2) ^ (coeff a j * coeff b j).val *
              ((List.range j).map fun i =>
                ⁅lift j, lift i⁆ ^ (coeff a j * coeff b i).val).prod).prod := by
      intro l
      induction l with
      | nil => simp
      | cons j l ih =>
          simp only [List.map_cons, List.sum_cons, List.prod_cons]
          rw [show Multiplicative.ofAdd
                (((coeff a j * coeff b j) • sqCoord j +
                    ((List.range j).map fun i =>
                      (coeff a j * coeff b i) • commCoord j i).sum) +
                  (l.map fun j =>
                    (coeff a j * coeff b j) • sqCoord j +
                      ((List.range j).map fun i =>
                        (coeff a j * coeff b i) • commCoord j i).sum).sum) =
              (Multiplicative.ofAdd ((coeff a j * coeff b j) • sqCoord j) *
                Multiplicative.ofAdd
                  (((List.range j).map fun i =>
                    (coeff a j * coeff b i) • commCoord j i).sum)) *
                Multiplicative.ofAdd
                  ((l.map fun j =>
                    (coeff a j * coeff b j) • sqCoord j +
                      ((List.range j).map fun i =>
                        (coeff a j * coeff b i) • commCoord j i).sum).sum) by rfl,
            map_mul, map_mul, ofAdd_zmod2_smul, map_pow, hiota_sq,
            hcomm_list, ih]
    exact houter (List.range d)
  have hsec_mul (a b : V) :
      sec a * sec b =
        sec (a + b) * iota (Multiplicative.ofAdd (cocycle a b)) := by
    have h := word_mul_word lift (coeff a) (coeff b)
      hsq_center hcomm_center d
    change word lift (coeff a) d * word lift (coeff b) d =
      word lift (coeff (a + b)) d *
        iota (Multiplicative.ofAdd (cocycle a b))
    rw [hcoeff_add, hiota_cocycle]
    exact h
  have hcocycle_diag (a : V) : cocycle a a = q a := by
    apply hiota
    have haa : a + a = 0 := by
      rw [← two_nsmul]
      exact ZModModule.char_nsmul_eq_zero 2 a
    calc
      iota (Multiplicative.ofAdd (cocycle a a)) = sec a ^ 2 := by
        have h := hsec_mul a a
        rw [haa, hsec_zero, one_mul] at h
        simpa [pow_two] using h.symm
      _ = iota (Multiplicative.ofAdd (q (pi (sec a)).toAdd)) :=
        (hsquare (sec a)).symm
      _ = iota (Multiplicative.ofAdd (q a)) := by
        rw [hpi_sec]
        rfl
  let pairLift : V → W → P := fun a z =>
    sec a * iota (Multiplicative.ofAdd z)
  have hpair_zero : pairLift 0 0 = 1 := by
    simp [pairLift, hsec_zero]
  have hpair_surj (x : P) : ∃ a z, x = pairLift a z := by
    let a : V := (pi x).toAdd
    have hker : (sec a)⁻¹ * x ∈ pi.ker := by
      change pi ((sec a)⁻¹ * x) = 1
      rw [map_mul, map_inv, hpi_sec]
      simp [a]
    have hrange : (sec a)⁻¹ * x ∈ iota.range := by simpa [hexact] using hker
    rcases hrange with ⟨z, hz⟩
    refine ⟨a, z.toAdd, ?_⟩
    change x = sec a * iota (Multiplicative.ofAdd z.toAdd)
    rw [show Multiplicative.ofAdd z.toAdd = z by rfl, hz]
    group
  have hpair_inj (a : V) (z : W) (b : V) (w : W)
      (h : pairLift a z = pairLift b w) : a = b ∧ z = w := by
    have hab : a = b := by
      have hpi_eq := congrArg pi h
      simpa [pairLift, hpi_sec, hpi_iota] using
        congrArg Multiplicative.toAdd hpi_eq
    subst b
    refine ⟨rfl, ?_⟩
    apply Multiplicative.ofAdd.injective
    apply hiota
    exact mul_left_cancel h
  have hpair_mul (a : V) (z : W) (b : V) (w : W) :
      pairLift a z * pairLift b w =
        pairLift (a + b) (z + w + cocycle a b) := by
    have hz_center : iota (Multiplicative.ofAdd z) ∈ Subgroup.center P :=
      hcentral ⟨Multiplicative.ofAdd z, rfl⟩
    have hc_center : iota (Multiplicative.ofAdd (cocycle a b)) ∈
        Subgroup.center P :=
      hcentral ⟨Multiplicative.ofAdd (cocycle a b), rfl⟩
    have hcenter_sum :
        iota (Multiplicative.ofAdd (cocycle a b)) *
            (iota (Multiplicative.ofAdd z) * iota (Multiplicative.ofAdd w)) =
          iota (Multiplicative.ofAdd (z + w + cocycle a b)) := by
      rw [show Multiplicative.ofAdd (z + w + cocycle a b) =
          (Multiplicative.ofAdd z * Multiplicative.ofAdd w) *
            Multiplicative.ofAdd (cocycle a b) by rfl,
        map_mul, map_mul]
      exact (Subgroup.mem_center_iff.mp hc_center _).symm
    change (sec a * iota (Multiplicative.ofAdd z)) *
        (sec b * iota (Multiplicative.ofAdd w)) =
      sec (a + b) * iota (Multiplicative.ofAdd (z + w + cocycle a b))
    calc
      (sec a * iota (Multiplicative.ofAdd z)) *
          (sec b * iota (Multiplicative.ofAdd w)) =
        (sec a * sec b) *
          (iota (Multiplicative.ofAdd z) * iota (Multiplicative.ofAdd w)) := by
            simp only [mul_assoc]
            rw [← mul_assoc (iota (Multiplicative.ofAdd z))]
            rw [(Subgroup.mem_center_iff.mp hz_center (sec b)).symm]
            simp only [mul_assoc]
      _ = (sec (a + b) * iota (Multiplicative.ofAdd (cocycle a b))) *
          (iota (Multiplicative.ofAdd z) * iota (Multiplicative.ofAdd w)) := by
            rw [hsec_mul]
      _ = sec (a + b) *
          iota (Multiplicative.ofAdd (z + w + cocycle a b)) := by
            simpa only [mul_assoc] using
              congrArg (fun t => sec (a + b) * t) hcenter_sum
  have hpair_pi (a : V) (z : W) :
      pi (pairLift a z) = Multiplicative.ofAdd a := by
    simp [pairLift, hpi_sec, hpi_iota]
  have hpair_center (z : W) :
      pairLift 0 z = iota (Multiplicative.ofAdd z) := by
    simp [pairLift, hsec_zero]
  exact ⟨pairLift, cocycle, hcocycle_add_left, hcocycle_add_right,
    hcocycle_diag, hpair_zero, hpair_surj, hpair_inj, hpair_mul,
    hpair_pi, hpair_center⟩

/-- Central-extension coordinates can be normalized to any prescribed
bilinear multiplication defect with the correct diagonal square map. -/
public theorem exists_coordinates_with_prescribed_bilinear_defect
    {V W P : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    [Group P]
    (iota : Multiplicative W →* P) (pi : P →* Multiplicative V)
    (hiota : Function.Injective iota) (hpi : Function.Surjective pi)
    (hexact : iota.range = pi.ker)
    (hcentral : iota.range ≤ Subgroup.center P)
    (q : V → W)
    (hsquare : ∀ x : P,
      iota (Multiplicative.ofAdd (q (pi x).toAdd)) = x ^ 2)
    (target : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (htarget_diag : ∀ a : V, target a a = q a) :
    ∃ pairLift : V → W → P,
      pairLift 0 0 = 1 ∧
      (∀ x : P, ∃ a z, x = pairLift a z) ∧
      (∀ a z b w, pairLift a z = pairLift b w → a = b ∧ z = w) ∧
      ∀ a z b w,
        pairLift a z * pairLift b w =
          pairLift (a + b) (z + w + target a b) := by
  classical
  obtain ⟨pairLift0, cocycle, hcocycle_left, hcocycle_right,
      hcocycle_diag, hpair_zero, hpair_surj, hpair_inj, hpair_mul,
      _hpair_pi, _hpair_center⟩ :=
    exists_bilinear_coordinates_of_central_extension
      iota pi hiota hpi hexact hcentral q hsquare
  have hcocycle_zero_left (b : V) : cocycle 0 b = 0 := by
    have h := hcocycle_left 0 0 b
    simp only [zero_add] at h
    apply add_left_cancel (a := cocycle 0 b)
    simpa using h.symm
  have hcocycle_zero_right (a : V) : cocycle a 0 = 0 := by
    have h := hcocycle_right a 0 0
    simp only [zero_add] at h
    apply add_left_cancel (a := cocycle a 0)
    simpa using h.symm
  let cocycleL : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W :=
    { toFun := fun a =>
        { toFun := fun b => cocycle a b
          map_add' := hcocycle_right a
          map_smul' := by
            intro c b
            have hc : c = 0 ∨ c = 1 := by
              fin_cases c
              · left
                rfl
              · right
                rfl
            rcases hc with rfl | rfl
            · simp [hcocycle_zero_right]
            · simp }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        exact hcocycle_left a b c
      map_smul' := by
        intro c a
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · left
            rfl
          · right
            rfl
        rcases hc with rfl | rfl
        · apply LinearMap.ext
          intro b
          simp [hcocycle_zero_left]
        · simp }
  let D : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W := cocycleL + target
  have hD_self (a : V) : D a a = 0 := by
    change cocycle a a + target a a = 0
    rw [hcocycle_diag, htarget_diag]
    nth_rw 2 [← ZModModule.neg_eq_self (q a)]
    exact add_neg_cancel _
  obtain ⟨f, hf_zero, hf_add⟩ := exists_quadratic_refinement D hD_self
  let pairLift : V → W → P := fun a z => pairLift0 a (z + f a)
  refine ⟨pairLift, ?_, ?_, ?_, ?_⟩
  · simpa [pairLift, hf_zero] using hpair_zero
  · intro x
    obtain ⟨a, z, hx⟩ := hpair_surj x
    refine ⟨a, z - f a, ?_⟩
    simpa [pairLift] using hx
  · intro a z b w hab
    have h := hpair_inj a (z + f a) b (w + f b) hab
    rcases h with ⟨rfl, hzw⟩
    refine ⟨rfl, ?_⟩
    exact add_right_cancel hzw
  · intro a z b w
    rw [show pairLift a z = pairLift0 a (z + f a) by rfl,
      show pairLift b w = pairLift0 b (w + f b) by rfl,
      hpair_mul]
    change pairLift0 (a + b)
        ((z + f a) + (w + f b) + cocycle a b) =
      pairLift0 (a + b) (z + w + target a b + f (a + b))
    congr 1
    rw [hf_add]
    change (z + f a) + (w + f b) + cocycle a b =
      z + w + target a b +
        (f a + f b + (cocycle a b + target a b))
    nth_rw 2 [← ZModModule.neg_eq_self (target a b)]
    abel

end PFAppendixIII
end CFSG.BenderSuzuki
