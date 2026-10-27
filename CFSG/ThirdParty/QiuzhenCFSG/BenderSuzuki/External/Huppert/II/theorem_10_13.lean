module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.NoncommRing

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.10.13

The statement follows Volume I, physical pages 256--257 (PDF pages 267--268).
-/

namespace CFSG.BenderSuzuki
namespace External

open MatrixGroups
open scoped LinearAlgebra.Projectivization
open scoped commutatorElement

universe u

private theorem projectiveSpecialUnitaryMatrixGroup_equiv_of_gram
    {K : Type u} [Field K] {n : ℕ}
    (J J₀ : HermitianForm n K) (P : GL (Fin n) K)
    (hconj : J₀.conj = J.conj)
    (hgram : J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
      (P : Matrix (Fin n) (Fin n) K) = J₀.form) :
    Nonempty
      (ProjectiveSpecialUnitaryMatrixGroup J ≃*
        ProjectiveSpecialUnitaryMatrixGroup J₀) := by
  classical
  let eGL : GL (Fin n) K ≃* GL (Fin n) K := MulAut.conj P⁻¹
  let ePGL : Matrix.ProjGenLinGroup (Fin n) K ≃*
      Matrix.ProjGenLinGroup (Fin n) K :=
    MulAut.conj (Matrix.ProjGenLinGroup.mk P⁻¹)
  have hadj_mul (A B : Matrix (Fin n) (Fin n) K) :
      J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
    ext i j
    simp only [HermitianForm.conjTranspose, Matrix.mul_apply, map_sum, map_mul]
    apply Finset.sum_bij (fun k _ => k) <;> simp [mul_comm]
  have hadj_one :
      J.conjTranspose (1 : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [HermitianForm.conjTranspose]
    · have hji : j ≠ i := fun hji => hij hji.symm
      simp [HermitianForm.conjTranspose, hij, hji]
  have hP_inv_mul :
      ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (P : Matrix (Fin n) (Fin n) K) = 1 := by
    exact congrArg
      (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K))
      (inv_mul_cancel P)
  have hP_mul_inv :
      (P : Matrix (Fin n) (Fin n) K) *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    exact congrArg
      (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K))
      (mul_inv_cancel P)
  have hadj_inv_mul :
      J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          J.conjTranspose (P : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← hadj_mul, hP_mul_inv, hadj_one]
  have hadj_mul_inv :
      J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
          J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← hadj_mul, hP_inv_mul, hadj_one]
  have hgram_inv :
      J.conjTranspose ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          J₀.form *
          ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = J.form := by
    calc
      J.conjTranspose
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          J₀.form *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        J.conjTranspose
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
              (P : Matrix (Fin n) (Fin n) K)) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hgram]
      _ = (J.conjTranspose
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) * J.form *
          ((P : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        noncomm_ring
      _ = J.form := by rw [hadj_inv_mul, hP_mul_inv]; simp
  have hJ₀adj (A : Matrix (Fin n) (Fin n) K) :
      J₀.conjTranspose A = J.conjTranspose A := by
    ext i j
    simp [HermitianForm.conjTranspose, hconj]
  have hforward (A : GL (Fin n) K) (hA : A ∈ J.specialSubgroup) :
      P⁻¹ * A * P ∈ J₀.specialSubgroup := by
    rw [J₀.mem_specialSubgroup_iff]
    constructor
    · have hAunit := (J.mem_specialSubgroup_iff A).mp hA |>.1
      change J₀.conjTranspose
          (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) *
            (P : Matrix (Fin n) (Fin n) K)) * J₀.form *
          (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) *
            (P : Matrix (Fin n) (Fin n) K)) = J₀.form
      rw [hJ₀adj, hadj_mul, hadj_mul]
      calc
        J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose
                  ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            J₀.form *
            (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K) *
              (P : Matrix (Fin n) (Fin n) K)) =
          J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose
                  ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) * J.form *
              (P : Matrix (Fin n) (Fin n) K)) *
            (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K) *
              (P : Matrix (Fin n) (Fin n) K)) := by rw [hgram]
        _ = J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose
                  ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) * J.form *
              ((P : Matrix (Fin n) (Fin n) K) *
                ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              (A : Matrix (Fin n) (Fin n) K) *
              (P : Matrix (Fin n) (Fin n) K) := by
          noncomm_ring
        _ = J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) * J.form *
                (A : Matrix (Fin n) (Fin n) K)) *
              (P : Matrix (Fin n) (Fin n) K) := by
          rw [hadj_inv_mul, hP_mul_inv]
          simp only [mul_one]
          noncomm_ring
        _ = J₀.form := by rw [hAunit, hgram]
    · have hAdet := (J.mem_specialSubgroup_iff A).mp hA |>.2
      change Matrix.GeneralLinearGroup.det (P⁻¹ * A * P) = 1
      simp [hAdet]
  have hbackward (A : GL (Fin n) K) (hA : A ∈ J₀.specialSubgroup) :
      P * A * P⁻¹ ∈ J.specialSubgroup := by
    rw [J.mem_specialSubgroup_iff]
    constructor
    · have hAunit := (J₀.mem_specialSubgroup_iff A).mp hA |>.1
      rw [hJ₀adj] at hAunit
      change J.conjTranspose
          ((P : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * J.form *
          ((P : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = J.form
      rw [hadj_mul, hadj_mul]
      calc
        J.conjTranspose
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) * J.form *
            ((P : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K) *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
          J.conjTranspose
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose (P : Matrix (Fin n) (Fin n) K)) *
            (J.conjTranspose
                ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              J₀.form *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
            ((P : Matrix (Fin n) (Fin n) K) *
              (A : Matrix (Fin n) (Fin n) K) *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [hgram_inv]
        _ = J.conjTranspose
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              J.conjTranspose (A : Matrix (Fin n) (Fin n) K) *
              (J.conjTranspose (P : Matrix (Fin n) (Fin n) K) *
                J.conjTranspose
                  ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
              J₀.form *
              (((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                (P : Matrix (Fin n) (Fin n) K)) *
              (A : Matrix (Fin n) (Fin n) K) *
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          noncomm_ring
        _ = J.conjTranspose
              ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (J.conjTranspose (A : Matrix (Fin n) (Fin n) K) * J₀.form *
              (A : Matrix (Fin n) (Fin n) K)) *
            ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hadj_mul_inv, hP_inv_mul]
          simp only [mul_one]
          noncomm_ring
        _ = J.form := by rw [hAunit, hgram_inv]
    · have hAdet := (J₀.mem_specialSubgroup_iff A).mp hA |>.2
      change Matrix.GeneralLinearGroup.det (P * A * P⁻¹) = 1
      simp [hAdet]
  have hspecial :
      J.specialSubgroup.map eGL.toMonoidHom = J₀.specialSubgroup := by
    ext A
    rw [Subgroup.mem_map_equiv]
    constructor
    · intro hA
      have := hforward (eGL.symm A) hA
      have heq : P⁻¹ * eGL.symm A * P = A := by
        change eGL (eGL.symm A) = A
        exact eGL.apply_symm_apply A
      rw [← heq]
      exact this
    · intro hA
      simpa [eGL, Matrix.mul_assoc] using hbackward A hA
  have he_comm (A : GL (Fin n) K) :
      ePGL (Matrix.ProjGenLinGroup.mk A) =
        Matrix.ProjGenLinGroup.mk (eGL A) := by
    simp [ePGL, eGL]
  have hcomp :
      ePGL.toMonoidHom.comp Matrix.ProjGenLinGroup.mk =
        Matrix.ProjGenLinGroup.mk.comp eGL.toMonoidHom := by
    ext A
    exact he_comm A
  have hprojective :
      (J.specialSubgroup.map Matrix.ProjGenLinGroup.mk).map ePGL.toMonoidHom =
        J₀.specialSubgroup.map Matrix.ProjGenLinGroup.mk := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hspecial]
  exact ⟨(ePGL.subgroupMap
      (J.specialSubgroup.map Matrix.ProjGenLinGroup.mk)).trans
    (MulEquiv.subgroupCongr hprojective)⟩

private theorem hermitian_exists_torus_scale_ne_one
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (q : ℕ) (hq : 2 < q)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    ∃ k : Kˣ, (k : K) * (J.conj (k : K))⁻¹ ^ 2 ≠ 1 := by
  obtain ⟨k, hkorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcardUnits : Nat.card Kˣ = q ^ 2 - 1 := by
    rw [Nat.card_units, hKcard]
  rw [hcardUnits] at hkorder
  have hkpow : k ^ (2 * q - 1) ≠ 1 := by
    intro hp
    have hdvd := orderOf_dvd_of_pow_eq_one hp
    rw [hkorder] at hdvd
    have hle : q ^ 2 - 1 ≤ 2 * q - 1 :=
      Nat.le_of_dvd (by omega) hdvd
    have hle' : q ^ 2 ≤ 2 * q :=
      (Nat.sub_le_sub_iff_right (by omega : 1 ≤ 2 * q)).mp hle
    have hlt : 2 * q < q ^ 2 := by
      simpa [pow_two] using
        (Nat.mul_lt_mul_right (by omega : 0 < q)).mpr hq
    exact (Nat.not_lt_of_ge hle') hlt
  refine ⟨k, ?_⟩
  intro hs
  apply hkpow
  apply Units.ext
  have hkne : (k : K) ≠ 0 := Units.ne_zero k
  have hconj := huppert_II_10_4_conj_eq_frobenius
    J q hKcard hfixed_card (k : K)
  rw [hconj] at hs
  have hkt : (k : K) = ((k : K) ^ q) ^ 2 := by
    calc
      (k : K) =
          ((k : K) * (((k : K) ^ q)⁻¹ ^ 2)) * ((k : K) ^ q) ^ 2 := by
            field_simp
      _ = ((k : K) ^ q) ^ 2 := by rw [hs, one_mul]
  change (k : K) ^ (2 * q - 1) = 1
  apply mul_right_cancel₀ hkne
  calc
    (k : K) ^ (2 * q - 1) * (k : K) =
        (k : K) ^ ((2 * q - 1) + 1) := (pow_succ _ _).symm
    _ = (k : K) ^ (2 * q) := by
      rw [show (2 * q - 1) + 1 = 2 * q by omega]
    _ = ((k : K) ^ q) ^ 2 := by
      simpa [Nat.mul_comm] using pow_mul (k : K) q 2
    _ = (k : K) := hkt.symm
    _ = 1 * (k : K) := by rw [one_mul]

set_option maxHeartbeats 800000 in
/-- Huppert II.10.13: `PSU(3,q^2)` is simple for `q > 2`. -/
public theorem huppert_II_10_13
    {K : Type u} [Field K] [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hq : 2 < q)
    (hKcard : Nat.card K = q ^ 2)
    (hfixed_card : Nat.card {x : K // J.conj x = x} = q) :
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  have hstandard_basis :=
    huppert_II_10_4_b_standard_hermitian_basis J q hKcard hfixed_card
  have hcoordinate_transport :
      ∃ J₀ : HermitianForm 3 K,
        J₀.conj = J.conj ∧
        J₀.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
        Nonempty
          (ProjectiveSpecialUnitaryMatrixGroup J ≃*
            ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    rcases hstandard_basis with ⟨P, hP⟩
    let J₀ : HermitianForm 3 K :=
      { conj := J.conj
        conj_involutive := J.conj_involutive
        form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
        form_hermitian := by
          intro i j
          fin_cases i <;> fin_cases j <;> simp
        form_nondegenerate := by
          simp [Matrix.det_fin_three] }
    refine ⟨J₀, rfl, rfl, ?_⟩
    exact projectiveSpecialUnitaryMatrixGroup_equiv_of_gram J J₀ P rfl hP
  rcases hcoordinate_transport with ⟨J₀, hJ₀conj, hJ₀standard, hequiv⟩
  have hfixed_card₀ : Nat.card {x : K // J₀.conj x = x} = q := by
    simpa only [hJ₀conj] using hfixed_card
  have h1012 :=
    huppert_II_10_12 J₀ q hKcard hfixed_card₀ hJ₀standard
  rcases h1012 with
    ⟨hOmega_card, rho, pinf, hrho, hrho_apply, hstabilizer_data⟩
  dsimp only at hstabilizer_data
  rcases hstabilizer_data with
    ⟨hUcard, hRH, htwo_transitive, hGcard, hthree_fixed⟩
  rcases hRH with
    ⟨R, H, hRle, hHle, hRnormal, hRinfH, hRsupH, hHcyclic,
      hRcard, hRcomm, hRcomm_card, hHcard, hRregular,
      hRcoordinates, hHcoordinates, hHcoordinates_surjective⟩
  let P := ℙ K (Fin 3 → K)
  let A : Set P :=
    {x | ∃ (v : Fin 3 → K) (hv : v ≠ 0),
      x = Projectivization.mk K v hv ∧
        dotProduct (fun i => J₀.conj (v i)) (J₀.form.mulVec v) = 0}
  let Omega := {x : P // x ∈ A}
  let G := ProjectiveSpecialUnitaryMatrixGroup J₀
  let U : Subgroup G :=
    (MulAction.stabilizer (Equiv.Perm Omega) pinf).comap rho
  have hstabilizer_commutator_le :
      (commutator U).map U.subtype ≤ R := by
    let RU : Subgroup U := R.subgroupOf U
    let HU : Subgroup U := H.subgroupOf U
    letI : RU.Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hRnormal
    letI : IsCyclic H := hHcyclic
    letI : IsMulCommutative H := IsCyclic.isMulCommutative
    have hHUcomm : IsMulCommutative HU := by
      refine ⟨⟨?_⟩⟩
      intro x y
      let xH : H := ⟨((x : U) : G), x.property⟩
      let yH : H := ⟨((y : U) : G), y.property⟩
      have hcomm : xH * yH = yH * xH :=
        (IsMulCommutative.is_comm (M := H)).comm _ _
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : H => (z : G)) hcomm
    have hsup : RU ⊔ HU = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (A := R) (A' := H) (B := U) hRle hHle]
      rw [hRsupH, Subgroup.subgroupOf_self]
    have hcommU : commutator U ≤ RU :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hHUcomm
    rintro x ⟨y, hy, rfl⟩
    exact hcommU hy
  have hstabilizer_commutator_ge :
      R ≤ (commutator U).map U.subtype := by
    rcases hRcoordinates with ⟨coordR, hcoordRMatrix⟩
    let rootPSU := hermitianUnipotentPSU J₀ hJ₀standard
    have hcoordR_eq_root (z : hermitianUnipotentCoord J₀) :
        ((coordR z : R) : G) = rootPSU z := by
      rcases hcoordRMatrix z with ⟨M, hM, hMproj⟩
      have hMroot : M = hermitianUnipotentGL J₀ z := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (M : Matrix (Fin 3) (Fin 3) K) i j =
          (hermitianUnipotentGL J₀ z : Matrix (Fin 3) (Fin 3) K) i j
        rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
      apply Subtype.ext
      calc
        (((coordR z : R) : G) : Matrix.ProjGenLinGroup (Fin 3) K) =
            Matrix.ProjGenLinGroup.mk M := hMproj
        _ = Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ z) := by
          rw [hMroot]
        _ = (rootPSU z : Matrix.ProjGenLinGroup (Fin 3) K) := by
          rw [hermitianUnipotentPSU_val]
    let coordRMul : hermitianUnipotentCoord J₀ ≃* R :=
      { coordR with
        map_mul' := by
          intro z w
          apply Subtype.ext
          calc
            ((coordR (z * w) : R) : G) = rootPSU (z * w) :=
              hcoordR_eq_root (z * w)
            _ = rootPSU z * rootPSU w := map_mul rootPSU z w
            _ = ((coordR z : R) : G) * ((coordR w : R) : G) := by
              rw [hcoordR_eq_root, hcoordR_eq_root] }
    have hcoordinate_commutator_core :
        R ≤ (commutator U).map U.subtype := by
      have hroot_injective : Function.Injective rootPSU := by
        intro z w hzw
        apply coordRMul.injective
        apply Subtype.ext
        exact (hcoordR_eq_root z).trans (hzw.trans (hcoordR_eq_root w).symm)
      obtain ⟨k, hk⟩ :=
        hermitian_exists_torus_scale_ne_one J₀ q hq hKcard hfixed_card₀
      let scale : K := (k : K) * (J₀.conj (k : K))⁻¹ ^ 2
      have hscale : scale ≠ 1 := by
        exact hk
      obtain ⟨h, M, hM, hMproj⟩ := hHcoordinates_surjective k
      have hMtorus : M = hermitianTorusGL J₀ k := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (M : Matrix (Fin 3) (Fin 3) K) i j =
          (hermitianTorusGL J₀ k : Matrix (Fin 3) (Fin 3) K) i j
        rw [hM, hermitianTorusGL_val]
        rfl
      have hh_torus : (h : G) = hermitianTorusPSU J₀ hJ₀standard k := by
        apply Subtype.ext
        rw [hMproj, hermitianTorusPSU_val, hMtorus]
      intro r hr
      let z := coordRMul.symm ⟨r, hr⟩
      let a : K := z.1.1 / (1 - scale)
      have ha_fixed :
          J₀.conj (-(a * J₀.conj a)) = -(a * J₀.conj a) := by
        rw [map_neg, map_mul, J₀.conj_involutive]
        ring
      obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective
        J₀ q hKcard hfixed_card₀ (-(a * J₀.conj a)) ha_fixed
      let w : hermitianUnipotentCoord J₀ :=
        ⟨(a, b), by linear_combination hb⟩
      let rwR : R := coordRMul w
      let rwU : U := ⟨(rwR : G), hRle rwR.property⟩
      let hU : U := ⟨(h : G), hHle h.property⟩
      have hrwU : (rwU : G) = rootPSU w := by
        exact hcoordR_eq_root w
      have hhU : (hU : G) = hermitianTorusPSU J₀ hJ₀standard k := by
        exact hh_torus
      have hcU : ⁅rwU, hU⁆ ∈ commutator U :=
        Subgroup.commutator_mem_commutator (by simp) (by simp)
      have hcMap :
          ((⁅rwU, hU⁆ : U) : G) ∈ (commutator U).map U.subtype :=
        ⟨⁅rwU, hU⁆, hcU, rfl⟩
      let cR : R :=
        ⟨((⁅rwU, hU⁆ : U) : G), hstabilizer_commutator_le hcMap⟩
      let c := coordRMul.symm cR
      have hc_eq : c = w * hermitianTorusAction J₀ k w⁻¹ := by
        apply hroot_injective
        calc
          rootPSU c = (cR : G) := by
            rw [← hcoordR_eq_root]
            change ((coordRMul (coordRMul.symm cR) : R) : G) = (cR : G)
            rw [coordRMul.apply_symm_apply]
          _ = ((⁅rwU, hU⁆ : U) : G) := rfl
          _ = rootPSU (w * hermitianTorusAction J₀ k w⁻¹) := by
            rw [map_mul]
            change ⁅(rwU : G), (hU : G)⁆ =
              rootPSU w * rootPSU (hermitianTorusAction J₀ k w⁻¹)
            rw [hrwU, hhU, commutatorElement_def]
            calc
          rootPSU w * hermitianTorusPSU J₀ hJ₀standard k *
                (rootPSU w)⁻¹ *
              (hermitianTorusPSU J₀ hJ₀standard k)⁻¹ =
            rootPSU w *
              (hermitianTorusPSU J₀ hJ₀standard k * (rootPSU w)⁻¹) *
              (hermitianTorusPSU J₀ hJ₀standard k)⁻¹ := by group
          _ = rootPSU w *
              (rootPSU (hermitianTorusAction J₀ k w⁻¹) *
                hermitianTorusPSU J₀ hJ₀standard k) *
              (hermitianTorusPSU J₀ hJ₀standard k)⁻¹ := by
                rw [← map_inv, hermitianTorusPSU_mul_unipotent]
              _ = rootPSU w *
                  rootPSU (hermitianTorusAction J₀ k w⁻¹) := by group
      have hc_fst : c.1.1 = z.1.1 := by
        rw [hc_eq]
        change
          (hermitianUnipotentMul J₀ w
            (hermitianTorusAction J₀ k (hermitianUnipotentInv J₀ w))).1.1 =
              z.1.1
        have hfst_formula :
            (hermitianUnipotentMul J₀ w
              (hermitianTorusAction J₀ k
                (hermitianUnipotentInv J₀ w))).1.1 =
              a + (-a) * scale := by
          simp [hermitianUnipotentMul, hermitianUnipotentInv,
            hermitianTorusAction_fst, w, scale, mul_assoc]
        rw [hfst_formula]
        dsimp [a]
        have hden : 1 - scale ≠ 0 := sub_ne_zero.mpr hscale.symm
        field_simp [hden]
        ring
      let d := z * c⁻¹
      have hd_fst : d.1.1 = 0 := by
        change z.1.1 + -c.1.1 = 0
        rw [hc_fst]
        ring
      have hd_center_coord :
          d ∈ Subgroup.center (hermitianUnipotentCoord J₀) := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        apply Prod.ext
        · change x.1.1 + d.1.1 = d.1.1 + x.1.1
          exact add_comm _ _
        · change x.1.2 + d.1.2 - x.1.1 * J₀.conj d.1.1 =
            d.1.2 + x.1.2 - d.1.1 * J₀.conj x.1.1
          rw [hd_fst, map_zero, mul_zero, zero_mul, sub_zero, sub_zero,
            add_comm]
      have hd_center_R : coordRMul d ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨xcoord, rfl⟩ := coordRMul.surjective x
        simpa only [map_mul] using congrArg coordRMul
          ((Subgroup.mem_center_iff.mp hd_center_coord) xcoord)
      have hd_comm_R : coordRMul d ∈ commutator R := by
        rw [hRcomm]
        exact hd_center_R
      let inclRU : R →* U :=
        R.subtype.codRestrict U (fun x => hRle x.property)
      have hd_comm_U : inclRU (coordRMul d) ∈ commutator U := by
        apply map_derivedSeries_le_derivedSeries inclRU 1
        exact ⟨coordRMul d, hd_comm_R, rfl⟩
      have hdMap :
          ((coordRMul d : R) : G) ∈ (commutator U).map U.subtype := by
        exact ⟨inclRU (coordRMul d), hd_comm_U, rfl⟩
      have hprod := ((commutator U).map U.subtype).mul_mem hdMap hcMap
      convert hprod using 1
      change r = ((coordRMul d : R) : G) * ((⁅rwU, hU⁆ : U) : G)
      calc
        r = ((coordRMul z : R) : G) := by
          change r = ((coordRMul (coordRMul.symm ⟨r, hr⟩) : R) : G)
          rw [coordRMul.apply_symm_apply]
        _ = ((coordRMul d : R) : G) * ((coordRMul c : R) : G) := by
          have hdc : z = d * c := by
            dsimp [d]
            group
          calc
            ((coordRMul z : R) : G) =
                (((coordRMul d * coordRMul c : R)) : G) := by
              apply congrArg (fun x : R => (x : G))
              rw [hdc, map_mul]
            _ = ((coordRMul d : R) : G) * ((coordRMul c : R) : G) :=
              map_mul R.subtype _ _
        _ = ((coordRMul d : R) : G) * ((⁅rwU, hU⁆ : U) : G) := by
          congr 1
          change ((coordRMul c : R) : G) = (cR : G)
          rw [coordRMul.apply_symm_apply]
    exact hcoordinate_commutator_core
  have hstabilizer_commutator :
      (commutator U).map U.subtype = R :=
    le_antisymm hstabilizer_commutator_le hstabilizer_commutator_ge
  have htorus_le_commutator : H ≤ commutator G := by
    rcases hRcoordinates with ⟨coordR, hcoordRMatrix⟩
    let rootPSU := hermitianUnipotentPSU J₀ hJ₀standard
    let torusPSU := hermitianTorusPSU J₀ hJ₀standard
    let weyl : G := hermitianWeylPSU J₀ hJ₀standard
    have hcoordR_eq_root (z : hermitianUnipotentCoord J₀) :
        ((coordR z : R) : G) = rootPSU z := by
      rcases hcoordRMatrix z with ⟨M, hM, hMproj⟩
      have hMroot : M = hermitianUnipotentGL J₀ z := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        change (M : Matrix (Fin 3) (Fin 3) K) i j =
          (hermitianUnipotentGL J₀ z : Matrix (Fin 3) (Fin 3) K) i j
        rw [hM, hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq]
      apply Subtype.ext
      calc
        (((coordR z : R) : G) : Matrix.ProjGenLinGroup (Fin 3) K) =
            Matrix.ProjGenLinGroup.mk M := hMproj
        _ = Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ z) := by
          rw [hMroot]
        _ = (rootPSU z : Matrix.ProjGenLinGroup (Fin 3) K) := by
          rw [hermitianUnipotentPSU_val]
    have hR_le_commutator : R ≤ commutator G := by
      intro r hr
      apply (show (commutator U).map U.subtype ≤ commutator G by
        rw [Subgroup.map_subtype_commutator]
        exact Subgroup.commutator_mono le_top le_top)
      rw [hstabilizer_commutator]
      exact hr
    have hroot_mem (z : hermitianUnipotentCoord J₀) :
        rootPSU z ∈ commutator G := by
      rw [← hcoordR_eq_root]
      exact hR_le_commutator (coordR z).property
    have hweyl_sq : weyl * weyl = 1 := by
      apply Subtype.ext
      change Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
          Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) = 1
      rw [← map_mul]
      have hGL :
          hermitianWeylGL (K := K) * hermitianWeylGL (K := K) = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply,
            Fin.sum_univ_three]
      rw [hGL, map_one]
    have hweyl_inv : weyl⁻¹ = weyl := by
      calc
        weyl⁻¹ = weyl⁻¹ * (weyl * weyl) := by rw [hweyl_sq, mul_one]
        _ = weyl := by group
    have hroot_weyl_conj_mem (z : hermitianUnipotentCoord J₀) :
        weyl * rootPSU z * weyl ∈ commutator G := by
      have hconj :=
        (inferInstance : (commutator G).Normal).conj_mem
          (rootPSU z) (hroot_mem z) weyl
      simpa only [hweyl_inv] using hconj
    have htorus_weyl_mem (k : Kˣ) :
        torusPSU k * weyl ∈ commutator G := by
      have hk0 : (k : K) ≠ 0 := Units.ne_zero k
      have hconjk0 : J₀.conj (k : K) ≠ 0 :=
        (map_ne_zero J₀.conj).2 hk0
      let target : K := -((k : K) + J₀.conj (k : K))
      have htarget_fixed : J₀.conj target = target := by
        dsimp [target]
        rw [map_neg, map_add, J₀.conj_involutive]
        ring
      obtain ⟨a, ha⟩ : ∃ a : K, a * J₀.conj a = target := by
        by_cases htarget0 : target = 0
        · exact ⟨0, by simp [htarget0]⟩
        · obtain ⟨a, ha0, ha⟩ :=
            huppert_II_10_4_norm_surjective
              J₀ q hKcard hfixed_card₀ target htarget_fixed htarget0
          exact ⟨a, ha⟩
      have hparam : (k : K) + J₀.conj (k : K) + a * J₀.conj a = 0 := by
        dsimp [target] at ha
        linear_combination ha
      let z : hermitianUnipotentCoord J₀ := ⟨(a, (k : K)), hparam⟩
      let zL : hermitianUnipotentCoord J₀ :=
        ⟨(-a / J₀.conj (k : K), (k : K)⁻¹), by
          dsimp only
          rw [map_inv₀, map_div₀, map_neg, J₀.conj_involutive]
          field_simp [hk0, hconjk0]
          linear_combination hparam⟩
      let zR : hermitianUnipotentCoord J₀ :=
        ⟨(-a / (k : K), (k : K)⁻¹), by
          dsimp only
          rw [map_inv₀, map_div₀, map_neg]
          field_simp [hk0, hconjk0]
          linear_combination hparam⟩
      have hbruhat :
          weyl * rootPSU z * weyl =
            rootPSU zL * torusPSU k * weyl * rootPSU zR := by
        have hGL :
            hermitianWeylGL (K := K) * hermitianUnipotentGL J₀ z *
                hermitianWeylGL (K := K) =
              hermitianUnipotentGL J₀ zL * hermitianTorusGL J₀ k *
                hermitianWeylGL (K := K) * hermitianUnipotentGL J₀ zR := by
          apply Matrix.GeneralLinearGroup.ext
          intro i j
          change
            ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
                hermitianUnipotentMatrix J₀ z *
                (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K)) i j =
              (hermitianUnipotentMatrix J₀ zL *
                hermitianTorusMatrix J₀ k *
                (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
                hermitianUnipotentMatrix J₀ zR) i j
          fin_cases i <;> fin_cases j <;>
            simp [hermitianWeylMatrix, hermitianUnipotentMatrix,
              hermitianTorusMatrix, Matrix.mul_apply, Fin.sum_univ_three,
              z, zL, zR]
          all_goals field_simp [hk0, hconjk0]
          all_goals try rw [J₀.conj_involutive]
          all_goals try linear_combination (k : K) * hparam
          all_goals ring_nf
          exact hparam.symm
        apply Subtype.ext
        change
          Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
                Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ z) *
                Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) =
            Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ zL) *
                Matrix.ProjGenLinGroup.mk (hermitianTorusGL J₀ k) *
                Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
                Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ zR)
        calc
          Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
                  Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ z) *
                  Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) =
              Matrix.ProjGenLinGroup.mk
                (hermitianWeylGL (K := K) *
                  hermitianUnipotentGL J₀ z * hermitianWeylGL (K := K)) := by
                    simp
          _ = Matrix.ProjGenLinGroup.mk
                (hermitianUnipotentGL J₀ zL * hermitianTorusGL J₀ k *
                  hermitianWeylGL (K := K) *
                  hermitianUnipotentGL J₀ zR) := by rw [hGL]
          _ = Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ zL) *
                Matrix.ProjGenLinGroup.mk (hermitianTorusGL J₀ k) *
                Matrix.ProjGenLinGroup.mk (hermitianWeylGL (K := K)) *
                Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J₀ zR) := by
                  simp
      have hmiddle :
          torusPSU k * weyl =
            (rootPSU zL)⁻¹ * (weyl * rootPSU z * weyl) *
              (rootPSU zR)⁻¹ := by
        rw [hbruhat]
        group
      rw [hmiddle]
      exact ((commutator G).mul_mem
        ((commutator G).mul_mem
          ((commutator G).inv_mem (hroot_mem zL))
          (hroot_weyl_conj_mem z))
        ((commutator G).inv_mem (hroot_mem zR)))
    intro h hh
    rcases hHcoordinates ⟨h, hh⟩ with ⟨k, M, hM, hMproj⟩
    have hMtorus : M = hermitianTorusGL J₀ k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change (M : Matrix (Fin 3) (Fin 3) K) i j =
        (hermitianTorusGL J₀ k : Matrix (Fin 3) (Fin 3) K) i j
      rw [hM, hermitianTorusGL_val]
      rfl
    have hh_torus : h = torusPSU k := by
      apply Subtype.ext
      rw [hMproj, hermitianTorusPSU_val, hMtorus]
    rw [hh_torus]
    have hk := htorus_weyl_mem k
    have hone := htorus_weyl_mem (1 : Kˣ)
    have hcancel :
        torusPSU k =
          (torusPSU k * weyl) * (torusPSU (1 : Kˣ) * weyl)⁻¹ := by
      rw [map_one, one_mul, hweyl_inv]
      calc
        torusPSU k = torusPSU k * 1 := by rw [mul_one]
        _ = torusPSU k * (weyl * weyl) := by rw [hweyl_sq]
        _ = torusPSU k * weyl * weyl := by rw [mul_assoc]
    rw [hcancel]
    exact (commutator G).mul_mem hk ((commutator G).inv_mem hone)
  have hperfect : commutator G = ⊤ := by
    letI : MulAction G Omega := MulAction.compHom Omega rho
    have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      exact htwo_transitive a b c d hab hcd
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    letI : MulAction.IsPreprimitive G Omega :=
      MulAction.isPreprimitive_of_is_two_pretransitive htwo
    have hOmega_one_lt : 1 < Nat.card Omega := by
      rw [hOmega_card]
      have hq_pos : 0 < q := by omega
      simpa using Nat.add_lt_add_right (pow_pos hq_pos 3) 1
    letI : Nontrivial Omega :=
      Finite.one_lt_card_iff_nontrivial.mp hOmega_one_lt
    letI : FaithfulSMul G Omega := faithfulSMul_iff.mpr (by
      intro g hg
      apply hrho
      apply Equiv.ext
      intro x
      have hx := hg x
      change rho g • x = x at hx
      rw [Equiv.Perm.smul_def] at hx
      calc
        (rho g) x = x := hx
        _ = (rho 1) x := by rw [map_one]; rfl)
    have hR_le_commutator : R ≤ commutator G := by
      intro r hr
      apply (show (commutator U).map U.subtype ≤ commutator G by
        rw [Subgroup.map_subtype_commutator]
        exact Subgroup.commutator_mono le_top le_top)
      rw [hstabilizer_commutator]
      exact hr
    have hU_le_commutator : U ≤ commutator G := by
      have hsup_le : R ⊔ H ≤ commutator G :=
        sup_le hR_le_commutator htorus_le_commutator
      intro x hx
      apply hsup_le
      rw [hRsupH]
      exact hx
    have hUeq : U = MulAction.stabilizer G pinf := rfl
    have hUcoatom : IsCoatom U := by
      rw [hUeq]
      exact
        MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G pinf
    rcases hUcoatom.le_iff.mp hU_le_commutator with htop | heq
    · exact htop
    · rcases hRcoordinates with ⟨coordR, _hcoordRMatrix⟩
      letI : Finite R :=
        Finite.of_injective coordR.symm coordR.symm.injective
      have hR_ne_bot : R ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hRcard]
        exact one_lt_pow₀ (by omega : 1 < q) (by decide : (3 : ℕ) ≠ 0)
      have hU_ne_bot : U ≠ ⊥ := by
        intro hUbot
        apply hR_ne_bot
        apply le_antisymm
        · rw [← hUbot]
          exact hRle
        · exact bot_le
      have hcomm_normal : (commutator G).Normal := inferInstance
      letI : U.Normal := heq ▸ hcomm_normal
      letI : MulAction.IsQuasiPreprimitive G Omega :=
        MulAction.IsPreprimitive.isQuasiPreprimitive
      have hfixed_ne_univ :
          MulAction.fixedPoints U Omega ≠ Set.univ := by
        intro hfixed
        apply hU_ne_bot
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        have hg_one :
            g = 1 :=
          (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G Omega)) g
            (fun x => by
              have hx : x ∈ MulAction.fixedPoints U Omega := by
                rw [hfixed]
                trivial
              exact MulAction.mem_fixedPoints.mp hx ⟨g, hg⟩)
        exact Subgroup.mem_bot.mpr hg_one
      letI : MulAction.IsPretransitive U Omega :=
        MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
          hfixed_ne_univ
      obtain ⟨x, hx⟩ := exists_ne pinf
      obtain ⟨u, hu⟩ :=
        @MulAction.IsPretransitive.exists_smul_eq U Omega
          inferInstance inferInstance pinf x
      have hufix : (u : G) • pinf = pinf := by
        exact u.property
      exfalso
      apply hx
      exact (calc
        pinf = (u : G) • pinf := hufix.symm
        _ = x := hu).symm
  have hsimple_standard : IsSimpleGroup G := by
    classical
    have hU_solvable : IsSolvable U := by
      have hmap_derived_two :
          (derivedSeries U 2).map U.subtype =
            (commutator R).map R.subtype := by
        rw [show 2 = 1 + 1 by omega, derivedSeries_succ,
          Subgroup.map_commutator, derivedSeries_one,
          hstabilizer_commutator, Subgroup.map_subtype_commutator]
      have hcenter_commutator :
          ⁅Subgroup.center R, Subgroup.center R⁆ = ⊥ := by
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer (H := Subgroup.center R))
      have hmap_derived_three :
          (derivedSeries U 3).map U.subtype = ⊥ := by
        change (⁅derivedSeries U 2, derivedSeries U 2⁆).map U.subtype = ⊥
        rw [Subgroup.map_commutator, hmap_derived_two, hRcomm,
          ← Subgroup.map_commutator, hcenter_commutator, Subgroup.map_bot]
      exact ⟨⟨3,
        ((derivedSeries U 3).map_eq_bot_iff_of_injective
          U.subtype_injective).mp hmap_derived_three⟩⟩
    letI : MulAction G Omega := MulAction.compHom Omega rho
    have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
      rw [MulAction.is_two_pretransitive_iff]
      intro a b c d hab hcd
      exact htwo_transitive a b c d hab hcd
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    letI : MulAction.IsPreprimitive G Omega :=
      MulAction.isPreprimitive_of_is_two_pretransitive htwo
    letI : MulAction.IsQuasiPreprimitive G Omega :=
      MulAction.IsPreprimitive.isQuasiPreprimitive
    have hOmega_one_lt : 1 < Nat.card Omega := by
      rw [hOmega_card]
      have hq_pos : 0 < q := by omega
      simpa using Nat.add_lt_add_right (pow_pos hq_pos 3) 1
    letI : Nontrivial Omega :=
      Finite.one_lt_card_iff_nontrivial.mp hOmega_one_lt
    letI : FaithfulSMul G Omega := faithfulSMul_iff.mpr (by
      intro g hg
      apply hrho
      apply Equiv.ext
      intro x
      have hx := hg x
      change rho g • x = x at hx
      rw [Equiv.Perm.smul_def] at hx
      calc
        (rho g) x = x := hx
        _ = (rho 1) x := by rw [map_one]; rfl)
    obtain ⟨g, hg, _hfixed⟩ := hthree_fixed hq
    letI : Nontrivial G :=
      nontrivial_iff_exists_ne 1 |>.2 ⟨g, hg⟩
    have hU_eq_stabilizer : U = MulAction.stabilizer G pinf := rfl
    refine { eq_bot_or_eq_top_of_normal := ?_ }
    intro N hN_normal
    by_cases hN_bot : N = ⊥
    · exact Or.inl hN_bot
    · refine Or.inr ?_
      letI : N.Normal := hN_normal
      have hfixed_ne_univ : MulAction.fixedPoints N Omega ≠ Set.univ := by
        intro hfixed
        apply hN_bot
        rw [Subgroup.eq_bot_iff_forall]
        intro n hn
        have hfix_all : ∀ omega : Omega, n • omega = omega := by
          intro omega
          have homega : omega ∈ MulAction.fixedPoints N Omega := by
            rw [hfixed]
            trivial
          exact MulAction.mem_fixedPoints.mp homega ⟨n, hn⟩
        have hn_one : n = 1 :=
          FaithfulSMul.eq_of_smul_eq_smul (m₁ := n) (m₂ := (1 : G)) (by
            intro omega
            calc
              n • omega = omega := hfix_all omega
              _ = (1 : G) • omega := (one_smul _ omega).symm)
        exact Subgroup.mem_bot.mpr hn_one
      have hN_transitive : MulAction.IsPretransitive N Omega :=
        MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
      letI : MulAction.IsPretransitive N Omega := hN_transitive
      let quotientFromU : U →* G ⧸ N :=
        (QuotientGroup.mk' N).comp U.subtype
      have hquotientFromU_surjective : Function.Surjective quotientFromU := by
        intro z
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
        obtain ⟨n, hn⟩ :=
          @MulAction.IsPretransitive.exists_smul_eq N Omega inferInstance
            inferInstance pinf (g • pinf)
        have hn' : (n : G) • pinf = g • pinf := hn
        let uval : G := (n : G)⁻¹ * g
        have hu_stabilizer : uval ∈ MulAction.stabilizer G pinf := by
          rw [MulAction.mem_stabilizer_iff]
          change ((n : G)⁻¹ * g) • pinf = pinf
          rw [mul_smul, ← hn']
          exact inv_smul_smul (n : G) pinf
        have hu_U : uval ∈ U := by
          rw [hU_eq_stabilizer]
          exact hu_stabilizer
        let u : U := ⟨uval, hu_U⟩
        refine ⟨u, ?_⟩
        change QuotientGroup.mk' N uval = QuotientGroup.mk' N g
        apply QuotientGroup.eq_iff_div_mem.mpr
        change ((n : G)⁻¹ * g) / g ∈ N
        rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel, mul_one]
        exact N.inv_mem n.property
      have hquotient_solvable : Group.IsSolvable (G ⧸ N) := by
        letI : Group.IsSolvable U := hU_solvable
        exact Group.isSolvable_of_surjective
          (f := quotientFromU) hquotientFromU_surjective
      by_contra hN_top
      letI : Nontrivial (G ⧸ N) :=
        QuotientGroup.nontrivial_iff.mpr hN_top
      letI : Group.IsPerfect G := ⟨hperfect⟩
      letI : Group.IsPerfect (G ⧸ N) := inferInstance
      exact Group.IsPerfect.not_isSolvable (G ⧸ N) hquotient_solvable
  exact hequiv.some.isSimpleGroup_congr.mpr hsimple_standard

end External
end CFSG.BenderSuzuki
