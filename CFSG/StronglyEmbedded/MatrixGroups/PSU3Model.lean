module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Unitary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_4
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG

namespace BenderSuzuki

open Matrix
open BenderSuzuki
open BenderSuzuki.MatrixGroups

universe u v w

private def generalLinearMapEquiv
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (R : Type v) (S : Type w) [CommRing R] [CommRing S]
    (e : R ≃+* S) : GL ι R ≃* GL ι S where
  toFun := GeneralLinearGroup.map e.toRingHom
  invFun := GeneralLinearGroup.map e.symm.toRingHom
  left_inv A := by
    change (GeneralLinearGroup.map e.symm.toRingHom)
      ((GeneralLinearGroup.map e.toRingHom) A) = A
    rw [← MonoidHom.comp_apply, ← GeneralLinearGroup.map_comp]
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
      ext x
      exact e.symm_apply_apply x
    rw [he, GeneralLinearGroup.map_id]
    rfl
  right_inv A := by
    change (GeneralLinearGroup.map e.toRingHom)
      ((GeneralLinearGroup.map e.symm.toRingHom) A) = A
    rw [← MonoidHom.comp_apply, ← GeneralLinearGroup.map_comp]
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
      ext x
      exact e.apply_symm_apply x
    rw [he, GeneralLinearGroup.map_id]
    rfl
  map_mul' A B := GeneralLinearGroup.map_mul e.toRingHom A B

private theorem coe_generalLinearMapEquiv
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (R : Type v) (S : Type w) [CommRing R] [CommRing S]
    (e : R ≃+* S) (A : GL ι R) :
    ((generalLinearMapEquiv ι R S e A : GL ι S) : Matrix ι ι S) =
      (A : Matrix ι ι R).map e := by
  rfl

private def projGenLinMapEquiv
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (R : Type v) (S : Type w) [CommRing R] [CommRing S]
    (e : R ≃+* S) : ProjGenLinGroup ι R ≃* ProjGenLinGroup ι S where
  toFun := ProjGenLinGroup.map e.toRingHom
  invFun := ProjGenLinGroup.map e.symm.toRingHom
  left_inv A := by
    change (ProjGenLinGroup.map e.symm.toRingHom)
      ((ProjGenLinGroup.map e.toRingHom) A) = A
    rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
    have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
      ext x
      exact e.symm_apply_apply x
    rw [he, ProjGenLinGroup.map_id]
    rfl
  right_inv A := by
    change (ProjGenLinGroup.map e.toRingHom)
      ((ProjGenLinGroup.map e.symm.toRingHom) A) = A
    rw [← MonoidHom.comp_apply, ← ProjGenLinGroup.map_comp]
    have he : e.toRingHom.comp e.symm.toRingHom = RingHom.id S := by
      ext x
      exact e.apply_symm_apply x
    rw [he, ProjGenLinGroup.map_id]
    rfl
  map_mul' A B := map_mul (ProjGenLinGroup.map e.toRingHom) A B

private theorem projectiveSpecialUnitary_equiv_model_of_eq
    {E : Type u} [Field E] [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hn : 2 ≤ n)
    (hform : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hEcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n)
    (T : Subgroup (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))))
    (hT : T = PSU3Model n) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* T) := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let F := GaloisField 2 (2 * n)
  let : Fintype F := Fintype.ofFinite F
  have htwon : 2 * n ≠ 0 := by omega
  have hFcard : Nat.card F = (2 ^ n) ^ 2 := by
    dsimp [F]
    calc
      Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
        GaloisField.card 2 (2 * n) htwon
      _ = 2 ^ (n * 2) := by rw [Nat.mul_comm 2 n]
      _ = (2 ^ n) ^ 2 := pow_mul 2 n 2
  let eF : E ≃+* F :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hEcard, hFcard])
  let eGL : GL (Fin 3) E ≃* GL (Fin 3) F :=
    generalLinearMapEquiv (Fin 3) E F eF
  let ePGL : ProjGenLinGroup (Fin 3) E ≃*
      ProjGenLinGroup (Fin 3) F :=
    projGenLinMapEquiv (Fin 3) E F eF
  let K : Matrix (Fin 3) (Fin 3) F :=
    !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  let star (A : Matrix (Fin 3) (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F :=
    Matrix.of fun i j => A j i ^ (2 ^ n)
  have hconj (z : E) : eF (J.conj z) = eF z ^ (2 ^ n) := by
    simpa using congrArg eF
      (BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius
        J (2 ^ n) hEcard hfixed z)
  have hadjoint (A : GL (Fin 3) E) :
      (J.conjTranspose (A : Matrix (Fin 3) (Fin 3) E)).map eF =
        star (eGL A : Matrix (Fin 3) (Fin 3) F) := by
    ext i j
    simp only [HermitianForm.conjTranspose, Matrix.map_apply, star,
      Matrix.of_apply]
    exact hconj ((A : Matrix (Fin 3) (Fin 3) E) j i)
  have hformmap : J.form.map eF = K := by
    rw [hform]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [K]
  have hGLmap (A : GL (Fin 3) E) :
      (A : Matrix (Fin 3) (Fin 3) E).map eF =
        (eGL A : Matrix (Fin 3) (Fin 3) F) := by
    simpa [eGL] using
      (coe_generalLinearMapEquiv (Fin 3) E F eF A).symm
  have hunitary (A : GL (Fin 3) E) :
      J.conjTranspose (A : Matrix (Fin 3) (Fin 3) E) * J.form *
          (A : Matrix (Fin 3) (Fin 3) E) = J.form ↔
        star (eGL A : Matrix (Fin 3) (Fin 3) F) * K *
          (eGL A : Matrix (Fin 3) (Fin 3) F) = K := by
    constructor
    · intro hA
      have hm := congrArg
        (fun S : Matrix (Fin 3) (Fin 3) E => S.map eF) hA
      simpa only [Matrix.map_mul, hadjoint A, hformmap, hGLmap A] using hm
    · intro hA
      apply (eF.mapMatrix (m := Fin 3)).injective
      change
        (J.conjTranspose (A : Matrix (Fin 3) (Fin 3) E) * J.form *
          (A : Matrix (Fin 3) (Fin 3) E)).map eF = J.form.map eF
      simpa only [Matrix.map_mul, hadjoint A, hformmap, hGLmap A] using hA
  have hdet (A : GL (Fin 3) E) :
      GeneralLinearGroup.det (eGL A) = 1 ↔
        GeneralLinearGroup.det A = 1 := by
    change
      GeneralLinearGroup.det (GeneralLinearGroup.map eF.toRingHom A) = 1 ↔
        GeneralLinearGroup.det A = 1
    constructor
    · intro hA
      have hm := GeneralLinearGroup.map_det eF.symm.toRingHom
        (GeneralLinearGroup.map eF.toRingHom A)
      have hcancel :
          GeneralLinearGroup.map eF.symm.toRingHom
              (GeneralLinearGroup.map eF.toRingHom A) = A := by
        change eGL.symm (eGL A) = A
        exact eGL.symm_apply_apply A
      rw [hcancel, hA, map_one] at hm
      exact hm
    · intro hA
      rw [GeneralLinearGroup.map_det, hA, map_one]
  let U : Set (GL (Fin 3) F) :=
    {A | star (A : Matrix (Fin 3) (Fin 3) F) * K *
          (A : Matrix (Fin 3) (Fin 3) F) = K ∧
        GeneralLinearGroup.det A = 1}
  have hcarrier :
      U = (J.specialSubgroup.map eGL.toMonoidHom : Set (GL (Fin 3) F)) := by
    ext A
    change
      (star (A : Matrix (Fin 3) (Fin 3) F) * K *
          (A : Matrix (Fin 3) (Fin 3) F) = K ∧
        GeneralLinearGroup.det A = 1) ↔
        A ∈ J.specialSubgroup.map eGL.toMonoidHom
    rw [Subgroup.mem_map_equiv, J.mem_specialSubgroup_iff]
    let B : GL (Fin 3) E := eGL.symm A
    have hBA : eGL B = A := eGL.apply_symm_apply A
    change
      (star (A : Matrix (Fin 3) (Fin 3) F) * K *
          (A : Matrix (Fin 3) (Fin 3) F) = K ∧
        GeneralLinearGroup.det A = 1) ↔
      (J.conjTranspose (B : Matrix (Fin 3) (Fin 3) E) * J.form *
          (B : Matrix (Fin 3) (Fin 3) E) = J.form ∧
        GeneralLinearGroup.det B = 1)
    rw [← hBA, ← hunitary B, hdet B]
  have hspecial :
      J.specialSubgroup.map eGL.toMonoidHom = Subgroup.closure U := by
    calc
      J.specialSubgroup.map eGL.toMonoidHom =
          Subgroup.closure
            (J.specialSubgroup.map eGL.toMonoidHom : Set (GL (Fin 3) F)) :=
        (Subgroup.closure_eq _).symm
      _ = Subgroup.closure U := congrArg Subgroup.closure hcarrier.symm
  have hcomm (A : GL (Fin 3) E) :
      ePGL (ProjGenLinGroup.mk A) = ProjGenLinGroup.mk (eGL A) := by
    change
      ProjGenLinGroup.map eF.toRingHom (ProjGenLinGroup.mk A) =
        ProjGenLinGroup.mk (GeneralLinearGroup.map eF.toRingHom A)
    exact ProjGenLinGroup.map_mk eF.toRingHom A
  have hcomp :
      ePGL.toMonoidHom.comp ProjGenLinGroup.mk =
        ProjGenLinGroup.mk.comp eGL.toMonoidHom := by
    ext A
    exact hcomm A
  have hprojective :
      (J.specialSubgroup.map ProjGenLinGroup.mk).map ePGL.toMonoidHom =
        (Subgroup.closure U).map ProjGenLinGroup.mk := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hspecial]
  have htarget :
      (Subgroup.closure U).map ProjGenLinGroup.mk = T := by
    calc
      (Subgroup.closure U).map ProjGenLinGroup.mk = PSU3Model n := by rfl
      _ = T := hT.symm
  exact ⟨(ePGL.subgroupMap
      (J.specialSubgroup.map ProjGenLinGroup.mk)).trans
    (MulEquiv.subgroupCongr (hprojective.trans htarget))⟩

theorem projectiveSpecialUnitary_equiv_PSU3Model
    {E : Type u} [Field E] [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hn : 2 ≤ n)
    (hform : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hEcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3Model n) :=
  projectiveSpecialUnitary_equiv_model_of_eq J n hn hform hEcard hfixed _ rfl

end BenderSuzuki

end CFSG
