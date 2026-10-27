module

public import CFSG.Quasithin.Background.HSU3Torus

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H Matrix
open scoped Matrix

noncomputable section

variable {F : Type} [Field F]

@[expose] noncomputable def su3Anti (F : Type) [Field F] [CharP F 2] (k : ℕ) :
    Subgroup (GL (Fin 3) F) :=
  (StatedSU 3 (2 ^ k) F).map
    (MulAut.conj ((CFSG.Quasithin.H.SU3.wittGL (K := F))⁻¹)).toMonoidHom

theorem mem_su3Anti_iff [Finite F] [CharP F 2] {k : ℕ}
    (hFc : Nat.card F = (2 ^ k) ^ 2) {g : GL (Fin 3) F} :
    g ∈ su3Anti F k ↔
      (g : Matrix (Fin 3) (Fin 3) F).det = 1 ∧
        ((g : Matrix (Fin 3) (Fin 3) F).map (· ^ (2 ^ k)))ᵀ *
          (CFSG.Quasithin.H.SU3.antiJ (K := F)) * (g : Matrix (Fin 3) (Fin 3) F) =
          CFSG.Quasithin.H.SU3.antiJ (K := F) := by
  rw [su3Anti, Subgroup.mem_map_equiv]
  rw [MulAut.conj_symm_apply, inv_inv]
  set W := CFSG.Quasithin.H.SU3.wittGL (K := F) with hW
  set A : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F) with hA
  have hcoe : ((W * g * W⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F) * A *
        CFSG.Quasithin.H.SU3.wittInv := by
    rw [Units.val_mul, Units.val_mul, CFSG.Quasithin.H.SU3.coe_wittGL,
      CFSG.Quasithin.H.SU3.coe_wittGL_inv]
  have hWW : (CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F).det *
      (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← Matrix.det_mul, CFSG.Quasithin.H.SU3.wittMat_mul_wittInv, Matrix.det_one]
  constructor
  · intro h
    have hdet0 := CFSG.Quasithin.H.SU3.det_of_mem_statedSU h
    rw [hcoe] at hdet0
    have huni0 := CFSG.Quasithin.H.SU3.isUnitaryM_of_mem (n := k) hFc h
    rw [hcoe] at huni0
    have hd : A.det = 1 := by
      have h : (CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F).det * A.det *
          (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F).det = 1 := by
        rw [← Matrix.det_mul, ← Matrix.det_mul]
        exact hdet0
      rw [show (CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F).det * A.det *
            (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F).det =
            A.det * ((CFSG.Quasithin.H.SU3.wittMat : Matrix (Fin 3) (Fin 3) F).det *
              (CFSG.Quasithin.H.SU3.wittInv : Matrix (Fin 3) (Fin 3) F).det) by ring] at h
      rwa [hWW, mul_one] at h
    refine ⟨hd, ?_⟩
    have hJ := (CFSG.Quasithin.H.SU3.isUnitaryM_conj_iff (n := k) (A := A)).mp huni0
    simpa [CFSG.Quasithin.H.SU3.IsUnitaryJ, CFSG.Quasithin.H.SU3.conjM_eq_map_pow] using hJ
  · rintro ⟨hdet, huni⟩
    refine CFSG.Quasithin.H.SU3.mem_statedSU ?_ ?_
    · rw [hcoe, Matrix.det_mul, Matrix.det_mul, hdet, mul_one, hWW]
    · rw [hcoe]
      have hJ : CFSG.Quasithin.H.SU3.IsUnitaryJ k A := by
        rw [CFSG.Quasithin.H.SU3.IsUnitaryJ, CFSG.Quasithin.H.SU3.conjM_eq_map_pow]
        exact huni
      have h := (CFSG.Quasithin.H.SU3.isUnitaryM_conj_iff (n := k) (A := A)).mpr hJ
      simpa [CFSG.Quasithin.H.SU3.IsUnitaryM,
        CFSG.Quasithin.H.SU3.conjM_eq_map_pow] using h

theorem exists_uJGL_of_mem_ujSub [Finite F] [CharP F 2] {k : ℕ}
    (hFc : Nat.card F = (2 ^ k) ^ 2) {u : GL (Fin 3) F}
    (hu : u ∈ CFSG.Quasithin.H.SU3.ujSub k F) :
    ∃ a b : F, b + b ^ (2 ^ k) = a * a ^ (2 ^ k) ∧
      u = CFSG.Quasithin.H.SU3.uJGL k a b := by
  obtain ⟨huL, huT⟩ := Subgroup.mem_inf.mp hu
  obtain ⟨hlow, hdiag⟩ := CFSG.Quasithin.H.Tri.uni3_entries huT
  obtain ⟨-, hform⟩ := (mem_su3Anti_iff (F := F) hFc).mp huL
  set A : Matrix (Fin 3) (Fin 3) F := (u : Matrix (Fin 3) (Fin 3) F) with hA
  let a : F := A 0 1
  let b : F := A 0 2
  have h10 : A 1 0 = 0 := hlow 1 0 (by decide)
  have h20 : A 2 0 = 0 := hlow 2 0 (by decide)
  have h21 : A 2 1 = 0 := hlow 2 1 (by decide)
  have h00 : A 0 0 = 1 := hdiag 0
  have h11 : A 1 1 = 1 := hdiag 1
  have h22 : A 2 2 = 1 := hdiag 2
  have h12 : A 1 2 = a ^ (2 ^ k) := by
    have h := congrFun (congrFun hform 1) 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three,
      CFSG.Quasithin.H.SU3.antiJ] at h
    have hh : A 1 2 + a ^ (2 ^ k) = 0 := by
      simpa [a, h21, h00, h11, h22] using h
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hh
    exact hh
  have htr : b + b ^ (2 ^ k) = a * a ^ (2 ^ k) := by
    have h := congrFun (congrFun hform 2) 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three,
      CFSG.Quasithin.H.SU3.antiJ] at h
    have hp : (a ^ (2 ^ k)) ^ (2 ^ k) = a := by
      letI : Fintype F := Fintype.ofFinite F
      rw [← pow_mul, show 2 ^ k * 2 ^ k = Nat.card F by rw [hFc]; ring,
        Nat.card_eq_fintype_card]
      exact FiniteField.pow_card a
    have hh : b + a * a ^ (2 ^ k) + b ^ (2 ^ k) = 0 := by
      simpa [b, a, h12, h21, h00, h11, h22, hp] using h
    have h1 : b + a * a ^ (2 ^ k) = b ^ (2 ^ k) := by
      have h' := add_eq_zero_iff_eq_neg.mp hh
      simpa [CharTwo.neg_eq] using h'
    rw [← h1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  refine ⟨a, b, htr, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [A, a, b, h10, h20, h21, h00, h11, h22, h12,
      CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.uJMat,
      CFSG.Quasithin.H.SU3.bar_apply]

theorem hasScalarCommutant_su3Anti [Finite F] [CharP F 2] {k : ℕ} (hk : 1 ≤ k)
    (hFc : Nat.card F = (2 ^ k) ^ 2) :
    CFSG.Quasithin.H.HasScalarCommutant (su3Anti F k) := by
  classical
  intro f hf
  have hSU := CFSG.Quasithin.H.SU3.hasScalarCommutant' (n := k) hk hFc
  let W : GL (Fin 3) F := CFSG.Quasithin.H.SU3.wittGL (K := F)
  let cW : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => (W : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      map_zero' := Matrix.mulVec_zero _
      map_add' := fun v w => Matrix.mulVec_add _ _ _ }
  let cWi : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun v => ((W⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      map_zero' := Matrix.mulVec_zero _
      map_add' := fun v w => Matrix.mulVec_add _ _ _ }
  let f' : (Fin 3 → F) →+ (Fin 3 → F) := cW.comp (f.comp cWi)
  have hf' : ∀ s ∈ StatedSU 3 (2 ^ k) F, ∀ v,
      f' ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        (s : Matrix (Fin 3) (Fin 3) F) *ᵥ f' v := by
    intro s hs v
    have hs' : W⁻¹ * s * W ∈ su3Anti F k := by
      rw [su3Anti]
      refine Subgroup.mem_map_equiv.mpr ?_
      rw [MulAut.conj_symm_apply, inv_inv]
      dsimp only [W]
      convert hs using 1
      group
    have hcomp : cWi ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
        ((W⁻¹ * s * W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ cWi v := by
      simp [cWi, Matrix.mulVec_mulVec, mul_assoc]
    calc
      f' ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ v)
          = cW (f (cWi ((s : Matrix (Fin 3) (Fin 3) F) *ᵥ v))) := rfl
      _ = cW (f (((W⁻¹ * s * W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            cWi v)) := by rw [hcomp]
      _ = cW (((W⁻¹ * s * W : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
            f (cWi v)) := by rw [hf _ hs' (cWi v)]
      _ = (s : Matrix (Fin 3) (Fin 3) F) *ᵥ cW (f (cWi v)) := by
        simp [cW, Matrix.mulVec_mulVec, mul_assoc]
      _ = (s : Matrix (Fin 3) (Fin 3) F) *ᵥ f' v := rfl
  obtain ⟨c, hc⟩ := hSU f' hf'
  refine ⟨c, fun v => ?_⟩
  have hv := hc (cW v)
  have h1 : cWi (cW v) = v := by
    simp [cWi, cW, Matrix.mulVec_mulVec]
  have h2 : cW (f v) = c • cW v := by simpa [f', h1] using hv
  have h3 : cWi (cW (f v)) = cWi (c • cW v) := congrArg cWi h2
  simpa [cWi, cW, Matrix.mulVec_mulVec, Matrix.mulVec_smul] using h3

theorem uJMat_mulVec [Finite F] [CharP F 2] {k : ℕ} (a b : F) (v : Fin 3 → F) :
    (CFSG.Quasithin.H.SU3.uJMat k a b) *ᵥ v =
      ![v 0 + a * v 1 + b * v 2,
        v 1 + CFSG.Quasithin.H.SU3.bar k a * v 2, v 2] := by
  ext i
  fin_cases i <;>
    simp [CFSG.Quasithin.H.SU3.uJMat, Matrix.mulVec, Fin.sum_univ_three, vecHead, vecTail,
      add_assoc]

theorem uJMat_mulVec_single_zero [Finite F] [CharP F 2] {k : ℕ} (a b c : F) :
    (CFSG.Quasithin.H.SU3.uJMat k a b) *ᵥ (Pi.single 0 c : Fin 3 → F) =
      Pi.single 0 c := by
  rw [uJMat_mulVec]
  ext i
  fin_cases i <;> simp [vecHead, vecTail]

theorem uJMat_mulVec_single_one [Finite F] [CharP F 2] {k : ℕ} (a b c : F) :
    (CFSG.Quasithin.H.SU3.uJMat k a b) *ᵥ (Pi.single 1 c : Fin 3 → F) =
      (a * c) • (Pi.single 0 1 : Fin 3 → F) + c • (Pi.single 1 1 : Fin 3 → F) := by
  rw [uJMat_mulVec]
  ext i
  fin_cases i <;> simp [vecHead, vecTail, add_comm, add_left_comm, add_assoc]

theorem uJMat_mulVec_single_two [Finite F] [CharP F 2] {k : ℕ} (a b c : F) :
    (CFSG.Quasithin.H.SU3.uJMat k a b) *ᵥ (Pi.single 2 c : Fin 3 → F) =
      (b * c) • (Pi.single 0 1 : Fin 3 → F) +
        (CFSG.Quasithin.H.SU3.bar k a * c) • (Pi.single 1 1 : Fin 3 → F) +
          c • (Pi.single 2 1 : Fin 3 → F) := by
  rw [uJMat_mulVec]
  ext i
  fin_cases i <;> simp [vecHead, vecTail, add_comm, add_left_comm, add_assoc]

theorem uJMat_mul [Finite F] [CharP F 2] {k : ℕ} (a b a' b' : F) :
    CFSG.Quasithin.H.SU3.uJMat k a b * CFSG.Quasithin.H.SU3.uJMat k a' b' =
      CFSG.Quasithin.H.SU3.uJMat k (a + a')
        (b + b' + a * CFSG.Quasithin.H.SU3.bar k a') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Quasithin.H.SU3.uJMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem uJGL_mul [Finite F] [CharP F 2] {k : ℕ} (a b a' b' : F) :
    CFSG.Quasithin.H.SU3.uJGL k a b * CFSG.Quasithin.H.SU3.uJGL k a' b' =
      CFSG.Quasithin.H.SU3.uJGL k (a + a')
        (b + b' + a * CFSG.Quasithin.H.SU3.bar k a') := by
  apply Units.ext
  rw [Units.val_mul, CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.coe_uJGL,
    CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mul]

end

end CFSG.Quasithin.Stroth
