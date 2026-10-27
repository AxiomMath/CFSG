module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
import CFSG.Quasithin.AppendixH.H9.GLBasics
import all CFSG.LieType.Universal.SymplecticExtras.RankOne
import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin

private theorem caInv_isBlk_mulVec_eq_self {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : Type} [Field F] {p q : κ} {M : Matrix κ κ F}
    (hM : CFSG.LieType.Universal.Symplectic.SpExtras.IsBlk p q M) {v : κ → F}
    (hp : v p = 0) (hq : v q = 0) : M *ᵥ v = v := by
  have h : M *ᵥ v = (1 : Matrix κ κ F) *ᵥ v := by
    funext r
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t = p
    · rw [ht, hp, mul_zero, mul_zero]
    · by_cases ht' : t = q
      · rw [ht', hq, mul_zero, mul_zero]
      · rw [hM r t (Or.inr ⟨ht, ht'⟩)]
  rw [h, Matrix.one_mulVec]

private theorem caInv_isBlk_mul_eq_self {κ : Type*} [Fintype κ] [DecidableEq κ]
    {F : Type} [Field F] {p q : κ} {M : Matrix κ κ F}
    (hM : CFSG.LieType.Universal.Symplectic.SpExtras.IsBlk p q M) {y : κ → F}
    (hp : y p = 0) (hq : y q = 0) : (fun j => ∑ i, y i * M i j) = y := by
  funext j
  have hsum : (∑ i, y i * M i j) = ∑ i, y i * (1 : Matrix κ κ F) i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i = p
    · rw [hi, hp, zero_mul, zero_mul]
    · by_cases hi' : i = q
      · rw [hi', hq, zero_mul, zero_mul]
      · rw [hM i j (Or.inl ⟨hi, hi'⟩)]
  rw [hsum]
  have hone : (∑ i, y i * (1 : Matrix κ κ F) i j) = y j := by
    have h := congrFun (Matrix.one_mulVec (v := y)) j
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  exact hone

private theorem caInv_lastTwo_isBlk (k : ℕ) :
    CFSG.LieType.Universal.Symplectic.SpExtras.IsBlk (Fin.castSucc (Fin.last k))
      (Fin.last (k + 1))
      ((lastTwo (k + 2) rhoTwo : GL (Fin (k + 2)) (ZMod 2)) :
        Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) :=
  CFSG.LieType.Steinberg.Sp.isBlk_blockMat
    (rhoTwo : Matrix (Fin 2) (Fin 2) (ZMod 2))

theorem exists_levi_commute_bStar {m : ℕ} (hm : 4 ≤ m) {a : Matrix (Fin 1) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin 1) (ZMod 2)} {c : Matrix (Fin 1) (Fin 1) (ZMod 2)}
    (h2 : uGL a b c * uGL a b c = (1 : GL (BlkIdx 1 m) (ZMod 2))) :
    ∃ R : GL (Fin m) (ZMod 2),
      Commute (levi 1 R * bStar m * (levi 1 R)⁻¹) (uGL a b c) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  have hab : a * b = 0 := by
    have h := h2
    rw [uGL_mul, ← uGL_zero] at h
    obtain ⟨-, -, h3⟩ := uGL_injective h
    have hcc : c + c = 0 := by
      ext i j
      simp only [Matrix.add_apply, Matrix.zero_apply]
      exact CharTwo.add_self_eq_zero _
    rw [hcc, zero_add] at h3
    exact h3
  let i0 : Fin (k + 2) := ⟨0, by omega⟩
  let i1 : Fin (k + 2) := ⟨1, by omega⟩
  have hp0 : Fin.castSucc (Fin.last k) ≠ i0 := by
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (i0 : ℕ) = 0 := rfl
    have h3 : (Fin.castSucc (Fin.last k) : ℕ) = k := rfl
    omega
  have hq0 : Fin.last (k + 1) ≠ i0 := by
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (i0 : ℕ) = 0 := rfl
    have h3 : (Fin.last (k + 1) : ℕ) = k + 1 := rfl
    omega
  have hp1 : Fin.castSucc (Fin.last k) ≠ i1 := by
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (i1 : ℕ) = 1 := rfl
    have h3 : (Fin.castSucc (Fin.last k) : ℕ) = k := rfl
    omega
  have hq1 : Fin.last (k + 1) ≠ i1 := by
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (i1 : ℕ) = 1 := rfl
    have h3 : (Fin.last (k + 1) : ℕ) = k + 1 := rfl
    omega
  have hi10 : i1 ≠ i0 := by
    intro h
    have h1 := congrArg Fin.val h
    have h2 : (i1 : ℕ) = 1 := rfl
    have h3 : (i0 : ℕ) = 0 := rfl
    omega
  have he0 : (Pi.single i0 (1 : ZMod 2) : Fin (k + 2) → ZMod 2) ≠ 0 := by
    intro h
    have h1 := congrFun h i0
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have he1 : (Pi.single i1 (1 : ZMod 2) : Fin (k + 2) → ZMod 2) ≠ 0 := by
    intro h
    have h1 := congrFun h i1
    rw [Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  have h10 : (Pi.single i1 (1 : ZMod 2)) ⬝ᵥ (Pi.single i0 (1 : ZMod 2)) = 0 := by
    rw [single_dotProduct, one_mul]
    exact Pi.single_eq_of_ne hi10 1
  set bv : Fin (k + 2) → ZMod 2 := fun i => b i 0 with hbv_def
  obtain ⟨R, hcolp, hcolq, hrowp, hrowq⟩ : ∃ R : GL (Fin (k + 2)) (ZMod 2),
      ((↑(R⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *ᵥ bv)
          (Fin.castSucc (Fin.last k)) = 0 ∧
        ((↑(R⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *ᵥ bv)
          (Fin.last (k + 1)) = 0 ∧
        (a * (↑R : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) 0
          (Fin.castSucc (Fin.last k)) = 0 ∧
        (a * (↑R : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) 0
          (Fin.last (k + 1)) = 0 := by
    by_cases ha : a = 0
    · by_cases hb : b = 0
      · refine ⟨1, ?_, ?_, ?_, ?_⟩ <;> simp [hbv_def, ha, hb]
      · have hbvnz : bv ≠ 0 := by
          rw [hbv_def]
          intro h
          apply hb
          ext i j
          fin_cases j
          exact congrFun h i
        obtain ⟨A, hA⟩ := CFSG.ASVolI.ChH.exists_GL_mulVec_eq (n := k + 2)
          (v := bv) (w := Pi.single i0 (1 : ZMod 2)) hbvnz he0
        refine ⟨A⁻¹, ?_, ?_, ?_, ?_⟩
        · rw [inv_inv, hA]
          exact Pi.single_eq_of_ne hp0 1
        · rw [inv_inv, hA]
          exact Pi.single_eq_of_ne hq0 1
        · simp [ha]
        · simp [ha]
    · by_cases hb : b = 0
      · have hav : (a 0 : Fin (k + 2) → ZMod 2) ≠ 0 := by
          intro h
          apply ha
          ext i j
          fin_cases i
          exact congrFun h j
        obtain ⟨A, hA⟩ := CFSG.ASVolI.ChH.exists_GL_mulVec_eq (n := k + 2)
          (v := a 0) (w := Pi.single i0 (1 : ZMod 2)) hav he0
        let R : GL (Fin (k + 2)) (ZMod 2) :=
          Matrix.GeneralLinearGroup.inverseTranspose (A⁻¹)
        have hRcoe : (↑R : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) =
            ((A : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)))ᵀ := by
          show ((Matrix.GeneralLinearGroup.inverseTranspose (A⁻¹) : GL (Fin (k + 2)) (ZMod 2)) :
            Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) = _
          rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, inv_inv]
        have hrow : ∀ j, (a * (↑R : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) 0 j =
            (Pi.single i0 (1 : ZMod 2) : Fin (k + 2) → ZMod 2) j := by
          intro j
          have h := congrFun hA j
          simp only [Matrix.mulVec, dotProduct] at h
          rw [Matrix.mul_apply]
          simp only [hRcoe, Matrix.transpose_apply]
          rw [← h]
          refine Finset.sum_congr rfl fun i _ => ?_
          show a 0 i * A j i = A j i * a 0 i
          exact mul_comm _ _
        refine ⟨R, ?_, ?_, ?_, ?_⟩
        · rw [hbv_def, hb]
          change ((↑(R⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *ᵥ
            (0 : Fin (k + 2) → ZMod 2)) (Fin.castSucc (Fin.last k)) = 0
          rw [Matrix.mulVec_zero]
          rfl
        · rw [hbv_def, hb]
          change ((↑(R⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *ᵥ
            (0 : Fin (k + 2) → ZMod 2)) (Fin.last (k + 1)) = 0
          rw [Matrix.mulVec_zero]
          rfl
        · rw [hrow (Fin.castSucc (Fin.last k))]
          exact Pi.single_eq_of_ne hp0 1
        · rw [hrow (Fin.last (k + 1))]
          exact Pi.single_eq_of_ne hq0 1
      · have hbvnz : bv ≠ 0 := by
          rw [hbv_def]
          intro h
          apply hb
          ext i j
          fin_cases j
          exact congrFun h i
        have hav : (a 0 : Fin (k + 2) → ZMod 2) ≠ 0 := by
          intro h
          apply ha
          ext i j
          fin_cases i
          exact congrFun h j
        have hdot : (a 0) ⬝ᵥ bv = 0 := by
          rw [hbv_def]
          have h := congrFun (congrFun hab 0) 0
          rw [Matrix.mul_apply] at h
          simpa [dotProduct] using h
        obtain ⟨A, hA1, hA2⟩ := CFSG.ASVolI.ChH.exists_GL_mulVec_pair (n := k + 2)
          (v := bv) (φ := a 0) (v' := Pi.single i0 (1 : ZMod 2))
          (φ' := Pi.single i1 (1 : ZMod 2)) hbvnz hav he0 he1 (by rw [hdot, h10])
        have hrow : ∀ j, (a * (↑(A⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) 0 j =
            (Pi.single i1 (1 : ZMod 2) : Fin (k + 2) → ZMod 2) j := by
          intro j
          have h := congrFun hA2 j
          have hcoe : (((CFSG.ASVolI.ChH.dualGLn (k + 2) A : GL (Fin (k + 2)) (ZMod 2)) :
              Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) =
              ((↑(A⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)))ᵀ := rfl
          simp only [Matrix.mulVec, dotProduct] at h
          simp only [hcoe, Matrix.transpose_apply] at h
          rw [Matrix.mul_apply, ← h]
          refine Finset.sum_congr rfl fun i _ => ?_
          show a 0 i * (↑(A⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) i j =
            (↑(A⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) i j * a 0 i
          exact mul_comm _ _
        refine ⟨A⁻¹, ?_, ?_, ?_, ?_⟩
        · rw [inv_inv, hA1]
          exact Pi.single_eq_of_ne hp0 1
        · rw [inv_inv, hA1]
          exact Pi.single_eq_of_ne hq0 1
        · rw [hrow (Fin.castSucc (Fin.last k))]
          exact Pi.single_eq_of_ne hp1 1
        · rw [hrow (Fin.last (k + 1))]
          exact Pi.single_eq_of_ne hq1 1
  set RM : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2) := ↑R with hRM
  set R2 : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2) :=
    ↑(lastTwo (k + 2) rhoTwo) with hR2
  set Ri : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2) := ↑(R⁻¹) with hRi
  have hrowp' : (a * RM) 0 (Fin.castSucc (Fin.last k)) = 0 := hrowp
  have hrowq' : (a * RM) 0 (Fin.last (k + 1)) = 0 := hrowq
  have hrowfix' : a * RM * R2 = a * RM := by
    ext i j
    fin_cases i
    rw [Matrix.mul_apply, hR2]
    exact congrFun (caInv_isBlk_mul_eq_self (hM := caInv_lastTwo_isBlk k)
      (y := fun j => (a * RM) 0 j) hrowp' hrowq') j
  set D : GL (Fin (k + 2)) (ZMod 2) := R * lastTwo (k + 2) rhoTwo * R⁻¹ with hD
  have hvalD : (↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) = RM * R2 * Ri := by
    rw [hD, Units.val_mul, Units.val_mul, hRM, hR2, hRi]
  have hRinv : RM * Ri = 1 := by
    rw [hRM, hRi]; simp
  have hDinv : (↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *
      (↑(D⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) = 1 := by simp
  have hD1' : a * (↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) = a := by
    rw [hvalD]
    calc a * ((RM * R2) * Ri)
        = a * (RM * (R2 * Ri)) := by rw [Matrix.mul_assoc]
      _ = (a * RM) * (R2 * Ri) := by rw [← Matrix.mul_assoc]
      _ = ((a * RM) * R2) * Ri := by rw [← Matrix.mul_assoc]
      _ = (a * RM) * Ri := by rw [hrowfix']
      _ = a * (RM * Ri) := by rw [← Matrix.mul_assoc]
      _ = a := by rw [hRinv, Matrix.mul_one]
  have hD1inv : a * (↑(D⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) = a := by
    calc a * (↑(D⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) =
        (a * (↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) *
          (↑(D⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) := by rw [hD1']
      _ = a * ((↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *
            (↑(D⁻¹) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2))) := by
          rw [Matrix.mul_assoc]
      _ = a := by rw [hDinv, Matrix.mul_one]
  have hcolvec : R2 *ᵥ (Ri *ᵥ bv) = Ri *ᵥ bv := by
    rw [hR2, hRi]
    exact caInv_isBlk_mulVec_eq_self (hM := caInv_lastTwo_isBlk k) hcolp hcolq
  have hD2vec : (↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) *ᵥ bv = bv := by
    rw [hvalD]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [hcolvec]
    rw [Matrix.mulVec_mulVec, hRinv, Matrix.one_mulVec]
  have hD2 : (↑D : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 2)) * b = b := by
    ext i j
    fin_cases j
    have h := congrFun hD2vec i
    rw [hbv_def] at h
    exact h
  have hconj : levi 1 D * uGL a b c * (levi 1 D)⁻¹ = uGL a b c := by
    have h := levi_conj_uGL 1 (k + 2) (1 : GL (Fin 1) (ZMod 2)) D a b c
    rw [h]
    simp only [Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, hD1inv, hD2]
  have hlevi : levi 1 R * bStar (k + 2) * (levi 1 R)⁻¹ = levi 1 D := by
    have h : levi 1 R * bStar (k + 2) * (levi 1 R)⁻¹ =
        (leviOne (k + 2)) (R * lastTwo (k + 2) rhoTwo * R⁻¹) := by
      rw [bStar, map_mul, map_mul, map_inv]
      rfl
    rw [h, hD]
    rfl
  refine ⟨R, ?_⟩
  rw [hlevi]
  show levi 1 D * uGL a b c = uGL a b c * levi 1 D
  calc levi 1 D * uGL a b c = levi 1 D * uGL a b c * (levi 1 D)⁻¹ * levi 1 D := by group
    _ = uGL a b c * levi 1 D := by rw [hconj]

end CFSG.StandardType.FF81.CentA

end
