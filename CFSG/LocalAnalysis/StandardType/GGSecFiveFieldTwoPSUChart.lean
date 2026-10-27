module

public import CFSG.LocalAnalysis.StandardType.GGSelPSUChart
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.StandardType.FieldTwoPSU

open CFSG.LieType.Universal Matrix

private theorem mul_inclM_apply {F : Type*} [Field F] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) F) (ι : Fin 2 → Fin n) (a : Fin m) (c : Fin 2) :
    (M * SelectedRoot.SelPSU.inclM (F := F) ι) a c = M a (ι c) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (ι c)]
  · simp [SelectedRoot.SelPSU.inclM]
  · intro b _ hb
    simp [SelectedRoot.SelPSU.inclM, hb]
  · simp

private theorem map_inclM {F : Type*} [Field F] {n : ℕ} (σ : F ≃+* F) (ι : Fin 2 → Fin n) :
    (SelectedRoot.SelPSU.inclM (F := F) ι).map σ.toRingHom =
      SelectedRoot.SelPSU.inclM (F := F) ι := by
  ext x c
  by_cases h : x = ι c <;> simp [SelectedRoot.SelPSU.inclM, Matrix.map_apply, h]

theorem conj_embM_eq {K : Type*} [Field K] (σ : K ≃+* K) {n r : ℕ} (hn : 2 ≤ n) (hr : 2 ≤ r)
    (U : Matrix (Fin n) (Fin r) K) (Lm : Matrix (Fin r) (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (hUL : U * Lm = e) (hLU : Lm * U = 1)
    (hiso : Matrix.transpose (U.map σ.toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) K) * U =
      (Unitary.antidiag r : Matrix (Fin r) (Fin r) K))
    (hadj : Matrix.transpose (e.map σ.toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) K) =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) K) * e)
    (u u' : Matrix (Fin n) (Fin n) K) (hu : u * u' = 1)
    (hiso_u : Matrix.transpose (u.map σ.toRingHom) *
        (Unitary.antidiag n : Matrix (Fin n) (Fin n) K) * u =
      (Unitary.antidiag n : Matrix (Fin n) (Fin n) K))
    (α : K) (hα : σ α * α = 1)
    (hu0 : u *ᵥ Pi.single (⟨0, by omega⟩ : Fin n) 1 =
      α • (U *ᵥ Pi.single (⟨0, by omega⟩ : Fin r) 1))
    (hu1 : u *ᵥ Pi.single (Fin.rev (⟨0, by omega⟩ : Fin n)) 1 =
      α • (U *ᵥ Pi.single (Fin.rev (⟨0, by omega⟩ : Fin r)) 1))
    (B : Matrix (Fin 2) (Fin 2) K) :
    u * SelectedRoot.SelPSU.embM (SelectedRoot.SelPSU.pairCoord (⟨0, by omega⟩ : Fin n)) B * u' =
      U * SelectedRoot.SelPSU.embM (SelectedRoot.SelPSU.pairCoord (⟨0, by omega⟩ : Fin r)) B * Lm +
        (1 - e) := by
  classical
  let i0n : Fin n := ⟨0, by omega⟩
  let i0r : Fin r := ⟨0, by omega⟩
  let Jn : Matrix (Fin n) (Fin n) K := Unitary.antidiag n
  let Jr : Matrix (Fin r) (Fin r) K := Unitary.antidiag r
  let J2 : Matrix (Fin 2) (Fin 2) K := Unitary.antidiag 2
  let Pn : Matrix (Fin n) (Fin 2) K :=
    SelectedRoot.SelPSU.inclM (SelectedRoot.SelPSU.pairCoord i0n)
  let Pr : Matrix (Fin r) (Fin 2) K :=
    SelectedRoot.SelPSU.inclM (SelectedRoot.SelPSU.pairCoord i0r)
  simp only [SelectedRoot.SelPSU.embM]
  change u * (1 + Pn * (B - 1) * Pnᵀ) * u' =
    U * (1 + Pr * (B - 1) * Prᵀ) * Lm + (1 - e)
  have hJn : Jn * Jn = 1 := Unitary.antidiag_mul_self (F := K) n
  have hJr : Jr * Jr = 1 := Unitary.antidiag_mul_self (F := K) r
  have hu' : u' = Jn * (u.map σ.toRingHom)ᵀ * Jn := by
    have h2 : (u.map σ.toRingHom)ᵀ * Jn = Jn * u' := by
      calc (u.map σ.toRingHom)ᵀ * Jn
          = (u.map σ.toRingHom)ᵀ * Jn * (u * u') := by rw [hu, Matrix.mul_one]
        _ = ((u.map σ.toRingHom)ᵀ * Jn * u) * u' := by noncomm_ring
        _ = Jn * u' := by rw [hiso_u]
    calc u' = Jn * (Jn * u') := by rw [← Matrix.mul_assoc, hJn, Matrix.one_mul]
      _ = Jn * ((u.map σ.toRingHom)ᵀ * Jn) := by rw [← h2]
      _ = Jn * (u.map σ.toRingHom)ᵀ * Jn := by noncomm_ring
  let L1 : Matrix (Fin r) (Fin n) K := Jr * (U.map σ.toRingHom)ᵀ * Jn
  have hL1U : L1 * U = 1 := by
    calc L1 * U = Jr * ((U.map σ.toRingHom)ᵀ * Jn * U) := by
          simp only [L1, Matrix.mul_assoc]
      _ = Jr * Jr := by rw [hiso]
      _ = 1 := hJr
  have heU : e * U = U := by
    calc e * U = (U * Lm) * U := by rw [hUL]
      _ = U * (Lm * U) := by rw [Matrix.mul_assoc]
      _ = U := by rw [hLU, Matrix.mul_one]
  have heσ : (e.map σ.toRingHom) * (U.map σ.toRingHom) = U.map σ.toRingHom := by
    simpa only [Matrix.map_mul] using congrArg (fun M => M.map σ.toRingHom) heU
  have hL1e : L1 * e = L1 := by
    have htrans : (U.map σ.toRingHom)ᵀ * (e.map σ.toRingHom)ᵀ =
        (U.map σ.toRingHom)ᵀ := by
      rw [← Matrix.transpose_mul, heσ]
    have hUeJ : (U.map σ.toRingHom)ᵀ * ((e.map σ.toRingHom)ᵀ * Jn) =
        (U.map σ.toRingHom)ᵀ * Jn := by
      rw [← Matrix.mul_assoc, htrans]
    simp only [L1]
    calc Jr * (U.map σ.toRingHom)ᵀ * Jn * e
        = Jr * (U.map σ.toRingHom)ᵀ * (Jn * e) := by rw [Matrix.mul_assoc]
      _ = Jr * (U.map σ.toRingHom)ᵀ * ((e.map σ.toRingHom)ᵀ * Jn) := by
            rw [← hadj]
      _ = Jr * ((U.map σ.toRingHom)ᵀ * ((e.map σ.toRingHom)ᵀ * Jn)) := by
            rw [Matrix.mul_assoc]
      _ = Jr * ((U.map σ.toRingHom)ᵀ * Jn) := by rw [hUeJ]
      _ = Jr * (U.map σ.toRingHom)ᵀ * Jn := by rw [Matrix.mul_assoc]
  have hL1 : L1 = Lm := by
    calc L1 = L1 * e := hL1e.symm
      _ = L1 * (U * Lm) := by rw [hUL]
      _ = (L1 * U) * Lm := by simp only [L1, Matrix.mul_assoc]
      _ = Lm := by rw [hL1U, Matrix.one_mul]
  have hPJn : Pnᵀ * Jn = J2 * Pnᵀ := by
    have h := SelectedRoot.SelPSU.inclM_transpose_antidiag (F := K) (n := n)
      (ι := SelectedRoot.SelPSU.pairCoord i0n) (SelectedRoot.SelPSU.pairCoord_rev i0n)
    simpa only [Pn, Jn, J2] using h
  have hPJr : Prᵀ * Jr = J2 * Prᵀ := by
    have h := SelectedRoot.SelPSU.inclM_transpose_antidiag (F := K) (n := r)
      (ι := SelectedRoot.SelPSU.pairCoord i0r) (SelectedRoot.SelPSU.pairCoord_rev i0r)
    simpa only [Pr, Jr, J2] using h
  have hPσn : Pn.map σ.toRingHom = Pn := by
    simp only [Pn]
    exact map_inclM σ (SelectedRoot.SelPSU.pairCoord i0n)
  have hPσr : Pr.map σ.toRingHom = Pr := by
    simp only [Pr]
    exact map_inclM σ (SelectedRoot.SelPSU.pairCoord i0r)
  have hPn : u * Pn = α • (U * Pr) := by
    ext i c
    fin_cases c
    · have h := congrFun hu0 i
      rw [Matrix.mulVec_single_one] at h
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h
      simpa [Pn, Pr, mul_inclM_apply, SelectedRoot.SelPSU.pairCoord_zero, Pi.smul_apply,
        smul_eq_mul] using h
    · have h := congrFun hu1 i
      rw [Matrix.mulVec_single_one] at h
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h
      simpa [Pn, Pr, mul_inclM_apply, SelectedRoot.SelPSU.pairCoord_one, Pi.smul_apply,
        smul_eq_mul] using h
  have hPtu' : Pnᵀ * u' = (σ α) • (Prᵀ * Lm) := by
    have hmapn : (u * Pn).map σ.toRingHom = (σ α) • ((U * Pr).map σ.toRingHom) := by
      ext i c
      simp only [Matrix.map_apply, hPn, Matrix.smul_apply, smul_eq_mul, map_mul]
      rfl
    have hPtrans : Pnᵀ * (u.map σ.toRingHom)ᵀ =
        ((u * Pn).map σ.toRingHom)ᵀ := by
      rw [Matrix.map_mul, hPσn, Matrix.transpose_mul]
    have hUmap : ((U * Pr).map σ.toRingHom)ᵀ =
        Prᵀ * (U.map σ.toRingHom)ᵀ := by
      rw [Matrix.map_mul, hPσr, Matrix.transpose_mul]
    calc Pnᵀ * u'
        = Pnᵀ * (Jn * (u.map σ.toRingHom)ᵀ * Jn) := by rw [hu']
      _ = (Pnᵀ * Jn) * (u.map σ.toRingHom)ᵀ * Jn := by
            simp only [Matrix.mul_assoc]
      _ = (J2 * Pnᵀ) * (u.map σ.toRingHom)ᵀ * Jn := by rw [hPJn]
      _ = J2 * (Pnᵀ * (u.map σ.toRingHom)ᵀ) * Jn := by
            simp only [Matrix.mul_assoc]
      _ = J2 * (((u * Pn).map σ.toRingHom)ᵀ) * Jn := by rw [hPtrans]
      _ = J2 * (((σ α) • ((U * Pr).map σ.toRingHom))ᵀ) * Jn := by rw [hmapn]
      _ = J2 * ((σ α) • (((U * Pr).map σ.toRingHom)ᵀ)) * Jn := by
            rw [Matrix.transpose_smul]
      _ = (σ α) • (J2 * (((U * Pr).map σ.toRingHom)ᵀ) * Jn) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (σ α) • (J2 * (Prᵀ * (U.map σ.toRingHom)ᵀ) * Jn) := by rw [hUmap]
      _ = (σ α) • (J2 * Prᵀ * (U.map σ.toRingHom)ᵀ * Jn) := by
            rw [show J2 * (Prᵀ * (U.map σ.toRingHom)ᵀ) * Jn =
                J2 * Prᵀ * (U.map σ.toRingHom)ᵀ * Jn from by
              simp only [Matrix.mul_assoc]]
      _ = (σ α) • (Prᵀ * Jr * (U.map σ.toRingHom)ᵀ * Jn) := by rw [← hPJr]
      _ = (σ α) • (Prᵀ * L1) := by
            rw [show Prᵀ * Jr * (U.map σ.toRingHom)ᵀ * Jn = Prᵀ * L1 from by
              simp only [L1, Matrix.mul_assoc]]
      _ = (σ α) • (Prᵀ * Lm) := by rw [hL1]
  have hLHS : u * (1 + Pn * (B - 1) * Pnᵀ) * u' =
      1 + U * Pr * (B - 1) * Prᵀ * Lm := by
    have h1 : u * (1 + Pn * (B - 1) * Pnᵀ) * u' =
        u * u' + u * Pn * (B - 1) * (Pnᵀ * u') := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, hu, hPn, hPtu']
    have hα' : α * σ α = 1 := by
      rw [mul_comm]
      exact hα
    have hmain : (α • (U * Pr)) * (B - 1) * ((σ α) • (Prᵀ * Lm)) =
        U * Pr * (B - 1) * Prᵀ * Lm := by
      calc (α • (U * Pr)) * (B - 1) * ((σ α) • (Prᵀ * Lm))
          = α • ((U * Pr) * (B - 1)) * ((σ α) • (Prᵀ * Lm)) := by rw [Matrix.smul_mul]
        _ = α • (((U * Pr) * (B - 1)) * ((σ α) • (Prᵀ * Lm))) := by
              rw [Matrix.smul_mul]
        _ = α • ((σ α) • (((U * Pr) * (B - 1)) * (Prᵀ * Lm))) := by
              rw [Matrix.mul_smul]
        _ = (α * σ α) • (((U * Pr) * (B - 1)) * (Prᵀ * Lm)) := by rw [smul_smul]
        _ = (((U * Pr) * (B - 1)) * (Prᵀ * Lm)) := by rw [hα', one_smul]
        _ = U * Pr * (B - 1) * Prᵀ * Lm := by simp only [Matrix.mul_assoc]
    rw [hmain]
  have hRHS : U * (1 + Pr * (B - 1) * Prᵀ) * Lm + (1 - e) =
      1 + U * Pr * (B - 1) * Prᵀ * Lm := by
    have h1 : U * (1 + Pr * (B - 1) * Prᵀ) * Lm =
        U * Lm + U * Pr * (B - 1) * Prᵀ * Lm := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, hUL]
    abel
  rw [hLHS, hRHS]

end CFSG.StandardType.FieldTwoPSU

end
