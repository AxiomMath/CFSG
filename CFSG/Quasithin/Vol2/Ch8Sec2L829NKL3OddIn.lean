module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKDefs
public import CFSG.Goldschmidt.Steps.Rank2List
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open
open Matrix

section Matrices

variable {K : Type} [Field K]

@[expose] def nkL3xMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

@[expose] def nkL3xInvMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, -1; 0, 1, 0; 0, 0, 1]

@[expose] def nkL3zMat : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def nkL3xSqMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 2; 0, 1, 0; 0, 0, 1]

theorem nkL3xMat_mul_xInvMat : nkL3xMat * nkL3xInvMat = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nkL3xMat, nkL3xInvMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem nkL3xInvMat_mul_xMat : nkL3xInvMat * nkL3xMat = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nkL3xMat, nkL3xInvMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem nkL3zMat_mul_self : nkL3zMat * nkL3zMat = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nkL3zMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_nkL3xMat : (nkL3xMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [nkL3xMat, det_fin_three]

theorem det_nkL3zMat : (nkL3zMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [nkL3zMat, det_fin_three]

theorem nkL3xSqMat_pow (n : ℕ) :
    (nkL3xSqMat : Matrix (Fin 3) (Fin 3) K) ^ n =
      !![1, 0, 2 * (n : K); 0, 1, 0; 0, 0, 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_three]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [nkL3xSqMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

@[expose] def nkL3GLx : GL (Fin 3) K :=
  ⟨nkL3xMat, nkL3xInvMat, nkL3xMat_mul_xInvMat, nkL3xInvMat_mul_xMat⟩

@[expose] def nkL3GLz : GL (Fin 3) K :=
  ⟨nkL3zMat, nkL3zMat, nkL3zMat_mul_self, nkL3zMat_mul_self⟩

theorem nkL3GLx_mem : nkL3GLx ∈ StatedSL 3 K := Subgroup.subset_closure det_nkL3xMat

theorem nkL3GLz_mem : nkL3GLz ∈ StatedSL 3 K := Subgroup.subset_closure det_nkL3zMat

end Matrices

section Core

variable {K : Type} [Field K]

@[expose] def nkL3zH : ↥(StatedSL 3 K) := ⟨nkL3GLz, nkL3GLz_mem⟩

@[expose] def nkL3xH : ↥(StatedSL 3 K) := ⟨nkL3GLx, nkL3GLx_mem⟩

@[expose] def nkL3wH : ↥(StatedSL 3 K) := nkL3zH * (nkL3xH⁻¹ * nkL3zH * nkL3xH)

theorem nkL3wH_val :
    (((nkL3wH : ↥(StatedSL 3 K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      nkL3xSqMat := by
  show nkL3zMat * (nkL3xInvMat * nkL3zMat * nkL3xMat) = nkL3xSqMat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nkL3zMat, nkL3xInvMat, nkL3xMat, nkL3xSqMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem nkL3_core (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (h2 : (2 : K) ≠ 0)
    (hpK : (p : K) = 0) :
    ∃ z g : StatedProj (StatedSL 3 K), orderOf z = 2 ∧ 6 ≤ orderOf (z * (g⁻¹ * z * g)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzH : nkL3zH (K := K) * nkL3zH (K := K) = 1 := Subtype.ext (Units.ext nkL3zMat_mul_self)
  have hzne : (QuotientGroup.mk nkL3zH : StatedProj (StatedSL 3 K)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    rintro ⟨c, hc⟩
    have hc' : (Matrix.scalar (Fin 3) (c : K) : Matrix (Fin 3) (Fin 3) K) = nkL3zMat := by
      have h := congrArg Units.val hc
      rw [Matrix.GeneralLinearGroup.coe_scalar] at h
      exact h
    have e0 : (c : K) = -1 := by
      simpa [Matrix.scalar_apply, nkL3zMat] using congrFun (congrFun hc' 0) 0
    have e2 : (c : K) = 1 := by
      simpa [Matrix.scalar_apply, nkL3zMat] using congrFun (congrFun hc' 2) 2
    exact h2 (by linear_combination e0 - e2)
  have hsq : (QuotientGroup.mk nkL3zH : StatedProj (StatedSL 3 K)) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, sq, hzH, QuotientGroup.mk_one]
  have hz2 : orderOf (QuotientGroup.mk nkL3zH : StatedProj (StatedSL 3 K)) = 2 :=
    orderOf_eq_prime hsq hzne
  have hwp : nkL3wH (K := K) ^ p = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, nkL3wH_val, nkL3xSqMat_pow,
      Subgroup.coe_one, Units.val_one, Matrix.one_fin_three, hpK, mul_zero]
  have hpow : (QuotientGroup.mk nkL3wH : StatedProj (StatedSL 3 K)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, hwp, QuotientGroup.mk_one]
  have hne : (QuotientGroup.mk nkL3wH : StatedProj (StatedSL 3 K)) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
    rintro ⟨c, hc⟩
    have e := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 2) hc
    rw [nkL3wH_val] at e
    simp [nkL3xSqMat, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e
    exact h2 e.symm
  have hord : orderOf (QuotientGroup.mk nkL3wH : StatedProj (StatedSL 3 K)) = p :=
    orderOf_eq_prime hpow hne
  refine ⟨QuotientGroup.mk nkL3zH, QuotientGroup.mk nkL3xH, hz2, ?_⟩
  have hprod : (QuotientGroup.mk nkL3zH : StatedProj (StatedSL 3 K)) *
      ((QuotientGroup.mk nkL3xH : StatedProj (StatedSL 3 K))⁻¹ * QuotientGroup.mk nkL3zH *
        QuotientGroup.mk nkL3xH) = QuotientGroup.mk nkL3wH := by
    simp only [nkL3wH, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hprod, hord]
  omega

end Core

theorem nk_l3odd_uin (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) (h4 : p % 4 = 3)
    (X : Type) [Group X] (hX : IsPSL 3 p 1 X) : UIn X := by
  have hX0 := hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hp2 : p ≠ 2 := by omega
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hKodd
  have hpK : (p : K) = 0 := by
    letI : Fintype K := Fintype.ofFinite K
    have h := Nat.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK, pow_one] at h
    exact h
  haveI : Finite (StatedProj (StatedSL 3 K)) :=
    Finite.of_surjective
      (fun g : ↥(StatedSL 3 K) => (QuotientGroup.mk g : StatedProj (StatedSL 3 K)))
      (fun q => QuotientGroup.mk_surjective q)
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  obtain ⟨hconj, -⟩ := CFSG.Goldschmidt.Rank2List.psl3_concl X hp hp2 hX0
  obtain ⟨zQ, gQ, hz, hw⟩ := nkL3_core (K := K) p hp h7 h2 hpK
  have hEs : ∀ g : StatedProj (StatedSL 3 K), orderOf (e.symm g) = orderOf g := fun g =>
    orderOf_injective e.symm.toMonoidHom e.symm.injective g
  refine ⟨hconj, e.symm zQ, e.symm gQ, by rw [hEs]; exact hz, ?_⟩
  have hc : e.symm zQ * ((e.symm gQ)⁻¹ * e.symm zQ * e.symm gQ) =
      e.symm (zQ * (gQ⁻¹ * zQ * gQ)) := by
    simp only [map_mul, map_inv]
  rw [hc, hEs]
  exact hw

end CFSG.Quasithin.H13.L829NK
