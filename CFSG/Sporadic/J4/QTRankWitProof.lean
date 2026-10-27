module

public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.J4.QTRankWitCheck

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native

@[expose] noncomputable def runG (R : ℕ → J) : List Ins → (ℕ → J)
  | [] => R
  | .mul i j k :: p => runG (fun r => if r = k then R i * R j else R r) p
  | .pow n i k :: p => runG (fun r => if r = k then R i ^ n else R r) p

@[expose] noncomputable def init11G (r : ℕ) : J := if r = 0 then a else if r = 1 then b else 1

section Wit

variable (hM : MatFacts)

omit hM in
theorem run_spec : ∀ (p : List Ins) (RG : ℕ → J) (RN : ℕ → Array V2),
    (∀ r, Mx (RG r) = rowsMatrix (RN r)) → ∀ r, Mx (runG RG p r) = rowsMatrix (runN RN p r)
  | [], RG, RN, h => h
  | .mul i j k :: p, RG, RN, h => by
    refine run_spec p _ _ (fun r => ?_)
    by_cases hr : r = k
    · simp [hr, map_mul, h i, h j, rowsMatrix_mulRows]
    · simp [hr, h r]
  | .pow n i k :: p, RG, RN, h => by
    refine run_spec p _ _ (fun r => ?_)
    by_cases hr : r = k
    · simp [hr, map_pow, h i, rowsMatrix_powRows]
    · simp [hr, h r]

include hM in
theorem Mx_init11 (r : ℕ) : Mx (init11G r) = rowsMatrix (init11 r) := by
  unfold init11G init11
  by_cases h0 : r = 0
  · simp only [h0, ite_true]; exact Mx_a hM
  · by_cases h1 : r = 1
    · simp only [h1, ite_true]; exact Mx_b hM
    · simp only [h0, h1, ite_false]
      rw [map_one, rowsMatrix_idRows]

end Wit

theorem pow_eq_one_of_rows {g : J} {R : Array V2} (hg : Mx g = rowsMatrix R) {n : ℕ}
    (h : eqRows (powRows R n) idRows = true) : g ^ n = 1 := by
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 h)
  rw [rowsMatrix_powRows, rowsMatrix_idRows] at this
  rw [map_pow, hg, map_one]
  exact this

theorem comm_of_rows {g h : J} {R S : Array V2} (hg : Mx g = rowsMatrix R)
    (hh : Mx h = rowsMatrix S) (hc : eqRows (mulRows R S) (mulRows S R) = true) :
    g * h = h * g := by
  apply Mx_injective
  have := congrArg rowsMatrix (eqRows_iff.1 hc)
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows] at this
  rw [map_mul, map_mul, hg, hh]
  exact this

theorem wfRows_spec {X : Array V2} (h : wfRows X = true) :
    X.size = 112 ∧ ∀ x ∈ X, x.wf = true := by
  unfold wfRows at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact Array.all_eq_true.1 h.2 i hi

theorem eta_three_conj_five (hF : J4Facts) : IsConj (eta uJ 11 3) (eta uJ 11 5) := by
  obtain ⟨o, ho, h3, p, hp, h5⟩ := orbit_five
  have := eta_conj_orbit hF ho hp
  rwa [h3, h5] at this

section Wit2

variable (hF : J4Facts)
include hF

@[expose] noncomputable def xE : J := runG init11G prog11 22

@[expose] noncomputable def yE : J := runG init11G prog11 30

@[expose] noncomputable def zE : J := xE * yE * xE⁻¹ * yE⁻¹

theorem Mx_xE : Mx xE = rowsMatrix (X11 ()) :=
  run_spec prog11 init11G init11 (Mx_init11 hF.mat) 22

theorem Mx_yE : Mx yE = rowsMatrix (Y11 ()) :=
  run_spec prog11 init11G init11 (Mx_init11 hF.mat) 30

theorem xE_pow : xE ^ 11 = 1 := pow_eq_one_of_rows (Mx_xE hF) X11_pow

theorem yE_pow : yE ^ 11 = 1 := pow_eq_one_of_rows (Mx_yE hF) Y11_pow

theorem xE_inv : xE⁻¹ = xE ^ 10 := by
  apply inv_eq_of_mul_eq_one_right
  calc xE * xE ^ 10 = xE ^ 11 := (pow_succ' xE 10).symm
    _ = 1 := xE_pow hF

theorem yE_inv : yE⁻¹ = yE ^ 10 := by
  apply inv_eq_of_mul_eq_one_right
  calc yE * yE ^ 10 = yE ^ 11 := (pow_succ' yE 10).symm
    _ = 1 := yE_pow hF

theorem Mx_zE : Mx zE = rowsMatrix (Z11 ()) := by
  rw [zE, xE_inv hF, yE_inv hF, map_mul, map_mul, map_mul, map_pow, map_pow, Mx_xE hF, Mx_yE hF,
    Z11, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRows,
    rowsMatrix_powRows]

theorem witness11 : xE ^ 11 = 1 ∧ zE ^ 11 = 1 ∧ zE ≠ 1 ∧ xE * zE = zE * xE ∧
    yE * zE = zE * yE ∧ yE⁻¹ * xE * yE = zE * xE ∧ a * xE * a = xE⁻¹ ∧ a * zE = zE * a := by
  have hM := hF.mat
  have hz := Mx_zE hF
  have hXZ : xE * zE = zE * xE := comm_of_rows (Mx_xE hF) hz XZ11_comm
  have hYZ : yE * zE = zE * yE := comm_of_rows (Mx_yE hF) hz YZ11_comm
  refine ⟨xE_pow hF, pow_eq_one_of_rows hz Z11_pow, ?_, hXZ, hYZ, ?_, ?_,
    comm_of_rows (Mx_a hM) hz AZ11_comm⟩
  · intro h1
    have h2 : rowsMatrix (Z11 ()) = rowsMatrix idRows := by
      rw [← hz, h1, map_one, rowsMatrix_idRows]
    obtain ⟨hs1, hw1⟩ := wfRows_spec Z11_wf.1
    obtain ⟨hs2, hw2⟩ := wfRows_spec Z11_wf.2
    exact rowsMatrix_ne_of_eqRows_false hs1 hs2 hw1 hw2 Z11_ne h2
  · have h1 : zE * yE * xE = xE * yE := by unfold zE; group
    calc yE⁻¹ * xE * yE = yE⁻¹ * (xE * yE) := by group
      _ = yE⁻¹ * (zE * yE * xE) := by rw [h1]
      _ = yE⁻¹ * ((yE * zE) * xE) := by rw [← hYZ, mul_assoc]
      _ = zE * xE := by group
  · apply Mx_injective
    have h1 := congrArg rowsMatrix (eqRows_iff.1 AX11_inv)
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_powRows] at h1
    rw [map_mul, map_mul, Mx_a hM, Mx_xE hF, xE_inv hF, map_pow, Mx_xE hF]
    exact h1

@[expose] noncomputable def gW : J := a * b * a * b * a

@[expose] noncomputable def c37 : J := eta uJ 11 1 * (gW⁻¹ * eta uJ 11 1 * gW)

theorem Mx_c37 : Mx c37 = rowsMatrix (C37 ()) := by
  have hM := hF.mat
  have hg0 := Mx_gEl hM (show 0 < 3 by norm_num)
  have hg1 := Mx_gEl hM (show 1 < 3 by norm_num)
  have e0 : gEl 0 = a := by simp [gEl]
  have e1 : gEl 1 = b := by simp [gEl]
  rw [e0] at hg0
  rw [e1] at hg1
  have hinv : gW⁻¹ = a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ := by unfold gW; group
  rw [c37, hinv, gW]
  simp only [map_mul]
  rw [Mx_etaR hM, hg0.1, hg1.1, hg0.2, hg1.2]
  unfold C37
  simp only [rowsMatrix_mulRows]
  rfl

theorem c37_pow : c37 ^ 37 = 1 := pow_eq_one_of_rows (Mx_c37 hF) C37_pow

theorem c37_ne : c37 ≠ 1 := by
  intro h1
  have h2 : rowsMatrix (C37 ()) = rowsMatrix idRows := by
    rw [← Mx_c37 hF, h1, map_one, rowsMatrix_idRows]
  obtain ⟨hs1, hw1⟩ := wfRows_spec C37_wf
  obtain ⟨hs2, hw2⟩ := wfRows_spec Z11_wf.2
  exact rowsMatrix_ne_of_eqRows_false hs1 hs2 hw1 hw2 C37_ne h2

theorem orderOf_c37 : orderOf c37 = 37 := by
  have : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  exact orderOf_eq_prime (c37_pow hF) (c37_ne hF)

theorem isConj_eta_three_a : IsConj (eta uJ 11 3) a := by
  have hM := hF.mat
  have hAE : Mx (a * eta uJ 11 5) = rowsMatrix (AE5 ()) := by
    rw [map_mul, Mx_a hM, Mx_etaR hM]
    unfold AE5
    rw [rowsMatrix_mulRows]
    rfl
  have h1 : (a * eta uJ 11 5) ^ 11 = 1 := pow_eq_one_of_rows hAE AE5_pow
  obtain ⟨k, hk⟩ := @dihedral_conj_odd J inferInstance a (eta uJ 11 5) (a_mul_a hM)
    (eta_sq (elem_uJ hM) 5) 11 (by decide) h1
  exact (eta_three_conj_five hF).trans (isConj_iff.2 ⟨k, hk⟩).symm

end Wit2

end CFSG.Sporadic.J4.QT
