module

public import CFSG.Quasithin.Background.RonanH44Sig
public import CFSG.HardMathSupport.Foote.ModuleExclusions.Hilbert90
public import CFSG.Quasithin.Background.HFL3Par

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem mul_conjM_eq_one (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (h2 : (rhoT hK A * fldAut (bar n)) * (rhoT hK A * fldAut (bar n)) = 1) :
    (A : Matrix (Fin 3) (Fin 3) K) * conjM n (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  classical
  have hbar2 : (bar n : K ≃+* K) * bar n = 1 := by
    ext x
    change bar n (bar n x) = x
    exact bar_bar hK x
  have h3 : rhoT hK (A * mapGL (bar n) A) = 1 := by
    rw [map_mul]
    calc rhoT hK A * rhoT hK (mapGL (bar n) A) =
        rhoT hK A * rhoT hK (mapGL (bar n) A) * fldAut ((bar n : K ≃+* K) * bar n) := by
          rw [hbar2, fldAut_one, mul_one]
      _ = (rhoT hK A * fldAut (bar n)) * (rhoT hK A * fldAut (bar n)) := by
          rw [fldAut_mul, mul_assoc (rhoT hK A) (fldAut (bar n)), ← mul_assoc (fldAut (bar n)),
            fldAut_mul_rhoT]
          group
      _ = 1 := h2
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK h3
  have hd' : (A : Matrix (Fin 3) (Fin 3) K) * conjM n (A : Matrix (Fin 3) (Fin 3) K) = d • 1 := by
    rw [← hd, Units.val_mul, coe_mapGL]
    rfl
  have hdd : d * bar n d = 1 := by
    have h1 := congrArg (fun Y : HMod n K => mat Y 0 0) (congrArg (fun f => f (e00 hK)) h3)
    simp only [MulAut.one_apply, mat_rhoT, hd, tw, mat_pt, rk1_apply] at h1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, conjM, Matrix.smul_apply, rk1_apply] using h1
  have hAi : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcA : conjM n (A : Matrix (Fin 3) (Fin 3) K) = d • ((A⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) := by
    calc conjM n (A : Matrix (Fin 3) (Fin 3) K) =
        (((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * A) * conjM n (A : Matrix _ _ K) := by
          rw [hAi, Matrix.one_mul]
      _ = ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (d • 1) := by
          rw [Matrix.mul_assoc, hd']
      _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hdb : bar n d = d := by
    have h1 : conjM n ((A : Matrix (Fin 3) (Fin 3) K) * conjM n (A : Matrix (Fin 3) (Fin 3) K)) =
        conjM n (A : Matrix (Fin 3) (Fin 3) K) * A := by
      rw [conjM_mul, conjM_conjM hK]
    rw [hd', hcA, Matrix.smul_mul, hAi] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa [conjM] using h2
  have hd1 : d = 1 := eq_one_of_sq_eq_one (by rw [hdb] at hdd; exact hdd)
  rw [hd1, one_smul] at hd'
  exact hd'

theorem exists_conj_of_mul_conjM (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {A : GL (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) * conjM n (A : Matrix (Fin 3) (Fin 3) K) = 1) :
    ∃ B : GL (Fin 3) K, rhoT hK A * sig n K = rhoT hK B * sig n K * (rhoT hK B)⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (bar n : K ≃+* K) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext x
      exact bar_bar hK x
    · intro h
      obtain ⟨z, hz⟩ := exists_bar_ne hn hK
      apply hz
      have := congrArg (fun f : K ≃+* K => f z) h
      simpa using this
  have hAi : CFSG.HardMathSupport.Foote.ModuleExclusions.Ai (bar n) (A : Matrix (Fin 3) (Fin 3) K)
      2 = 1 := by
    simp only [CFSG.HardMathSupport.Foote.ModuleExclusions.Ai, Matrix.map_one _ (map_zero _)
      (map_one _), Matrix.mul_one]
    exact hA
  obtain ⟨B, hBdet, hAB⟩ := CFSG.HardMathSupport.Foote.ModuleExclusions.speiser (bar n)
    (A : Matrix (Fin 3) (Fin 3) K) 2 hord (by norm_num) hAi
  let Bu : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hBdet
  refine ⟨Bu, ?_⟩
  have hBu : (Bu : Matrix (Fin 3) (Fin 3) K) = B := rfl
  have hABu : A * mapGL (bar n) Bu = Bu := Units.ext (by
    rw [Units.val_mul, coe_mapGL, hBu]
    exact hAB)
  have hA' : A = Bu * mapGL (bar n) Bu⁻¹ := by
    rw [map_inv]
    exact eq_mul_inv_of_mul_eq hABu
  have h1 : rhoT hK Bu * sig n K * (rhoT hK Bu)⁻¹ =
      rhoT hK Bu * (fldAut (bar n) * rhoT hK Bu⁻¹ * (fldAut (bar n))⁻¹) * fldAut (bar n) := by
    rw [map_inv]
    unfold sig
    group
  rw [h1, fldAut_conj_rhoT, ← map_mul, ← hA']
  rfl

theorem exists_conj_sig (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {i : MulAut (HMod n K)} (hi : i ∈ norm hK) (hi2 : i * i = 1) (hiL : i ∉ img hK) :
    ∃ B : GL (Fin 3) K, i = rhoT hK B * sig n K * (rhoT hK B)⁻¹ := by
  obtain ⟨A, hA | hA⟩ := exists_of_involution hn hK hi hi2
  · exfalso
    apply hiL
    have hlin : i ∈ linImg hK := by
      rw [hA]
      exact ⟨A, rfl⟩
    refine mem_img_of_isPGroup_zpowers hK hlin ?_
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      show i ^ ((2 : ℕ) : ℤ) = 1 by rw [zpow_natCast, pow_two, hi2], _root_.one_zpow]
    rfl
  · have h2 : (rhoT hK A * fldAut (bar n)) * (rhoT hK A * fldAut (bar n)) = 1 := by
      rw [← hA]
      exact hi2
    obtain ⟨B, hB⟩ := exists_conj_of_mul_conjM hn hK (mul_conjM_eq_one hK h2)
    exact ⟨B, hA.trans hB⟩

end CFSG.Quasithin.RonanH44
