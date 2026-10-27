module

public import CFSG.Quasithin.Background.F7TwoInvL2Even
public import CFSG.ClassicalInvolution.Phan.AutSU3
public import CFSG.LieType.Steinberg.CentralExt.SUThreeThree
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F7TwoDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Phan

section Generic

variable {L P : Type*} [Group L] [Group P]

theorem range_le_closure_invXiAut (ρ : L →* P) (hρ : Function.Injective ρ) {φ : MulAut L}
    {α : MulAut P} (h : ∀ x, α (ρ x) = ρ (φ x)) (hφ : InvAutGen L φ) :
    ρ.range ≤ Subgroup.closure (invXiAut α) := by
  have hsub : ρ '' invXiAut φ ⊆ invXiAut α := by
    rintro _ ⟨x, hx, rfl⟩
    show ¬ IsPGroup 2 ↥(Subgroup.zpowers (α (ρ x) * (ρ x)⁻¹))
    rw [h x, ← map_inv, ← map_mul, isPGroup_zpowers_map_iff ρ hρ]
    exact hx
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Subgroup.closure (invXiAut φ) := by
    rw [(invAutGen_iff_closure_invXiAut φ).mp hφ]
    exact Subgroup.mem_top x
  refine Subgroup.closure_mono hsub ?_
  rw [← MonoidHom.map_closure]
  exact Subgroup.mem_map_of_mem ρ hx

end Generic

section SUTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] (f : ℕ)

@[expose] def suSwapGL : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]⟩

omit [Finite K] [CharP K 2] in
theorem coe_suSwapGL :
    ((suSwapGL : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

@[expose] noncomputable def suSwap : Su K 2 f 2 :=
  ⟨suSwapGL, by
    refine ⟨?_, ?_⟩
    · rw [coe_suSwapGL, Matrix.det_fin_two_of]
      simp [CharTwo.neg_eq]
    · rw [coe_suSwapGL]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem coe_coe_suSwap :
    (((suSwap f : Su K 2 f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] :=
  rfl

theorem suSwap_mul_self : suSwap f * suSwap f = (1 : Su K 2 f 2) :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_coe_suSwap, Matrix.mul_apply, Fin.sum_univ_two]))

theorem suSwap_ne_one : suSwap f ≠ (1 : Su K 2 f 2) := fun h => by
  have := congrArg (fun g : Su K 2 f 2 => (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) 0 0) h
  simp [coe_coe_suSwap] at this

theorem fieldAutSU_two_eq_conj_suSwap (A : Su K 2 f 2) :
    fieldAutSU 2 f (unitaryInvolution K 2 f) 2 A = suSwap f * A * (suSwap f)⁻¹ := by
  have hinv : (suSwap f)⁻¹ = (suSwap f : Su K 2 f 2) :=
    inv_eq_of_mul_eq_one_right (suSwap_mul_self (K := K) f)
  rw [hinv]
  set M := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det = 1 := A.2.1
  have hU : conjTr (unitaryInvolution K 2 f) M * M = 1 := A.2.2
  have h1 : conjTr (unitaryInvolution K 2 f) M = M.adjugate := by
    calc conjTr (unitaryInvolution K 2 f) M
        = conjTr (unitaryInvolution K 2 f) M * (M * M.adjugate) := by
          rw [Matrix.mul_adjugate, hdet, one_smul, Matrix.mul_one]
      _ = (conjTr (unitaryInvolution K 2 f) M * M) * M.adjugate := by rw [Matrix.mul_assoc]
      _ = M.adjugate := by rw [hU, Matrix.one_mul]
  have hneg : ∀ x : K, -x = x := CharTwo.neg_eq
  have e00 : unitaryInvolution K 2 f (M 0 0) = M 1 1 := by
    simpa [conjTr, Matrix.adjugate_fin_two] using congrFun (congrFun h1 0) 0
  have e01 : unitaryInvolution K 2 f (M 1 0) = M 0 1 := by
    simpa [conjTr, Matrix.adjugate_fin_two, hneg] using congrFun (congrFun h1 0) 1
  have e10 : unitaryInvolution K 2 f (M 0 1) = M 1 0 := by
    simpa [conjTr, Matrix.adjugate_fin_two, hneg] using congrFun (congrFun h1 1) 0
  have e11 : unitaryInvolution K 2 f (M 1 1) = M 0 0 := by
    simpa [conjTr, Matrix.adjugate_fin_two] using congrFun (congrFun h1 1) 1
  have key : M.map (unitaryInvolution K 2 f) = !![M 1 1, M 1 0; M 0 1, M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j
    exacts [e00, e10, e01, e11]
  have jmj : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * M * !![0, 1; 1, 0] =
      !![M 1 1, M 1 0; M 0 1, M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_coe_suSwap]
  exact key.trans jmj.symm

theorem invAutGen_suTwo_conj_suSwap (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    InvAutGen (Su K 2 f 2) (MulAut.conj (suSwap f)) := by
  obtain ⟨Φ⟩ := CFSG.LieType.Steinberg.CentralExt.SUThreeThree.nonempty_sl2_mulEquiv_SUid_two
    (F := K) (p := 2) (f := f) hK
  have hF4 : 4 ≤ Nat.card (fixedSubfield K 2 f) := by
    rw [card_fixedSubfield hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hg2 : Φ.symm (suSwap f) * Φ.symm (suSwap f) = 1 := by
    rw [← map_mul, suSwap_mul_self, map_one]
  have hg1 : Φ.symm (suSwap f) ≠ 1 := fun h =>
    suSwap_ne_one f (by simpa using congrArg Φ h)
  have h := InvAutGen.congr Φ (invAutGen_sl2_conj_involution hg2 hg1 hF4)
  have e : (Φ.symm.trans (MulAut.conj (Φ.symm (suSwap f)))).trans Φ = MulAut.conj (suSwap f) :=
    MulEquiv.ext fun x => by simp [MulAut.conj_apply]
  rwa [e] at h

end SUTwo

end CFSG.Quasithin.F7Two
