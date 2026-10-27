module

public import CFSG.ClassicalInvolution.AschTight.S19KLinFL
public import CFSG.ClassicalInvolution.AschTight.S19KOutL

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups Matrix

variable {F : Type} [Field F]

theorem false_of_twist {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hker : θ.ker ≤ Subgroup.center SL(3, F)) (h2 : (2 : F) ≠ 0) {v : MulAut E}
    {α : SL(3, F) →* SL(3, F)} {G : GL (Fin 3) F} (hα : ∀ x, θ (α x) = v (θ x))
    (hform : ∀ x, ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (G : Matrix (Fin 3) (Fin 3) F) * twist true x * ((G⁻¹ : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F))
    (hG : IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F)) (hv2 : v * v = 1)
    (hfix : ∀ A : SL(2, F), v (θ (WeakCT.blockSL F 3 2 0 (by omega) A)) =
      θ (WeakCT.blockSL F 3 2 0 (by omega) A)) : False := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have hσσ : ∀ x, v (v x) = x := fun x => by rw [← MulAut.mul_apply, hv2, MulAut.one_apply]
  have hαα := ModelFacts.UnitaryAut.lift_comp_self_eq_id hker hσσ hα
  set Gm := (G : Matrix (Fin 3) (Fin 3) F) with hGm
  set Gi := ((G⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hGidef
  have hGi : Gi * Gm = 1 := Units.inv_mul G
  have hGi' : Gm * Gi = 1 := Units.mul_inv G
  have hdet0 : Gm.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hGi'
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hcomm : ∀ x : SL(3, F), (Gm * Giᵀ) * (x : Matrix (Fin 3) (Fin 3) F) =
      (x : Matrix (Fin 3) (Fin 3) F) * (Gm * Giᵀ) := by
    intro x
    have h1 := congrArg (fun y : SL(3, F) => (y : Matrix (Fin 3) (Fin 3) F))
      (DFunLike.congr_fun hαα x)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at h1
    rw [hform] at h1
    have h2' : twist true (α x) = Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) * Gmᵀ := by
      simp only [twist, ↓reduceIte]
      rw [← map_inv, hform]
      simp only [twist, ↓reduceIte, inv_inv]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [h2'] at h1
    have hP : Gmᵀ * Gi * (Gm * Giᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Gi Gm, hGi, Matrix.one_mul,
        ← Matrix.transpose_mul, hGi, Matrix.transpose_one]
    calc Gm * Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) =
        Gm * Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) * (Gmᵀ * Gi * (Gm * Giᵀ)) := by
          rw [hP, Matrix.mul_one]
      _ = (Gm * (Giᵀ * (x : Matrix (Fin 3) (Fin 3) F) * Gmᵀ) * Gi) * (Gm * Giᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (x : Matrix (Fin 3) (Fin 3) F) * (Gm * Giᵀ) := by rw [h1]
  obtain ⟨s, hs⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := Gm * Giᵀ)
    fun t => (hcomm t.toSpecialLinearGroup).symm
  have hGs : Gm = s • Gmᵀ := by
    have h1 : Gm * Giᵀ * Gmᵀ = Gm := by
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hGi', Matrix.transpose_one, Matrix.mul_one]
    rw [← hs, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at h1
    exact h1.symm
  obtain ⟨hG02, hG12, hG20, hG21⟩ := hG
  have hdetB : Gm.det = (Gm 0 0 * Gm 1 1 - Gm 0 1 * Gm 1 0) * Gm 2 2 := by
    rw [Matrix.det_fin_three, hG02, hG12, hG20, hG21]
    ring
  have hG22 : Gm 2 2 ≠ 0 := fun h => hdet0 (by rw [hdetB, h, mul_zero])
  have hs1 : s = 1 := by
    have h1 := congrFun (congrFun hGs 2) 2
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h1
    have h2 : 1 * Gm 2 2 = s * Gm 2 2 := by rw [one_mul]; exact h1
    exact (mul_right_cancel₀ hG22 h2).symm
  have hsymm : Gm 0 1 = Gm 1 0 := by
    have h1 := congrFun (congrFun hGs 0) 1
    simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hs1, one_mul] at h1
    exact h1
  have heq : ∀ A : SL(2, F), ∃ r : F,
      Gm * twist true (WeakCT.blockSL F 3 2 0 (by omega) A) =
        r • ((WeakCT.blockSL F 3 2 0 (by omega) A : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Gm := by
    intro A
    set x := WeakCT.blockSL F 3 2 0 (by omega) A with hx
    have h1 : α x * x⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hfix A, mul_inv_cancel]
    obtain ⟨r, -, hr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp (hker h1)
    refine ⟨r, ?_⟩
    have h2 : α x = (α x * x⁻¹) * x := by group
    have h3 : ((α x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        r • ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
      rw [h2, Matrix.SpecialLinearGroup.coe_mul, ← hr, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul]
    rw [hform] at h3
    calc Gm * twist true x = Gm * twist true x * Gi * Gm := by
          rw [Matrix.mul_assoc _ Gi Gm, hGi, Matrix.mul_one]
      _ = r • ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * Gm := by rw [h3]
  have htw : ∀ A : SL(2, F), twist true (WeakCT.blockSL F 3 2 0 (by omega) A) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 1 1, -(A : Matrix (Fin 2) (Fin 2) F) 1 0, 0;
        -(A : Matrix (Fin 2) (Fin 2) F) 0 1, (A : Matrix (Fin 2) (Fin 2) F) 0 0, 0; 0, 0, 1] := by
    intro A
    simp only [twist, ↓reduceIte, ← map_inv, WeakCT.coe_blockSL_three_zero,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let A₁ : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let A₂ : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  obtain ⟨r₁, h₁⟩ := heq A₁
  obtain ⟨r₂, h₂⟩ := heq A₂
  rw [htw, WeakCT.coe_blockSL_three_zero] at h₁ h₂
  have e122 := congrFun (congrFun h₁ 2) 2
  have e100 := congrFun (congrFun h₁ 0) 0
  have e101 := congrFun (congrFun h₁ 0) 1
  have e201 := congrFun (congrFun h₂ 0) 1
  have e222 := congrFun (congrFun h₂ 2) 2
  simp [A₁, A₂, Matrix.mul_apply, Fin.sum_univ_three, hG02, hG12, hG20,
    hG21] at e122 e100 e101 e201 e222
  have hr₁ : r₁ = 1 := (mul_right_cancel₀ hG22 (by rw [one_mul]; exact e122)).symm
  have hr₂ : r₂ = 1 := (mul_right_cancel₀ hG22 (by rw [one_mul]; exact e222)).symm
  subst hr₁ hr₂
  simp only [one_mul] at e100 e101 e201
  have hc : Gm 1 0 = -Gm 0 1 := by linear_combination -e100
  have hd : Gm 1 1 = 0 := by linear_combination -e101
  have ha : Gm 0 0 = 0 := by linear_combination -e201
  have hb : Gm 0 1 = 0 := by
    have h3 : (2 : F) * Gm 0 1 = 0 := by linear_combination hsymm + hc
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h h2
    · exact h
  apply hdet0
  rw [hdetB, ha, hd, hb]
  ring

variable [Finite F]

theorem inner_of_fix_root (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hcl : RouteD.Gaps.LinearAutClassification F 3) {E : Type} [Group E] (θ : SL(3, F) →* E)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) {v : MulAut E}
    (hv2 : v * v = 1)
    (hfix : ∀ A : SL(2, F), v (θ (WeakCT.blockSL F 3 2 0 (by omega) A)) =
      θ (WeakCT.blockSL F 3 2 0 (by omega) A)) : ∃ y : E, v = MulAut.conj y := by
  have h2 : (2 : F) ≠ 0 := by
    have := Fintype.ofFinite F
    refine Ring.two_ne_zero fun hc => ?_
    have h1 := FiniteField.even_card_of_char_two hc
    rw [← Nat.card_eq_fintype_card] at h1
    obtain ⟨k, hk⟩ := hodd
    omega
  have hh : v ∈ fixingSubgroup (MulAut E)
      (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup E) : Set E) := by
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
    exact hfix A
  obtain ⟨α, G, ε, hα, hform, hG⟩ := lin_lift_data hodd h5 hcl θ hθ hker v
    (hyp_of_mem_fixingSubgroup θ hker hh)
  cases ε with
  | false => exact lin_inner θ hθ hker hα hform hv2
  | true => exact (false_of_twist θ hker h2 hα hform hG hv2 hfix).elim

end CFSG.Quasithin.Ch3E213M.OLA
