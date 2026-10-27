
module

public import CFSG.Monster.B.TwoA.Sp8.ElemAbBase

public import CFSG.Monster.B.TwoA.Sp8.Zrel
public import CFSG.Monster.Visible.SignCompat.TrialityCycleOctad

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.B.TwoA.Census CFSG.Monster.VisCert CFSG.Monster.B.Co2

theorem tauhat_conj_uhat : tauhat * uhat * tauhat⁻¹ = ghat8 := rfl

theorem tauC_conj_slC :
    tauC * slC * tauC⁻¹ =
      slC * ⟨rhoEquiv (XQ ⟨dC, 0⟩), rhoEquiv_mem_Cgen XQ_dC_mem_centralizer⟩ :=
  Subtype.ext tauB_conj_slPair

theorem tauhat_conj_ghat8 :
    tauhat * ghat8 * tauhat⁻¹ = uhat * ghat8 := by
  have h := congrArg (fun x => iotaD (kappa x)) tauC_conj_slC
  simp only [map_mul, map_inv] at h
  rw [ghat8_eq]
  refine h.trans ?_
  rw [← ghat8_eq]
  have hc := ghat8_comm_PhiD (Pi.single 6 1)
  rw [PhiD_single_six] at hc
  exact hc

theorem Psi_add_single
    (j k : Fin 8) :
    Psi (Pi.single j 1 + Pi.single k 1) = aT j * aT k := by
  rw [Psi_add, Psi_single, Psi_single]

theorem aT_zero : aT 0 = xhat := rfl
theorem aT_one : aT 1 = yhat := rfl
theorem aT_two : aT 2 = dhat 2 3 := rfl
theorem aT_three : aT 3 = dhat 2 4 := rfl
theorem aT_four : aT 4 = dhat 2 5 := rfl
theorem aT_five : aT 5 = dhat 2 6 := rfl
theorem aT_six : aT 6 = uhat := rfl
theorem aT_seven : aT 7 = ghat8 := rfl

theorem tauhat_conj_aT
    (k : Fin 8) :
    tauhat * aT k * tauhat⁻¹ =
      (aEquiv (Multiplicative.ofAdd (bvec 8 (triRows.getD k 0))) : Dfull) := by
  rw [coe_aEquiv, toAdd_ofAdd, bvec_triRows]
  fin_cases k
  · show tauhat * aT 0 * tauhat⁻¹ = Psi (Pi.single 0 1 + Pi.single 1 1)
    rw [Psi_add_single, aT_zero, aT_one, tauhat_conj_xhat']
  · show tauhat * aT 1 * tauhat⁻¹ = Psi (Pi.single 0 1)
    rw [Psi_single, aT_zero, aT_one, tauhat_conj_yhat]
  · show tauhat * aT 2 * tauhat⁻¹ = Psi (Pi.single 2 1)
    rw [Psi_single, aT_two, tauhat_conj_dhat]
  · show tauhat * aT 3 * tauhat⁻¹ = Psi (Pi.single 3 1)
    rw [Psi_single, aT_three, tauhat_conj_dhat]
  · show tauhat * aT 4 * tauhat⁻¹ = Psi (Pi.single 4 1)
    rw [Psi_single, aT_four, tauhat_conj_dhat]
  · show tauhat * aT 5 * tauhat⁻¹ = Psi (Pi.single 5 1)
    rw [Psi_single, aT_five, tauhat_conj_dhat]
  · show tauhat * aT 6 * tauhat⁻¹ = Psi (Pi.single 7 1)
    rw [Psi_single, aT_six, aT_seven, tauhat_conj_uhat]
  · show tauhat * aT 7 * tauhat⁻¹ = Psi (Pi.single 6 1 + Pi.single 7 1)
    rw [Psi_add_single, aT_six, aT_seven, tauhat_conj_ghat8]

theorem A8_eq_closure :
    A8 = Subgroup.closure (Set.range aT) := by
  apply le_antisymm
  · rw [← range_PsiHom]
    rintro _ ⟨v, rfl⟩
    have hv : v.toAdd = ∑ k : Fin 8, Pi.single k (v.toAdd k) :=
      (Finset.univ_sum_single v.toAdd).symm
    rw [PsiHom_apply, hv]
    refine Finset.sum_induction _ (fun w => Psi w ∈ Subgroup.closure (Set.range aT))
      (fun a b ha hb => ?_) ?_ fun k _ => ?_
    · rw [Psi_add]
      exact Subgroup.mul_mem _ ha hb
    · rw [show Psi 0 = 1 from map_one PsiHom]
      exact Subgroup.one_mem _
    · rcases zmod2_cases (v.toAdd k) with h0 | h1
      · rw [h0, Pi.single_zero, show Psi 0 = 1 from map_one PsiHom]
        exact Subgroup.one_mem _
      · rw [h1, Psi_single]
        exact Subgroup.subset_closure ⟨k, rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    rw [← Psi_single]
    exact Psi_mem_A8 _

theorem conj_A8_le
    (g : Dfull) (hg : ∀ k, g * aT k * g⁻¹ ∈ A8) :
    ∀ x ∈ A8, g * x * g⁻¹ ∈ A8 := by
  intro x hx
  rw [A8_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    exact hg k
  | one => rw [mul_one, mul_inv_cancel]; exact A8.one_mem
  | mul y z _ _ hy hz =>
    have e : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
    rw [e]
    exact A8.mul_mem hy hz
  | inv y _ hy =>
    have e : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
    rw [e]
    exact A8.inv_mem hy

theorem tauhat_conj_mem_A8 :
    ∀ x ∈ A8, tauhat * x * tauhat⁻¹ ∈ A8 :=
  conj_A8_le tauhat fun k => by
    rw [tauhat_conj_aT]
    exact (aEquiv _).2

theorem tauhat_mem_normalizer_A8 :
    tauhat ∈ Subgroup.normalizer (A8 : Set Dfull) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨tauhat_conj_mem_A8 x, fun h => ?_⟩
  have h2 := tauhat_conj_mem_A8 _ (tauhat_conj_mem_A8 _ h)
  have e : tauhat * (tauhat * (tauhat * x * tauhat⁻¹) * tauhat⁻¹) * tauhat⁻¹ = x := by
    have h3 : tauhat * tauhat * tauhat = 1 := (pow_three' tauhat).symm.trans tauhat_pow_three
    calc tauhat * (tauhat * (tauhat * x * tauhat⁻¹) * tauhat⁻¹) * tauhat⁻¹ =
        (tauhat * tauhat * tauhat) * x * (tauhat * tauhat * tauhat)⁻¹ := by group
      _ = x := by rw [h3, one_mul, inv_one, mul_one]
  rw [e] at h2
  exact h2

theorem short_symplectic_eight_elementary_abelian :
    CFSG.IsElementaryAbelian 2 A8 ∧ Nat.card A8 = 2 ^ 8 ∧
    (∀ k : Fin 8, (aEquiv (Multiplicative.ofAdd (Pi.single k 1)) : Dfull) = aT k) ∧
    A8 ≤ Jhat ∧ A8 ⊓ Ehat = B7 ∧
    (A8.subgroupOf Jhat).map jhatToKv0 = Subgroup.zpowers rK ∧
    (∀ x : Dfull, x ∈ B7 ↔ ∃ h : x ∈ Ehat, psiW ⟨x, h⟩ ∈ Zsp) ∧
    psiW yhatE = decW 31 ∧ psiW (dhatE 2 3) = decW 12288 ∧ psiW (dhatE 2 4) = decW 20480 ∧
    psiW (dhatE 2 5) = decW 36864 ∧ psiW (dhatE 2 6) = decW 69632 ∧
    psiW uhatE = decW 30721 ∧
    LinearIndependent (ZMod 2) bVec ∧ Submodule.span (ZMod 2) (Set.range bVec) = Zsp ∧
    LinearMap.range (wAct v0 rK - 1) = Zsp ∧
    tauhat ∈ Subgroup.normalizer (A8 : Set Dfull) ∧
    (∀ k : Fin 8, tauhat * aT k * tauhat⁻¹ =
      (aEquiv (Multiplicative.ofAdd (bvec 8 (triRows.getD k 0))) : Dfull)) ∧
    tauhat * ghat8 * tauhat⁻¹ = uhat * ghat8 :=
  ⟨isElementaryAbelian_A8, natCard_A8, aEquiv_single, A8_le_Jhat, A8_inf_Ehat, map_A8,
    mem_B7_iff, psiW_yhat8, psiW_d23, psiW_d24, psiW_d25, psiW_d26, psiW_uhat,
    linearIndependent_bVec, span_bVec, range_rK_sub_one, tauhat_mem_normalizer_A8,
    tauhat_conj_aT, tauhat_conj_ghat8⟩

end CFSG.Monster.B.TwoA.Sp8
