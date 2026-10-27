
module


public import CFSG.Monster.B.TwoA.Sp8.T9
public import Certificates.Certificate16001

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def QPres
    (x : Dfull) : Prop :=
  (∀ v : Fin 8 → ZMod 2, ∃ w, x * Psi v * x⁻¹ = Psi w) ∧
  ∀ v : Fin 8 → ZMod 2, ∃ w, x * (cQ * Psi v) * x⁻¹ = cQ * Psi w ∧ qPoly w = qPoly v

theorem qPres_one : QPres 1 :=
  ⟨fun v => ⟨v, by rw [one_mul, inv_one, mul_one]⟩,
    fun v => ⟨v, by rw [one_mul, inv_one, mul_one], rfl⟩⟩

theorem qPres_mul
    {x y : Dfull} (hx : QPres x) (hy : QPres y) : QPres (x * y) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · obtain ⟨w, hw⟩ := hy.1 v
    obtain ⟨w', hw'⟩ := hx.1 w
    refine ⟨w', ?_⟩
    rw [show x * y * Psi v * (x * y)⁻¹ = x * (y * Psi v * y⁻¹) * x⁻¹ by group, hw, hw']
  · obtain ⟨w, hw, hq⟩ := hy.2 v
    obtain ⟨w', hw', hq'⟩ := hx.2 w
    refine ⟨w', ?_, hq'.trans hq⟩
    rw [show x * y * (cQ * Psi v) * (x * y)⁻¹ = x * (y * (cQ * Psi v) * y⁻¹) * x⁻¹ by group, hw,
      hw']

@[expose] def qPresMon :
    Submonoid Dfull where
  carrier := {x | QPres x}
  one_mem' := qPres_one
  mul_mem' := qPres_mul

theorem qPres_inv
    {x : Dfull} (hx : QPres x) : QPres x⁻¹ := by
  have hfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  have h1 : x⁻¹ = x ^ (orderOf x - 1) := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hfin.orderOf_pos,
      pow_orderOf_eq_one]
  rw [h1]
  exact qPresMon.pow_mem (show x ∈ qPresMon from hx) _

@[expose] def qPresGrp :
    Subgroup Dfull :=
  { qPresMon with inv_mem' := qPres_inv }

theorem mem_qPresGrp
    {x : Dfull} : x ∈ qPresGrp ↔ QPres x := Iff.rfl

theorem conj_Psi_of_rows
    {h : Dfull} {M : Fin 8 → Fin 8 → ZMod 2}
    (hrow : ∀ j, h * aT j * h⁻¹ = Psi (M j)) (v : Fin 8 → ZMod 2) :
    h * Psi v * h⁻¹ = Psi (∑ j, v j • M j) := by
  rw [show v = ∑ k : Fin 8, Pi.single k (v k) from (Finset.univ_sum_single v).symm]
  refine Finset.sum_induction _ (fun u => h * Psi u * h⁻¹ = Psi (∑ j, u j • M j))
    (fun a b ha hb => ?_) ?_ fun k _ => ?_
  · rw [Psi_add, show h * (Psi a * Psi b) * h⁻¹ = (h * Psi a * h⁻¹) * (h * Psi b * h⁻¹) by group,
      ha, hb, ← Psi_add]
    congr 1
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · simp only [Psi_zero', Pi.zero_apply, zero_smul, Finset.sum_const_zero, mul_one,
      mul_inv_cancel]
  · rcases zmod2_cases (v k) with h0 | h1
    · simp only [h0, Pi.single_zero, Psi_zero', Pi.zero_apply, zero_smul, Finset.sum_const_zero,
        mul_one, mul_inv_cancel]
    · rw [h1, Psi_single, hrow k]
      congr 1
      rw [Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, one_smul]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_smul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk

theorem conj_cPsi_of_rows
    {h : Dfull} {M : Fin 8 → Fin 8 → ZMod 2} {t : Fin 8 → ZMod 2}
    (hrow : ∀ j, h * aT j * h⁻¹ = Psi (M j)) (hc : h * cQ * h⁻¹ = cQ * Psi t)
    (v : Fin 8 → ZMod 2) :
    h * (cQ * Psi v) * h⁻¹ = cQ * Psi (t + ∑ j, v j • M j) := by
  rw [show h * (cQ * Psi v) * h⁻¹ = (h * cQ * h⁻¹) * (h * Psi v * h⁻¹) by group, hc,
    conj_Psi_of_rows hrow, mul_assoc, ← Psi_add]

theorem qPres_of_rows
    {h : Dfull} {M : Fin 8 → Fin 8 → ZMod 2} {t : Fin 8 → ZMod 2}
    (hrow : ∀ j, h * aT j * h⁻¹ = Psi (M j)) (hc : h * cQ * h⁻¹ = cQ * Psi t)
    (hq : ∀ v : Fin 8 → ZMod 2, qPoly (t + ∑ j, v j • M j) = qPoly v) : QPres h :=
  ⟨fun v => ⟨_, conj_Psi_of_rows hrow v⟩, fun v => ⟨_, conj_cPsi_of_rows hrow hc v, hq v⟩⟩

theorem tauhat_conj_cQ :
    tauhat * cQ * tauhat⁻¹ = cQ * Psi 0 := by
  rw [Psi_zero', mul_one]
  exact tauhat_conj_dhat 0 2

theorem tauhat_conj_aT_triM
    (j : Fin 8) : tauhat * aT j * tauhat⁻¹ = Psi (triM j) := by
  rw [tauhat_conj_aT, coe_aEquiv, toAdd_ofAdd]
  rfl

theorem triM_qPoly :
    ∀ v : Fin 8 → ZMod 2, qPoly (0 + ∑ j, v j • triM j) = qPoly v :=
  Certificates.certificate16001

theorem qPres_tauhat :
    QPres tauhat :=
  qPres_of_rows tauhat_conj_aT_triM tauhat_conj_cQ triM_qPoly

end CFSG.Monster.B.TwoA.Sp8
