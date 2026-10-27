module

public import CFSG.Sporadic.Th.Recog.GlueFacts

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords
open Equiv Equiv.Perm

section Basic

noncomputable abbrev cM : ↥Max3.M := ⟨hswJ 2, hswJ_mem_M 2 (by decide)⟩

noncomputable abbrev dM : ↥Max3.M := ⟨hswJ 3, hswJ_mem_M 3 (by decide)⟩

noncomputable abbrev eM : ↥Max3.M := ⟨hswJ 4, hswJ_mem_M 4 (by decide)⟩

noncomputable abbrev uM : ↥Max3.M := ⟨hswJ 7, hswJ_mem_M 7 (by decide)⟩

@[expose] noncomputable def ω₁ : ↥Max3.M := dM * eM

@[expose] noncomputable def ω₂ : ↥Max3.M := uM * ω₁ * uM⁻¹

@[expose] noncomputable def x₁ : ↥Max3.M := (cM * dM) ^ 2

@[expose] noncomputable def y₁ : ↥Max3.M := ω₁ * x₁ * ω₁⁻¹

@[expose] noncomputable def x₂ : ↥Max3.M := uM * x₁ * uM⁻¹

@[expose] noncomputable def y₂ : ↥Max3.M := uM * y₁ * uM⁻¹

@[expose] noncomputable def e₀ : ↥Max3.M := dM * cM * dM

@[expose] noncomputable def e₁ : ↥Max3.M := uM * e₀ * uM⁻¹

@[expose] noncomputable def e8 (l : Fin 8) : ↥Max3.M :=
  zM ^ (l.val % 2) * e₀ ^ (l.val / 2 % 2) * e₁ ^ (l.val / 4)

@[expose] noncomputable def nE : Fin 5 → ↥Max3.M :=
  ![cM, dM * eM * uM * dM * uM⁻¹, dM * eM * uM * dM * uM, dM * uM * dM * uM,
    dM * uM * dM * uM⁻¹]

@[expose] noncomputable def cE : Fin 7 → ↥Max3.M :=
  ![1, sLetter, sLetter ^ 6, sLetter ^ 2, sLetter * tLetter ^ 2, sLetter ^ 5,
    sLetter ^ 6 * tLetter ^ 2]

@[expose] noncomputable def cN : Fin 6 → ↥Max3.M :=
  ![dM * eM * uM * dM, sLetter, sLetter ^ 2, sLetter ^ 3, dM * eM * dM * tLetter,
    sLetter * dM * eM * dM * sLetter]

theorem kap_cM : Max3.InvRep.kap cM = 1 := by
  apply Subtype.ext
  rw [show cM = (⟨hswJ 2, hswJ_mem_M 2 (by decide)⟩ : ↥Max3.M) from rfl]
  rw [kap_hswJ 2 (by decide)]
  ext x
  fin_cases x <;> decide +kernel

theorem coe_kap_dM : (Max3.InvRep.kap dM : Perm (Fin 9)) =
    swap 0 4 * swap 1 7 * swap 2 8 * swap 3 5 := by
  rw [show dM = (⟨hswJ 3, hswJ_mem_M 3 (by decide)⟩ : ↥Max3.M) from rfl]
  rw [kap_hswJ 3 (by decide)]
  ext x
  fin_cases x <;> decide +kernel

theorem coe_kap_eM : (Max3.InvRep.kap eM : Perm (Fin 9)) =
    swap 0 2 * swap 1 8 * swap 3 6 * swap 4 7 := by
  rw [show eM = (⟨hswJ 4, hswJ_mem_M 4 (by decide)⟩ : ↥Max3.M) from rfl]
  rw [kap_hswJ 4 (by decide)]
  ext x
  fin_cases x <;> decide +kernel

theorem coe_kap_uM : (Max3.InvRep.kap uM : Perm (Fin 9)) =
    swap 0 8 * swap 1 2 := by
  rw [show uM = (⟨hswJ 7, hswJ_mem_M 7 (by decide)⟩ : ↥Max3.M) from rfl]
  rw [kap_hswJ 7 (by decide)]
  ext x
  fin_cases x <;> decide +kernel

theorem coe_kap_tLetter : (Max3.InvRep.kap tLetter : Perm (Fin 9)) =
    swap 0 7 * swap 0 8 * (swap 1 2 * swap 1 4) := by
  rw [show tLetter = (⟨hswJ 6, hswJ_mem_M 6 (by decide)⟩ : ↥Max3.M) from rfl]
  rw [kap_hswJ 6 (by decide)]
  ext x
  fin_cases x <;> decide +kernel

private theorem isThreeCycle_swap_0_7_mul_0_8 :
    (swap 0 7 * swap 0 8 : Perm (Fin 9)).IsThreeCycle := by
  rw [show swap 0 7 * swap 0 8 = ([0, 8, 7] : List (Fin 9)).formPerm by
    ext x
    fin_cases x <;> decide +kernel]
  rw [IsThreeCycle]
  rw [(List.isCycle_formPerm (l := [0, 8, 7]) (by decide) (by decide)).cycleType]
  rw [show ((([0, 8, 7] : List (Fin 9)).formPerm).support.card) = 3 by decide +kernel]

private theorem isThreeCycle_swap_1_2_mul_1_4 :
    (swap 1 2 * swap 1 4 : Perm (Fin 9)).IsThreeCycle := by
  rw [show swap 1 2 * swap 1 4 = ([1, 4, 2] : List (Fin 9)).formPerm by
    ext x
    fin_cases x <;> decide +kernel]
  rw [IsThreeCycle]
  rw [(List.isCycle_formPerm (l := [1, 4, 2]) (by decide) (by decide)).cycleType]
  rw [show ((([1, 4, 2] : List (Fin 9)).formPerm).support.card) = 3 by decide +kernel]

theorem cycleType_kap_tLetter :
    (Max3.InvRep.kap tLetter : Perm (Fin 9)).cycleType = {3, 3} := by
  rw [coe_kap_tLetter]
  have hd : Equiv.Perm.Disjoint (swap (0 : Fin 9) 7 * swap 0 8)
      (swap 1 2 * swap 1 4) := by
    intro x
    fin_cases x <;> decide +kernel
  rw [Equiv.Perm.Disjoint.cycleType_mul hd,
    isThreeCycle_swap_0_7_mul_0_8.cycleType, isThreeCycle_swap_1_2_mul_1_4.cycleType]
  rfl

private def relCD : List (Fin 8 × Bool) :=
  [(0, true), (3, false), (2, false), (3, false), (2, false), (3, false), (2, false), (3, false),
    (2, false)]

private def relDE : List (Fin 8 × Bool) :=
  [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)]

private def relU2 : List (Fin 8 × Bool) :=
  [(7, true), (7, true), (2, false), (0, false)]

private def relUC : List (Fin 8 × Bool) :=
  [(7, false), (2, false), (7, true), (2, true)]

private theorem mem_relWords_R0' {w : List (Fin 8 × Bool)}
    (hw : w ∈ [relCD, relDE, relU2, relUC]) : w ∈ R0' := by
  have hall : ([relCD, relDE, relU2, relUC] : List (List (Fin 8 × Bool))).all
      (fun w => decide (w ∈ R0')) = true := by
    simp only [relCD, relDE, relU2, relUC, R0', TauCeti.GroupPresentation.relators_def,
      TauCeti.Sporadic.Thompson.presentation, TauCeti.Sporadic.Thompson.relatorList,
      TauCeti.Sporadic.Thompson.relatorsOne, TauCeti.Sporadic.Thompson.relatorsTwo,
      TauCeti.Sporadic.Thompson.relatorsThree, TauCeti.Sporadic.Thompson.relatorsFour,
      TauCeti.Sporadic.Thompson.relatorsFive, TauCeti.Sporadic.Thompson.relatorsSix,
      TauCeti.Sporadic.Thompson.genA, TauCeti.Sporadic.Thompson.genB,
      TauCeti.Sporadic.Thompson.genC, TauCeti.Sporadic.Thompson.genD,
      TauCeti.Sporadic.Thompson.genE, TauCeti.Sporadic.Thompson.genS,
      TauCeti.Sporadic.Thompson.genT, TauCeti.Sporadic.Thompson.genU,
      TauCeti.Relator.toWord_gen, TauCeti.Relator.toWord_pow, TauCeti.Relator.toWord_mul,
      TauCeti.Relator.toWord_inv, TauCeti.Relator.toWord_div, TauCeti.Relator.toWord_conj,
      TauCeti.Relator.toWord_commInvInv, List.map_cons, List.map_append, List.map_nil]
    decide
  exact of_decide_eq_true (List.all_eq_true.mp hall w hw)

private theorem inv_hswJ_zero : (hswJ 0)⁻¹ = hswJ 0 :=
  inv_eq_of_mul_eq_one_right (hswJ_mul_self 0 (by decide))

private theorem inv_hswJ_two : (hswJ 2)⁻¹ = hswJ 2 :=
  inv_eq_of_mul_eq_one_right (hswJ_mul_self 2 (by decide))

private theorem inv_hswJ_three : (hswJ 3)⁻¹ = hswJ 3 :=
  inv_eq_of_mul_eq_one_right (hswJ_mul_self 3 (by decide))

private theorem coe_cM : ((cM : ↥Max3.M) : J) = hswJ 2 := rfl

private theorem coe_dM : ((dM : ↥Max3.M) : J) = hswJ 3 := rfl

private theorem coe_eM : ((eM : ↥Max3.M) : J) = hswJ 4 := rfl

private theorem coe_uM : ((uM : ↥Max3.M) : J) = hswJ 7 := rfl

private theorem coe_zM : ((zM : ↥Max3.M) : J) = hswJ 0 := by
  change (Max3.z : J) = hswJ 0
  rw [Max3.z_eq_a, ← hswJ_zero]

private theorem zM_comm (x : ↥Max3.M) : Commute zM x := by
  apply Subtype.ext
  change (Max3.z : J) * (x : J) = (x : J) * Max3.z
  exact (Max3.commute_z_of_mem_M x.2).eq

private theorem wprod_relCD :
    wprod hswJ relCD = hswJ 0 * (hswJ 3)⁻¹ * (hswJ 2)⁻¹ * (hswJ 3)⁻¹ * (hswJ 2)⁻¹ *
      (hswJ 3)⁻¹ * (hswJ 2)⁻¹ * (hswJ 3)⁻¹ * (hswJ 2)⁻¹ := by
  simp only [relCD, wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, Bool.false_eq_true, if_false, mul_one]
  group

private theorem wprod_relDE :
    wprod hswJ relDE = hswJ 3 * hswJ 4 * hswJ 3 * hswJ 4 * hswJ 3 * hswJ 4 := by
  simp only [relDE, wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, Bool.false_eq_true, if_false, mul_one]
  group

private theorem wprod_relU2 :
    wprod hswJ relU2 = hswJ 7 * hswJ 7 * (hswJ 2)⁻¹ * (hswJ 0)⁻¹ := by
  simp only [relU2, wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, Bool.false_eq_true, if_false, mul_one]
  group

private theorem wprod_relUC :
    wprod hswJ relUC = (hswJ 7)⁻¹ * ((hswJ 2)⁻¹ * (hswJ 7 * hswJ 2)) := by
  simp only [relUC, wprod, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    if_true, Bool.false_eq_true, if_false, mul_one]

private theorem dM_conj_cM_mul_dM : dM * (cM * dM) * dM = (cM * dM)⁻¹ := by
  apply Subtype.ext
  change hswJ 3 * (hswJ 2 * hswJ 3) * hswJ 3 = (hswJ 2 * hswJ 3)⁻¹
  rw [mul_inv_rev, inv_hswJ_three, inv_hswJ_two]
  simp [mul_assoc, hswJ_mul_self 3 (by decide)]

theorem cM_mul_dM_pow_four : (cM * dM) ^ 4 = zM := by
  have hw : wprod hswJ relCD = 1 := wprod_hswJ_of_mem (mem_relWords_R0' (by simp))
  rw [wprod_relCD, inv_hswJ_three, inv_hswJ_two] at hw
  have h1 : hswJ 0 * (hswJ 3 * hswJ 2) ^ 4 = 1 := by
    rw [← hw]
    simp [pow_succ, pow_two, mul_assoc]
  have h2 : (hswJ 3 * hswJ 2) ^ 4 = hswJ 0 := by
    simpa [inv_hswJ_zero] using
      @eq_inv_of_mul_eq_one_right J (inferInstance : DivisionMonoid J) (hswJ 0)
        ((hswJ 3 * hswJ 2) ^ 4) h1
  have h3 : (hswJ 2 * hswJ 3) ^ 4 = hswJ 0 := by
    rw [show hswJ 2 * hswJ 3 = (hswJ 3 * hswJ 2)⁻¹ from by
      rw [mul_inv_rev, inv_hswJ_three, inv_hswJ_two]]
    rw [inv_pow, h2, inv_hswJ_zero]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_cM, coe_dM, coe_zM]
  exact h3

theorem dM_mul_eM_pow_three : (dM * eM) ^ 3 = 1 := by
  have hw : wprod hswJ relDE = 1 := wprod_hswJ_of_mem (mem_relWords_R0' (by simp))
  rw [wprod_relDE] at hw
  have h : (hswJ 3 * hswJ 4) ^ 3 = 1 := by
    rw [← hw]
    simp [pow_succ, pow_two, mul_assoc]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_dM, coe_eM, Subgroup.coe_one]
  exact h

theorem uM_pow_two : uM ^ 2 = zM * cM := by
  have hw : wprod hswJ relU2 = 1 := wprod_hswJ_of_mem (mem_relWords_R0' (by simp))
  rw [wprod_relU2, inv_hswJ_zero, inv_hswJ_two] at hw
  have h : (hswJ 7 * hswJ 7) * (hswJ 2 * hswJ 0) = 1 := by
    rw [← hw]
    group
  have h' : hswJ 7 * hswJ 7 = hswJ 0 * hswJ 2 := by
    rw [@eq_inv_of_mul_eq_one_left J (inferInstance : DivisionMonoid J) (hswJ 7 * hswJ 7)
      (hswJ 2 * hswJ 0) h, mul_inv_rev, inv_hswJ_zero, inv_hswJ_two]
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_two, coe_uM, Subgroup.coe_mul, coe_zM, coe_cM]
  exact h'

theorem uM_comm_cM : uM * cM = cM * uM := by
  have hw : wprod hswJ relUC = 1 := wprod_hswJ_of_mem (mem_relWords_R0' (by simp))
  rw [wprod_relUC, inv_hswJ_two] at hw
  have hw' : (hswJ 7)⁻¹ * hswJ 2 * hswJ 7 * hswJ 2 = 1 := by
    rw [← hw]
    group
  have h1 : (hswJ 7)⁻¹ * hswJ 2 * hswJ 7 = hswJ 2 := by
    rw [@eq_inv_of_mul_eq_one_left J (inferInstance : DivisionMonoid J)
      ((hswJ 7)⁻¹ * hswJ 2 * hswJ 7) (hswJ 2) hw', inv_hswJ_two]
  have h' : hswJ 7 * hswJ 2 = hswJ 2 * hswJ 7 := by
    calc hswJ 7 * hswJ 2 = hswJ 7 * ((hswJ 7)⁻¹ * hswJ 2 * hswJ 7) := by rw [h1]
      _ = hswJ 2 * hswJ 7 := by group
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_uM, coe_cM]
  exact h'

theorem cM_mul_self : cM * cM = 1 := Subtype.ext (hswJ_mul_self 2 (by decide))

theorem dM_mul_self : dM * dM = 1 := Subtype.ext (hswJ_mul_self 3 (by decide))

theorem eM_mul_self : eM * eM = 1 := Subtype.ext (hswJ_mul_self 4 (by decide))

theorem dM_inv : dM⁻¹ = dM :=
  inv_eq_of_mul_eq_one_right dM_mul_self

theorem eM_inv : eM⁻¹ = eM :=
  inv_eq_of_mul_eq_one_right eM_mul_self

theorem cM_comm_tLetter : cM * tLetter = tLetter * cM := by
  apply Subtype.ext
  change hswJ 2 * hswJ 6 = hswJ 6 * hswJ 2
  exact hswJ_comm_six 2 (by decide)

theorem dM_comm_tLetter : dM * tLetter = tLetter * dM := by
  apply Subtype.ext
  change hswJ 3 * hswJ 6 = hswJ 6 * hswJ 3
  exact hswJ_comm_six 3 (by decide)

theorem eM_comm_tLetter : eM * tLetter = tLetter * eM := by
  apply Subtype.ext
  change hswJ 4 * hswJ 6 = hswJ 6 * hswJ 4
  exact hswJ_comm_six 4 (by decide)

theorem uM_conj_tLetter : uM * tLetter * uM⁻¹ = tLetter⁻¹ := by
  apply Subtype.ext
  change hswJ 7 * hswJ 6 * (hswJ 7)⁻¹ = (hswJ 6)⁻¹
  exact hswJ_seven_conj_six

theorem uM_mul_tLetter : uM * tLetter = tLetter⁻¹ * uM := by
  calc uM * tLetter = (uM * tLetter * uM⁻¹) * uM := by group
    _ = tLetter⁻¹ * uM := by rw [uM_conj_tLetter]

theorem x₁_pow_two : x₁ ^ 2 = zM := by
  rw [x₁, ← pow_mul, show 2 * 2 = 4 by norm_num, cM_mul_dM_pow_four]

theorem ω₁_pow_three : ω₁ ^ 3 = 1 := by
  rw [ω₁, dM_mul_eM_pow_three]

theorem coe_kap_ω₁ : (Max3.InvRep.kap ω₁ : Perm (Fin 9)) =
    swap 0 4 * swap 1 7 * swap 2 8 * swap 3 5 *
      (swap 0 2 * swap 1 8 * swap 3 6 * swap 4 7) := by
  rw [ω₁, map_mul, Subgroup.coe_mul, coe_kap_dM, coe_kap_eM]

theorem coe_kap_ω₂ : (Max3.InvRep.kap ω₂ : Perm (Fin 9)) =
    swap 0 8 * swap 1 2 * (swap 0 4 * swap 1 7 * swap 2 8 * swap 3 5 *
      (swap 0 2 * swap 1 8 * swap 3 6 * swap 4 7)) * (swap 0 8 * swap 1 2)⁻¹ := by
  rw [ω₂, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_kap_uM, coe_kap_ω₁]

private theorem ω₁_ne_one : ω₁ ≠ 1 := by
  intro h
  have hk : (Max3.InvRep.kap ω₁ : Perm (Fin 9)) = 1 := by rw [h, map_one]; rfl
  have h0 : (Max3.InvRep.kap ω₁ : Perm (Fin 9)) 0 = 8 := by
    rw [coe_kap_ω₁]
    decide +kernel
  rw [hk] at h0
  exact absurd h0 (by decide +kernel)

theorem orderOf_ω₁ : orderOf ω₁ = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime ω₁_pow_three ω₁_ne_one

theorem uM_pow_four : uM ^ 4 = 1 := by
  have hzc : Commute zM cM := zM_comm cM
  have h2 : (zM * cM) ^ 2 = 1 := by
    rw [@Commute.mul_pow ↥Max3.M (inferInstance : Monoid ↥Max3.M) zM cM hzc 2,
      show zM ^ 2 = 1 by rw [pow_two, zM_mul_self],
      show cM ^ 2 = 1 by rw [pow_two, cM_mul_self], mul_one]
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, uM_pow_two, h2]

theorem uM_inv : uM⁻¹ = uM ^ 3 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ', show 3 + 1 = 4 by norm_num, uM_pow_four]

theorem tLetter_mul_uM_sq : (tLetter * uM) ^ 2 = uM ^ 2 := by
  rw [pow_two, pow_two]
  calc tLetter * uM * (tLetter * uM)
      = (tLetter * (uM * tLetter * uM⁻¹)) * (uM * uM) := by group
    _ = (tLetter * tLetter⁻¹) * (uM * uM) := by rw [uM_conj_tLetter]
    _ = uM * uM := by group

theorem dM_conj_x₁ : dM * x₁ * dM = x₁⁻¹ := by
  have hconj : MulAut.conj (G := ↥Max3.M) dM (cM * dM) = (cM * dM)⁻¹ := by
    rw [MulAut.conj_apply, dM_inv]
    exact dM_conj_cM_mul_dM
  rw [x₁]
  calc dM * (cM * dM) ^ 2 * dM
      = MulAut.conj (G := ↥Max3.M) dM ((cM * dM) ^ 2) := by
        rw [MulAut.conj_apply, dM_inv]
    _ = ((cM * dM) ^ 2)⁻¹ := by rw [map_pow, hconj, inv_pow]

theorem dM_conj_ω₁ : dM * ω₁ * dM = ω₁⁻¹ := by
  rw [ω₁]
  calc dM * (dM * eM) * dM = eM * dM := by
        rw [← mul_assoc, dM_mul_self, one_mul]
    _ = (dM * eM)⁻¹ := by rw [mul_inv_rev, dM_inv, eM_inv]

theorem cM_ne_one : cM ≠ 1 := by
  intro h
  have h4 := cM_mul_dM_pow_four
  rw [h, one_mul] at h4
  have hd2 : dM ^ 2 = 1 := by rw [pow_two, dM_mul_self]
  have hd4 : dM ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hd2, one_pow]
  rw [hd4] at h4
  exact zM_ne_one h4.symm

theorem cM_ne_zM : cM ≠ zM := by
  intro h
  have h4 := cM_mul_dM_pow_four
  rw [h] at h4
  have hcomm : Commute zM dM := zM_comm dM
  have h2 : (zM * dM) ^ 2 = 1 := by
    rw [@Commute.mul_pow ↥Max3.M (inferInstance : Monoid ↥Max3.M) zM dM hcomm 2,
      show zM ^ 2 = 1 by rw [pow_two, zM_mul_self],
      show dM ^ 2 = 1 by rw [pow_two, dM_mul_self], mul_one]
  have hz4 : (zM * dM) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2, one_pow]
  rw [hz4] at h4
  exact zM_ne_one h4.symm

private theorem e₀_eq_conj : e₀ = MulAut.conj (G := ↥Max3.M) dM cM := by
  rw [e₀, MulAut.conj_apply, dM_inv]

theorem e₀_mul_self : e₀ * e₀ = 1 := by
  rw [e₀_eq_conj, ← map_mul, cM_mul_self, map_one]

theorem e₀_ne_one : e₀ ≠ 1 := by
  intro h
  have hconj : MulAut.conj (G := ↥Max3.M) dM cM = 1 := by rw [← e₀_eq_conj, h]
  have hc : cM = 1 := (MulAut.conj (G := ↥Max3.M) dM).injective (by
    simpa using hconj)
  exact cM_ne_one hc

theorem coe_e₀_ne_z : (e₀ : J) ≠ Max3.z := by
  intro h
  have he : e₀ = zM := Subtype.ext (by simpa [coe_zM] using h)
  have hc_eq : dM * e₀ * dM = cM := by
    rw [e₀]
    calc dM * (dM * cM * dM) * dM = (dM * dM) * cM * (dM * dM) := by group
      _ = cM := by rw [dM_mul_self, one_mul, mul_one]
  have hcomm : Commute zM dM := zM_comm dM
  have hz : dM * zM * dM = zM := by
    rw [hcomm.eq.symm, mul_assoc, dM_mul_self, mul_one]
  have hc : cM = zM := by rw [← hc_eq, he, hz]
  exact cM_ne_zM hc

private theorem kap_x₁ : Max3.InvRep.kap x₁ = 1 := by
  rw [x₁, map_pow, map_mul, kap_cM, one_mul, pow_two, ← map_mul, dM_mul_self, map_one]

private theorem kap_y₁ : Max3.InvRep.kap y₁ = 1 := by
  rw [y₁, map_mul, map_mul, map_inv, kap_x₁, mul_one, mul_inv_cancel]

private theorem kap_x₂ : Max3.InvRep.kap x₂ = 1 := by
  rw [x₂, map_mul, map_mul, map_inv, kap_x₁, mul_one, mul_inv_cancel]

private theorem kap_y₂ : Max3.InvRep.kap y₂ = 1 := by
  rw [y₂, map_mul, map_mul, map_inv, kap_y₁, mul_one, mul_inv_cancel]

private theorem kap_e₀ : Max3.InvRep.kap e₀ = 1 := by
  rw [e₀, map_mul, map_mul, kap_cM, mul_one, ← map_mul, dM_mul_self, map_one]

theorem x₁_mem_Q : (x₁ : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.mp kap_x₁

theorem y₁_mem_Q : (y₁ : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.mp kap_y₁

theorem x₂_mem_Q : (x₂ : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.mp kap_x₂

theorem y₂_mem_Q : (y₂ : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.mp kap_y₂

theorem e₀_mem_Q : (e₀ : J) ∈ Max3.Q := Max3.InvRep.kap_eq_one_iff.mp kap_e₀

theorem x₁_comm_tLetter : x₁ * tLetter = tLetter * x₁ := by
  have hcd : Commute (cM * dM) tLetter :=
    Commute.mul_left (a := cM) (b := dM) (c := tLetter) cM_comm_tLetter dM_comm_tLetter
  have hsq : Commute ((cM * dM) * (cM * dM)) tLetter :=
    Commute.mul_left (a := cM * dM) (b := cM * dM) (c := tLetter) hcd hcd
  simpa only [x₁, pow_two] using hsq.eq

theorem ω₁_comm_tLetter : ω₁ * tLetter = tLetter * ω₁ := by
  simpa only [ω₁] using
    (Commute.mul_left (a := dM) (b := eM) (c := tLetter)
      dM_comm_tLetter eM_comm_tLetter).eq

theorem y₁_comm_tLetter : y₁ * tLetter = tLetter * y₁ := by
  have hx : Commute (ω₁ * x₁) tLetter :=
    Commute.mul_left (a := ω₁) (b := x₁) (c := tLetter) ω₁_comm_tLetter x₁_comm_tLetter
  have hi : Commute ω₁⁻¹ tLetter :=
    Commute.inv_left (a := ω₁) (b := tLetter) ω₁_comm_tLetter
  simpa only [y₁] using
    (Commute.mul_left (a := ω₁ * x₁) (b := ω₁⁻¹) (c := tLetter) hx hi).eq

theorem x₂_comm_tLetter : x₂ * tLetter = tLetter * x₂ := by
  have h := @Commute.conj ↥Max3.M (inferInstance : Group ↥Max3.M)
    x₁ tLetter x₁_comm_tLetter uM
  rw [uM_conj_tLetter] at h
  have h' : Commute (uM * x₁ * uM⁻¹) tLetter :=
    (Commute.inv_left (a := tLetter⁻¹) (b := uM * x₁ * uM⁻¹) h.symm).symm
  simpa only [x₂] using h'.eq

theorem y₂_comm_tLetter : y₂ * tLetter = tLetter * y₂ := by
  have h := @Commute.conj ↥Max3.M (inferInstance : Group ↥Max3.M)
    y₁ tLetter y₁_comm_tLetter uM
  rw [uM_conj_tLetter] at h
  have h' : Commute (uM * y₁ * uM⁻¹) tLetter :=
    (Commute.inv_left (a := tLetter⁻¹) (b := uM * y₁ * uM⁻¹) h.symm).symm
  simpa only [y₂] using h'.eq

theorem ω₂_comm_tLetter : ω₂ * tLetter = tLetter * ω₂ := by
  have h := @Commute.conj ↥Max3.M (inferInstance : Group ↥Max3.M)
    ω₁ tLetter ω₁_comm_tLetter uM
  rw [uM_conj_tLetter] at h
  have h' : Commute (uM * ω₁ * uM⁻¹) tLetter :=
    (Commute.inv_left (a := tLetter⁻¹) (b := uM * ω₁ * uM⁻¹) h.symm).symm
  simpa only [ω₂] using h'.eq

theorem e₀_comm_tLetter : e₀ * tLetter = tLetter * e₀ := by
  have hdc : Commute (dM * cM) tLetter :=
    Commute.mul_left (a := dM) (b := cM) (c := tLetter) dM_comm_tLetter cM_comm_tLetter
  have hdi : Commute dM⁻¹ tLetter :=
    Commute.inv_left (a := dM) (b := tLetter) dM_comm_tLetter
  simpa only [e₀, dM_inv] using
    (Commute.mul_left (a := dM * cM) (b := dM⁻¹) (c := tLetter) hdc hdi).eq

theorem e₁_comm_tLetter : e₁ * tLetter = tLetter * e₁ := by
  have h := @Commute.conj ↥Max3.M (inferInstance : Group ↥Max3.M)
    e₀ tLetter e₀_comm_tLetter uM
  rw [uM_conj_tLetter] at h
  have h' : Commute (uM * e₀ * uM⁻¹) tLetter :=
    (Commute.inv_left (a := tLetter⁻¹) (b := uM * e₀ * uM⁻¹) h.symm).symm
  simpa only [e₁] using h'.eq

end Basic

end CFSG.Sporadic.Th.Recog.MFactsB
