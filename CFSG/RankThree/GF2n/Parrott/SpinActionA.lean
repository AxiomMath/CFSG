module

public import CFSG.RankThree.GF2n.Parrott.SpinAction
public import CFSG.RankThree.GF2n.Parrott.PSp43Model
public import Certificates.Certificate946007
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups
open CFSG.GH74.Exceptional CFSG.LieType.Multipliers
open scoped Matrix

local notation "P45" => Equiv.Perm (Fin 45)


local notation "Q45" => QP45.originalSubgroup
local notation "A45" => QA45.originalSubgroup
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)

theorem f45_sq : f45 * f45 = 1 := Certificates.certificate946007.f_sq

theorem f45_inv : f45⁻¹ = f45 := inv_eq_of_mul_eq_one_right f45_sq

theorem f45_conj_x : f45 * x45 * f45 = x45 := by
  have h := (CFSG.Certificates.schreierPermEq_eq_true_iff
    (f45 * x45 * f45) (evalW x45 y45 conjWordX)).1 Certificates.certificate946007.f_conj_x
  simpa [conjWordX, evalW] using h

theorem f45_conj_y : f45 * y45 * f45 = evalW x45 y45 conjWordY :=
  (CFSG.Certificates.schreierPermEq_eq_true_iff
    (f45 * y45 * f45) (evalW x45 y45 conjWordY)).1 Certificates.certificate946007.f_conj_y

theorem f45_not_mem_Q : f45 ∉ Q45 := by
  rw [mem_iff_sift QP45 QP45_ok]
  exact Certificates.certificate946007.f_not_mem_Q

theorem basis_apply (e : Fin 8) : basis e = Pi.single e 1 := rfl

theorem mat_eq_one_of_bitSq {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : ∀ e : Fin 8, bitSq M (1 <<< (e : Nat)) = 1 <<< (e : Nat)) : M * M = 1 := by
  refine Matrix.ext_of_mulVec_single (M := M * M) (N := 1) (fun e => ?_)
  rw [← basis_apply e]
  apply bitmask_injective
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  rw [← bitRow_bitmask M (M *ᵥ basis e), ← bitRow_bitmask M (basis e), bitmask_basis e]
  exact h e

theorem mat_eq_of_bitConj {M N : Matrix (Fin 8) (Fin 8) (ZMod 2)} {w : List Bool}
    (h : ∀ e : Fin 8, bitConj M N (1 <<< (e : Nat)) = bitWord (toSpinWord w) (1 <<< (e : Nat))) :
    M * N * M = matWord (toSpinWord w) := by
  refine Matrix.ext_of_mulVec_single (M := M * N * M) (N := matWord (toSpinWord w)) (fun e => ?_)
  rw [← basis_apply e]
  apply bitmask_injective
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [← bitRow_bitmask M (N *ᵥ (M *ᵥ basis e)), ← bitRow_bitmask N (M *ᵥ basis e),
    ← bitRow_bitmask M (basis e), bitmask_basis e]
  rw [← evalSpinWordV_eq_matWord_mulVec, ← bitWord_bitmask, bitmask_basis e]
  exact h e

theorem Mf_mul_Mf : Mf * Mf = 1 := mat_eq_one_of_bitSq Certificates.certificate946007.Mf_sq

theorem Mf_conj_Mx : Mf * Mx * Mf = matWord (toSpinWord conjWordX) :=
  mat_eq_of_bitConj Certificates.certificate946007.Mf_conj_Mx

theorem Mf_conj_My : Mf * My * Mf = matWord (toSpinWord conjWordY) :=
  mat_eq_of_bitConj Certificates.certificate946007.Mf_conj_My

@[expose] def MfUnit : GL8 :=
  ⟨Mf, Mf, Mf_mul_Mf, Mf_mul_Mf⟩

theorem MfUnit_val : (MfUnit : Matrix (Fin 8) (Fin 8) (ZMod 2)) = Mf := rfl

theorem MfUnit_mul_MfUnit : MfUnit * MfUnit = 1 := by
  apply Units.ext
  simp [MfUnit, Mf_mul_Mf]

theorem MfUnit_inv : MfUnit⁻¹ = MfUnit := inv_eq_of_mul_eq_one_right MfUnit_mul_MfUnit

theorem coe_evalW_genUnit (w : List Bool) :
    ((evalW MxUnit MyUnit w : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      matWord (toSpinWord w) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b
      · change (MxUnit * evalW MxUnit MyUnit w : GL8).val = matWord (toSpinWord (false :: w))
        rw [Units.val_mul, ih]
        rfl
      · change (MyUnit * evalW MxUnit MyUnit w : GL8).val = matWord (toSpinWord (true :: w))
        rw [Units.val_mul, ih]
        rfl

theorem x45_mem_Q : x45 ∈ Q45 := by
  rw [QP45_closure]
  exact Subgroup.subset_closure (by simp)

theorem y45_mem_Q : y45 ∈ Q45 := by
  rw [QP45_closure]
  exact Subgroup.subset_closure (by simp)

theorem f45_mem_A : f45 ∈ A45 := by
  rw [QA45_closure]
  exact Subgroup.subset_closure (by simp)

theorem Q45_le_A45 : Q45 ≤ A45 := by
  rw [QP45_closure]
  rw [Subgroup.closure_le]
  intro g hg
  rw [QA45_closure]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem evalW_mem_Q (w : List Bool) : evalW x45 y45 w ∈ Q45 := by
  induction w with
  | nil => exact Subgroup.one_mem Q45
  | cons b w ih =>
      cases b
      · simpa [evalW] using Subgroup.mul_mem Q45 x45_mem_Q ih
      · simpa [evalW] using Subgroup.mul_mem Q45 y45_mem_Q ih

theorem psi_s43_eq (i : Fin 45) : psi (s43 i) = tauPerm i := by
  ext j
  rw [psi_s43]
  rfl

theorem psi_xElt : psi U42.xElt = x45 := by
  rw [show U42.xElt = s43 0 from rfl, psi_s43_eq]
  rfl

theorem psi_yElt : psi U42.yElt = y45 := by
  rw [show U42.yElt = ((U42.bIdx).map s43).prod from rfl, y45, map_list_prod, List.map_map]
  change ((U42.bIdx).map (fun i => psi (s43 i))).prod = _
  rw [U42.bIdx]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [psi_s43_eq, psi_s43_eq, psi_s43_eq, psi_s43_eq]
  simp [mul_assoc]

theorem coe_psp43EquivP (g : PSp43) : (psp43EquivP g : P45) = psi g := rfl

theorem psp43EquivP_xElt : psp43EquivP U42.xElt = ⟨x45, x45_mem_Q⟩ := by
  apply Subtype.ext
  rw [coe_psp43EquivP, psi_xElt]

theorem psp43EquivP_yElt : psp43EquivP U42.yElt = ⟨y45, y45_mem_Q⟩ := by
  apply Subtype.ext
  rw [coe_psp43EquivP, psi_yElt]

theorem psp43EquivP_evalW (w : List Bool) :
    psp43EquivP (evalW U42.xElt U42.yElt w) = ⟨evalW x45 y45 w, evalW_mem_Q w⟩ := by
  apply Subtype.ext
  rw [coe_psp43EquivP, CFSG.GH74.KGroups.map_evalW, psi_xElt, psi_yElt]

theorem conj_x_mem_Q : f45 * x45 * f45⁻¹ ∈ Q45 := by
  rw [f45_inv, f45_conj_x]
  exact x45_mem_Q

theorem conj_y_mem_Q : f45 * y45 * f45⁻¹ ∈ Q45 := by
  rw [f45_inv, f45_conj_y]
  exact evalW_mem_Q conjWordY

theorem conj_mem_Q (q : Q45) : f45 * (q : P45) * f45⁻¹ ∈ Q45 := by
  have hmap : Subgroup.map (MulAut.conj f45).toMonoidHom Q45 ≤ Q45 := by
    rw [QP45_closure, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · have hx := conj_x_mem_Q
      rw [QP45_closure] at hx
      simpa [MulAut.conj_apply] using hx
    · have hy := conj_y_mem_Q
      rw [QP45_closure] at hy
      simpa [MulAut.conj_apply] using hy
  have hq : (MulAut.conj f45) (q : P45) ∈ Subgroup.map (MulAut.conj f45).toMonoidHom Q45 :=
    ⟨q, q.2, rfl⟩
  simpa [MulAut.conj_apply] using hmap hq

@[expose] noncomputable def alpha : MulAut Q45 where
  toFun q := ⟨f45 * (q : P45) * f45⁻¹, conj_mem_Q q⟩
  invFun q := ⟨f45 * (q : P45) * f45⁻¹, conj_mem_Q q⟩
  left_inv q := by
    apply Subtype.ext
    change f45 * (f45 * (q : P45) * f45⁻¹) * f45⁻¹ = (q : P45)
    calc f45 * (f45 * (q : P45) * f45⁻¹) * f45⁻¹
        = (f45 * f45) * (q : P45) * (f45⁻¹ * f45⁻¹) := by group
      _ = (q : P45) := by simp [f45_sq, f45_inv]
  right_inv q := by
    apply Subtype.ext
    change f45 * (f45 * (q : P45) * f45⁻¹) * f45⁻¹ = (q : P45)
    calc f45 * (f45 * (q : P45) * f45⁻¹) * f45⁻¹
        = (f45 * f45) * (q : P45) * (f45⁻¹ * f45⁻¹) := by group
      _ = (q : P45) := by simp [f45_sq, f45_inv]
  map_mul' q r := by
    apply Subtype.ext
    change f45 * ((q : P45) * (r : P45)) * f45⁻¹ =
      (f45 * (q : P45) * f45⁻¹) * (f45 * (r : P45) * f45⁻¹)
    simp [mul_assoc]

theorem alpha_apply (q : Q45) : (alpha q : P45) = f45 * (q : P45) * f45⁻¹ := rfl

theorem alpha_mul_alpha : alpha * alpha = 1 := by
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change f45 * (f45 * (q : P45) * f45⁻¹) * f45⁻¹ = (q : P45)
  calc f45 * (f45 * (q : P45) * f45⁻¹) * f45⁻¹
      = (f45 * f45) * (q : P45) * (f45⁻¹ * f45⁻¹) := by group
    _ = (q : P45) := by simp [f45_sq, f45_inv]

inductive C2 : Type
  | e
  | t
  deriving DecidableEq

namespace C2

@[expose] def mul : C2 → C2 → C2
  | e, x => x
  | t, e => t
  | t, t => e

@[expose] def inv : C2 → C2
  | e => e
  | t => t

instance : Group C2 where
  mul := mul
  one := e
  inv := inv
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

instance : Fintype C2 :=
  ⟨{e, t}, by intro x; cases x <;> simp⟩

end C2

theorem card_C2 : Nat.card C2 = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

@[expose] noncomputable def alphaFun : C2 → MulAut Q45
  | C2.e => 1
  | C2.t => alpha

theorem alphaFun_e : alphaFun C2.e = 1 := rfl
theorem alphaFun_t : alphaFun C2.t = alpha := rfl

theorem C2.mul_eq (b c : C2) : b * c = C2.mul b c := by
  cases b <;> cases c <;> rfl

@[expose] noncomputable def alphaHom : C2 →* MulAut Q45 where
  toFun := alphaFun
  map_one' := alphaFun_e
  map_mul' b c := by
    rw [C2.mul_eq]
    cases b with
    | e =>
      cases c with
      | e => change alphaFun C2.e = alphaFun C2.e * alphaFun C2.e; rw [alphaFun_e]; simp
      | t => change alphaFun C2.t = alphaFun C2.e * alphaFun C2.t; rw [alphaFun_e, alphaFun_t]; simp
    | t =>
      cases c with
      | e => change alphaFun C2.t = alphaFun C2.t * alphaFun C2.e; rw [alphaFun_e, alphaFun_t]; simp
      | t => change alphaFun C2.e = alphaFun C2.t * alphaFun C2.t; rw [alphaFun_e, alphaFun_t]; simp [alpha_mul_alpha]

theorem alphaHom_e : alphaHom C2.e = 1 := rfl

theorem alphaHom_t : alphaHom C2.t = alpha := rfl

@[expose] def fpow : C2 → P45
  | C2.e => 1
  | C2.t => f45

theorem fpow_e : fpow C2.e = 1 := rfl

theorem fpow_t : fpow C2.t = f45 := rfl

theorem fpow_mul_self (b : C2) : fpow b * fpow b = 1 := by
  cases b <;> simp [fpow, f45_sq]

theorem fpow_inv (b : C2) : (fpow b)⁻¹ = fpow b := by
  cases b <;> simp [fpow, f45_inv]

theorem fpow_mul (b c : C2) : fpow (b * c) = fpow b * fpow c := by
  rw [C2.mul_eq]
  cases b with
  | e =>
    cases c with
    | e => change fpow C2.e = fpow C2.e * fpow C2.e; rw [fpow_e]; simp
    | t => change fpow C2.t = fpow C2.e * fpow C2.t; rw [fpow_e, fpow_t]; simp
  | t =>
    cases c with
    | e => change fpow C2.t = fpow C2.t * fpow C2.e; rw [fpow_e, fpow_t]; simp
    | t => change fpow C2.e = fpow C2.t * fpow C2.t; rw [fpow_e, fpow_t]; simp [f45_sq]

theorem fpow_mem_A (b : C2) : fpow b ∈ A45 := by
  cases b <;> simp [fpow, f45_mem_A]

theorem alphaHom_apply_coe (b : C2) (q : Q45) :
    ((alphaHom b q : Q45) : P45) = fpow b * (q : P45) * (fpow b)⁻¹ := by
  cases b <;> simp [alphaHom, alphaFun, fpow, alpha, f45_inv]

abbrev QAct : Type := Q45 ⋊[alphaHom] C2

noncomputable instance : Finite QAct :=
  Finite.of_injective SemidirectProduct.equivProd SemidirectProduct.equivProd.injective

@[expose] noncomputable def toQA (p : QAct) : A45 :=
  ⟨(p.left : P45) * fpow p.right,
    Subgroup.mul_mem A45 (Q45_le_A45 p.left.2) (fpow_mem_A p.right)⟩

theorem toQA_apply (p : QAct) :
    (toQA p : P45) = (p.left : P45) * fpow p.right := rfl

theorem toQA_one : toQA 1 = 1 := by
  apply Subtype.ext
  change ((1 : Q45) : P45) * fpow C2.e = (1 : P45)
  rw [fpow_e]
  simp

theorem toQA_mul (p q : QAct) : toQA (p * q) = toQA p * toQA q := by
  apply Subtype.ext
  rw [toQA_apply, Subgroup.coe_mul, toQA_apply, toQA_apply]
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Subgroup.coe_mul]
  rw [fpow_mul, alphaHom_apply_coe, fpow_inv]
  have hsq : fpow p.right * fpow p.right = 1 := fpow_mul_self p.right
  calc ↑p.left * (fpow p.right * ↑q.left * fpow p.right) * (fpow p.right * fpow q.right)
      = ↑p.left * fpow p.right * ↑q.left * (fpow p.right * fpow p.right) * fpow q.right := by
        group
    _ = ↑p.left * fpow p.right * ↑q.left * 1 * fpow q.right := by rw [hsq]
    _ = ↑p.left * fpow p.right * (↑q.left * fpow q.right) := by group

@[expose] noncomputable def toQAMonoidHom : QAct →* A45 where
  toFun := toQA
  map_one' := toQA_one
  map_mul' := toQA_mul

theorem toQA_x :
    toQA (⟨⟨x45, x45_mem_Q⟩, C2.e⟩ : QAct) = ⟨x45, Q45_le_A45 x45_mem_Q⟩ := by
  apply Subtype.ext
  simp [toQA_apply, fpow_e, fpow_t]

theorem toQA_y :
    toQA (⟨⟨y45, y45_mem_Q⟩, C2.e⟩ : QAct) = ⟨y45, Q45_le_A45 y45_mem_Q⟩ := by
  apply Subtype.ext
  simp [toQA_apply, fpow_e, fpow_t]

theorem toQA_f :
    toQA (⟨1, C2.t⟩ : QAct) = ⟨f45, f45_mem_A⟩ := by
  apply Subtype.ext
  simp [toQA_apply, fpow_e, fpow_t]

theorem toQA_injective : Function.Injective toQA := by
  rintro ⟨p, bp⟩ ⟨q, bq⟩ h
  have hv : (p : P45) * fpow bp = (q : P45) * fpow bq := congrArg Subtype.val h
  cases bp <;> cases bq
  · simp [fpow] at hv
    exact SemidirectProduct.ext hv rfl
  · simp [fpow] at hv
    have hf : f45 ∈ Q45 := by
      have hcalc : f45 = (q : P45)⁻¹ * (p : P45) := by rw [hv]; group
      rw [hcalc]
      exact Subgroup.mul_mem Q45 (Subgroup.inv_mem Q45 q.2) p.2
    exact absurd hf f45_not_mem_Q
  · simp [fpow] at hv
    have hf : f45 ∈ Q45 := by
      have hcalc : f45 = (p : P45)⁻¹ * (q : P45) := by rw [← hv]; group
      rw [hcalc]
      exact Subgroup.mul_mem Q45 (Subgroup.inv_mem Q45 p.2) q.2
    exact absurd hf f45_not_mem_Q
  · simp [fpow] at hv
    exact SemidirectProduct.ext hv rfl

theorem card_Q45 : Nat.card Q45 = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem card_A45 : Nat.card A45 = 51840 := by
  rw [card_group QA45 QA45_ok, QA45_valid.2]

theorem card_QAct : Nat.card QAct = 51840 := by
  rw [SemidirectProduct.card, card_Q45, card_C2]

theorem toQA_bijective : Function.Bijective toQA :=
  Function.Injective.bijective_of_nat_card_le toQA_injective (by rw [card_A45, card_QAct])

theorem toQA_surjective : Function.Surjective toQA := toQA_bijective.2

@[expose] noncomputable def QAEquiv : QAct ≃* A45 :=
  MulEquiv.ofBijective toQAMonoidHom
    (Function.Surjective.bijective_of_nat_card_le toQA_surjective
      (by rw [card_QAct, card_A45]))

theorem QAEquiv_apply (p : QAct) : QAEquiv p = toQA p := rfl

theorem QAEquiv_symm_inl (q : Q45) :
    QAEquiv.symm ⟨q, Q45_le_A45 q.2⟩ = SemidirectProduct.inl q := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [QAEquiv_apply, toQA_apply, fpow]

theorem QAEquiv_symm_inr (b : C2) :
    QAEquiv.symm ⟨fpow b, fpow_mem_A b⟩ = SemidirectProduct.inr b := by
  rw [MulEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [QAEquiv_apply, toQA_apply]

theorem QAEquiv_inl (q : Q45) :
    QAEquiv (SemidirectProduct.inl q) = ⟨q, Q45_le_A45 q.2⟩ := by
  apply Subtype.ext
  change ((q : P45) * fpow (1 : C2)) = (q : P45)
  rw [show (1 : C2) = C2.e from rfl, fpow_e, mul_one]


@[expose] noncomputable def rhoQ : Q45 →* GL8 :=
  rho.comp psp43EquivP.symm.toMonoidHom

theorem rhoQ_apply (q : Q45) : rhoQ q = rho (psp43EquivP.symm q) := rfl

theorem rhoQ_x : rhoQ ⟨x45, x45_mem_Q⟩ = MxUnit := by
  rw [rhoQ_apply, ← psp43EquivP_xElt, MulEquiv.symm_apply_apply, rho_xElt]

theorem rhoQ_y : rhoQ ⟨y45, y45_mem_Q⟩ = MyUnit := by
  rw [rhoQ_apply, ← psp43EquivP_yElt, MulEquiv.symm_apply_apply, rho_yElt]

@[expose] noncomputable def conjBeta : MulAut PSp43 :=
  psp43EquivP.trans (alpha.trans psp43EquivP.symm)

theorem conjBeta_xElt : conjBeta U42.xElt = evalW U42.xElt U42.yElt conjWordX := by
  change psp43EquivP.symm (alpha (psp43EquivP U42.xElt)) = _
  rw [psp43EquivP_xElt]
  have halpha : alpha ⟨x45, x45_mem_Q⟩ = ⟨evalW x45 y45 conjWordX, evalW_mem_Q conjWordX⟩ := by
    apply Subtype.ext
    rw [alpha_apply, f45_inv, f45_conj_x]
    simp [conjWordX, evalW]
  rw [halpha, MulEquiv.symm_apply_eq, psp43EquivP_evalW]

theorem conjBeta_yElt : conjBeta U42.yElt = evalW U42.xElt U42.yElt conjWordY := by
  change psp43EquivP.symm (alpha (psp43EquivP U42.yElt)) = _
  rw [psp43EquivP_yElt]
  have halpha : alpha ⟨y45, y45_mem_Q⟩ = ⟨evalW x45 y45 conjWordY, evalW_mem_Q conjWordY⟩ := by
    apply Subtype.ext
    rw [alpha_apply, f45_inv, f45_conj_y]
  rw [halpha, MulEquiv.symm_apply_eq, psp43EquivP_evalW]

theorem rho_evalW (w : List Bool) :
    rho (evalW U42.xElt U42.yElt w) = evalW MxUnit MyUnit w := by
  rw [CFSG.GH74.KGroups.map_evalW (f := rho), rho_xElt, rho_yElt]

theorem rho_conjBeta_xElt :
    rho (conjBeta U42.xElt) = MfUnit * rho U42.xElt * MfUnit⁻¹ := by
  rw [conjBeta_xElt, rho_evalW]
  apply Units.ext
  rw [coe_evalW_genUnit, rho_xElt]
  simp [MfUnit, MxUnit, MfUnit_inv, Mf_conj_Mx]

theorem rho_conjBeta_yElt :
    rho (conjBeta U42.yElt) = MfUnit * rho U42.yElt * MfUnit⁻¹ := by
  rw [conjBeta_yElt, rho_evalW]
  apply Units.ext
  rw [coe_evalW_genUnit, rho_yElt]
  simp [MfUnit, MyUnit, MfUnit_inv, Mf_conj_My]

theorem rho_conjBeta (g : PSp43) : rho (conjBeta g) = MfUnit * rho g * MfUnit⁻¹ := by
  let K : Subgroup PSp43 :=
    { carrier := {g | rho (conjBeta g) = MfUnit * rho g * MfUnit⁻¹}
      one_mem' := by
        simp [beta, MfUnit_inv, MfUnit_mul_MfUnit]
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul conjBeta, map_mul rho, map_mul rho, ha, hb]
        group
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv conjBeta, map_inv rho, map_inv rho, ha]
        group }
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← U42.closure_xy]
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact rho_conjBeta_xElt
    · exact rho_conjBeta_yElt
  have hmem : g ∈ K := by
    rw [hK]
    exact Subgroup.mem_top g
  simpa [K] using hmem

theorem rhoQ_alpha (q : Q45) : rhoQ (alpha q) = MfUnit * rhoQ q * MfUnit⁻¹ := by
  change rho (psp43EquivP.symm (alpha q)) = MfUnit * rho (psp43EquivP.symm q) * MfUnit⁻¹
  have hbeta : conjBeta (psp43EquivP.symm q) = psp43EquivP.symm (alpha q) := by
    change psp43EquivP.symm (alpha (psp43EquivP (psp43EquivP.symm q))) = _
    rw [MulEquiv.apply_symm_apply]
  rw [← hbeta]
  exact rho_conjBeta _

@[expose] noncomputable def fgFun : C2 → GL8
  | C2.e => 1
  | C2.t => MfUnit

theorem fgFun_e : fgFun C2.e = 1 := rfl

theorem fgFun_t : fgFun C2.t = MfUnit := rfl

@[expose] noncomputable def fgUnit : C2 →* GL8 where
  toFun := fgFun
  map_one' := fgFun_e
  map_mul' b c := by
    rw [C2.mul_eq]
    cases b with
    | e =>
      cases c with
      | e => change fgFun C2.e = fgFun C2.e * fgFun C2.e; rw [fgFun_e]; simp
      | t => change fgFun C2.t = fgFun C2.e * fgFun C2.t; rw [fgFun_e, fgFun_t]; simp
    | t =>
      cases c with
      | e => change fgFun C2.t = fgFun C2.t * fgFun C2.e; rw [fgFun_e, fgFun_t]; simp
      | t => change fgFun C2.e = fgFun C2.t * fgFun C2.t; rw [fgFun_e, fgFun_t]; simp [MfUnit_mul_MfUnit]

@[expose] noncomputable def rhoAct : QAct →* GL8 :=
  SemidirectProduct.lift rhoQ fgUnit (by
    intro b
    apply MonoidHom.ext
    intro q
    cases b
    · simp [alphaHom_e, fgUnit, fgFun_e]
    · simpa [alphaHom_t, fgUnit, fgFun_t] using rhoQ_alpha q)

theorem rhoAct_inl (q : Q45) : rhoAct (SemidirectProduct.inl q) = rhoQ q := by
  simp [rhoAct]

theorem rhoAct_inr (b : C2) : rhoAct (SemidirectProduct.inr b) = fgUnit b := by
  simp [rhoAct]

@[expose] noncomputable def rhoA : A45 →* GL8 :=
  rhoAct.comp QAEquiv.symm.toMonoidHom

theorem rhoA_x : rhoA ⟨x45, Q45_le_A45 x45_mem_Q⟩ = MxUnit := by
  change rhoAct (QAEquiv.symm (Subtype.mk (Subtype.mk x45 x45_mem_Q)
    (Q45_le_A45 (Subtype.mk x45 x45_mem_Q).2))) = MxUnit
  rw [← QAEquiv_inl, MulEquiv.symm_apply_apply, rhoAct_inl, rhoQ_x]

theorem rhoA_y : rhoA ⟨y45, Q45_le_A45 y45_mem_Q⟩ = MyUnit := by
  change rhoAct (QAEquiv.symm (Subtype.mk (Subtype.mk y45 y45_mem_Q)
    (Q45_le_A45 (Subtype.mk y45 y45_mem_Q).2))) = MyUnit
  rw [← QAEquiv_inl, MulEquiv.symm_apply_apply, rhoAct_inl, rhoQ_y]

theorem rhoA_f : rhoA ⟨f45, f45_mem_A⟩ = MfUnit := by
  change rhoAct (QAEquiv.symm (⟨fpow C2.t, fpow_mem_A C2.t⟩ : A45)) = MfUnit
  rw [QAEquiv_symm_inr, rhoAct_inr]
  rfl

@[expose] noncomputable def actA (a : A45) (v : V) : V :=
  ((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v

theorem actA_one (v : V) : actA 1 v = v := by
  simp [actA]

theorem actA_mul (a b : A45) (v : V) : actA (a * b) v = actA a (actA b v) := by
  rw [actA, actA, actA, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem actA_add (a : A45) (v w : V) : actA a (v + w) = actA a v + actA a w := by
  simp [actA, Matrix.mulVec_add]

theorem actA_neg (a : A45) (v : V) : actA a (-v) = -actA a v := by
  exact Matrix.mulVec_neg v ((rhoA a : GL8) : Matrix (Fin 8) (Fin 8) (ZMod 2))

theorem actA_zero (a : A45) : actA a 0 = 0 := by
  simp [actA]

@[ext]
structure SpinExtA where
  v : V
  a : A45

namespace SpinExtA

@[expose] noncomputable def mul (p q : SpinExtA) : SpinExtA :=
  ⟨p.v + actA p.a q.v, p.a * q.a⟩

@[expose] noncomputable def inv (p : SpinExtA) : SpinExtA :=
  ⟨actA p.a⁻¹ (-p.v), p.a⁻¹⟩

noncomputable instance : Group SpinExtA where
  mul := mul
  one := ⟨0, 1⟩
  inv := inv
  mul_assoc p q r := by
    apply SpinExtA.ext
    · funext x
      change (p.v + actA p.a q.v) x + actA (p.a * q.a) r.v x =
        (p.v + actA p.a (q.v + actA q.a r.v)) x
      rw [actA_mul, actA_add]
      exact add_assoc _ _ _
    · change (p.a * q.a) * r.a = p.a * (q.a * r.a)
      rw [mul_assoc]
  one_mul p := by
    apply SpinExtA.ext
    · funext x
      change (0 + actA 1 p.v) x = p.v x
      simp [actA]
    · change 1 * p.a = p.a
      rw [one_mul]
  mul_one p := by
    apply SpinExtA.ext
    · funext x
      change (p.v + actA p.a 0) x = p.v x
      simp [actA]
    · change p.a * 1 = p.a
      rw [mul_one]
  inv_mul_cancel p := by
    apply SpinExtA.ext
    · funext x
      change (actA p.a⁻¹ (-p.v) + actA p.a⁻¹ p.v) x = (0 : V) x
      rw [actA_neg]
      exact congrFun (neg_add_cancel (actA p.a⁻¹ p.v)) x
    · change p.a⁻¹ * p.a = 1
      rw [inv_mul_cancel]

theorem mul_apply (p q : SpinExtA) : p * q = ⟨p.v + actA p.a q.v, p.a * q.a⟩ := rfl

theorem inv_apply (p : SpinExtA) : p⁻¹ = ⟨actA p.a⁻¹ (-p.v), p.a⁻¹⟩ := rfl

theorem one_apply : (1 : SpinExtA) = ⟨0, 1⟩ := rfl

def proj : SpinExtA →* A45 where
  toFun p := p.a
  map_one' := rfl
  map_mul' p q := rfl

def inl : Multiplicative V →* SpinExtA where
  toFun v := ⟨v.toAdd, 1⟩
  map_one' := by
    apply SpinExtA.ext
    · rfl
    · rfl
  map_mul' v w := by
    apply SpinExtA.ext
    · change Multiplicative.toAdd (v * w) = Multiplicative.toAdd v + actA 1 (Multiplicative.toAdd w)
      simp [actA]
    · change (1 : A45) = 1 * 1
      simp

theorem inl_apply (v : V) : inl (Multiplicative.ofAdd v) = ⟨v, 1⟩ := by
  apply SpinExtA.ext
  · rfl
  · rfl

theorem inl_injective : Function.Injective inl := by
  intro v w h
  simpa [inl] using congrArg SpinExtA.v h

theorem range_inl_eq_ker_proj : inl.range = proj.ker := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    change (inl v).a = 1
    rfl
  · intro hp
    have ha : p.a = 1 := hp
    refine ⟨Multiplicative.ofAdd p.v, ?_⟩
    apply SpinExtA.ext
    · rfl
    · change 1 = p.a
      rw [ha]

theorem proj_surjective : Function.Surjective proj := fun a => ⟨⟨0, a⟩, rfl⟩

def kerEquivV : proj.ker ≃ V where
  toFun p := p.1.v
  invFun v := ⟨⟨v, 1⟩, by change (⟨v, 1⟩ : SpinExtA).a = 1; rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply SpinExtA.ext
    · rfl
    · change 1 = p.1.a
      have hp : p.1.a = 1 := p.2
      rw [hp]
  right_inv v := rfl

theorem card_ker : Nat.card proj.ker = 2 ^ 8 := by
  rw [Nat.card_congr kerEquivV, Nat.card_fun, Nat.card_zmod]
  norm_num

def equivProd : SpinExtA ≃ V × A45 where
  toFun p := (p.v, p.a)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem card : Nat.card SpinExtA = 2 ^ 8 * 51840 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_fun, Nat.card_zmod, card_A45]
  norm_num

end SpinExtA

end CFSG.RankThree.GF2n.Parrott
