module

public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.RankThree.GF2n.Parrott.SpinModule

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.GH74.Exceptional CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U42
  CFSG.Sporadic.Bridge.TwoGen
open scoped Matrix


theorem matWord_spinRelA2 : matWord spinRelA2 = 1 := by
  refine Matrix.ext_of_mulVec_single (M := matWord spinRelA2) (N := 1) (fun e => ?_)
  have h := rel_a2 e
  rw [evalSpinWordV_eq_matWord_mulVec] at h
  simpa only [basis, Matrix.one_mulVec] using h

theorem matWord_spinRelB5 : matWord spinRelB5 = 1 := by
  refine Matrix.ext_of_mulVec_single (M := matWord spinRelB5) (N := 1) (fun e => ?_)
  have h := rel_b5 e
  rw [evalSpinWordV_eq_matWord_mulVec] at h
  simpa only [basis, Matrix.one_mulVec] using h

theorem matWord_spinRelAB9 : matWord spinRelAB9 = 1 := by
  refine Matrix.ext_of_mulVec_single (M := matWord spinRelAB9) (N := 1) (fun e => ?_)
  have h := rel_ab9 e
  rw [evalSpinWordV_eq_matWord_mulVec] at h
  simpa only [basis, Matrix.one_mulVec] using h

theorem matWord_spinRelComm3 : matWord spinRelComm3 = 1 := by
  refine Matrix.ext_of_mulVec_single (M := matWord spinRelComm3) (N := 1) (fun e => ?_)
  have h := rel_comm3 e
  rw [evalSpinWordV_eq_matWord_mulVec] at h
  simpa only [basis, Matrix.one_mulVec] using h

theorem matWord_spinRelCommBab2 : matWord spinRelCommBab2 = 1 := by
  refine Matrix.ext_of_mulVec_single (M := matWord spinRelCommBab2) (N := 1) (fun e => ?_)
  have h := rel_comm_bab2 e
  rw [evalSpinWordV_eq_matWord_mulVec] at h
  simpa only [basis, Matrix.one_mulVec] using h

theorem Mx_mul_Mx : Mx * Mx = 1 := by
  simpa [matWord, spinRelA2, spinLetterMatrix, List.prod_cons, List.prod_nil, mul_assoc]
    using matWord_spinRelA2

theorem My_mul_MyInv : My * MyInv = 1 := by
  simpa [matWord, spinRelB5, spinLetterMatrix, MyInv, List.prod_cons, List.prod_nil, mul_assoc]
    using matWord_spinRelB5

theorem MyInv_mul_My : MyInv * My = 1 := by
  simpa [matWord, spinRelB5, spinLetterMatrix, MyInv, List.prod_cons, List.prod_nil, mul_assoc]
    using matWord_spinRelB5

@[expose] def MxUnit : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  ⟨Mx, Mx, Mx_mul_Mx, Mx_mul_Mx⟩

@[expose] def MyUnit : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  ⟨My, MyInv, My_mul_MyInv, MyInv_mul_My⟩

@[expose] def genUnit : Fin 2 → Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  fun i => if i = 0 then MxUnit else MyUnit

noncomputable def freeRho : FreeGroup (Fin 2) →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  FreeGroup.lift genUnit

theorem coe_freeRho_mk (w : List (Fin 2 × Bool)) :
    ((freeRho (FreeGroup.mk w) : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = matWord w := by
  change (Units.coeHom (Matrix (Fin 8) (Fin 8) (ZMod 2)))
      (FreeGroup.lift genUnit (FreeGroup.mk w)) = matWord w
  rw [FreeGroup.lift_mk, map_list_prod, matWord, List.map_map]
  congr 1
  refine List.map_congr_left (fun l _ => ?_)
  rcases l with ⟨i, b⟩
  fin_cases i <;> cases b <;>
    simp [genUnit, MxUnit, MyUnit, spinLetterMatrix]

theorem freeRho_spinRelA2 : freeRho (FreeGroup.mk spinRelA2) = 1 :=
  Units.ext (by rw [Units.val_one, coe_freeRho_mk, matWord_spinRelA2])

theorem freeRho_spinRelB5 : freeRho (FreeGroup.mk spinRelB5) = 1 :=
  Units.ext (by rw [Units.val_one, coe_freeRho_mk, matWord_spinRelB5])

theorem freeRho_spinRelAB9 : freeRho (FreeGroup.mk spinRelAB9) = 1 :=
  Units.ext (by rw [Units.val_one, coe_freeRho_mk, matWord_spinRelAB9])

theorem freeRho_spinRelComm3 : freeRho (FreeGroup.mk spinRelComm3) = 1 :=
  Units.ext (by rw [Units.val_one, coe_freeRho_mk, matWord_spinRelComm3])

theorem freeRho_spinRelCommBab2 : freeRho (FreeGroup.mk spinRelCommBab2) = 1 :=
  Units.ext (by rw [Units.val_one, coe_freeRho_mk, matWord_spinRelCommBab2])

theorem freeRho_spinRels (w : List (Fin 2 × Bool)) (hw : w ∈ spinRels) :
    freeRho (FreeGroup.mk w) = 1 := by
  simp only [spinRels, List.mem_cons, List.mem_nil_iff, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact freeRho_spinRelA2
  · exact freeRho_spinRelB5
  · exact freeRho_spinRelAB9
  · exact freeRho_spinRelComm3
  · exact freeRho_spinRelCommBab2

theorem U42_rels_eq_spinRels : CFSG.LieType.Multipliers.U42.rels = spinRels := rfl

theorem freeRho_wordSet_rels (r : FreeGroup (Fin 2))
    (hr : r ∈ wordSet CFSG.LieType.Multipliers.U42.rels) : freeRho r = 1 := by
  rw [wordSet] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  exact freeRho_spinRels w (by simpa [U42_rels_eq_spinRels] using hw)

section Presentation


noncomputable def presGen : Fin 2 → PSp43 := fun i => img2 xElt yElt i.val

theorem isPresentation_presGen : IsPresentation presGen (wordSet rels) :=
  isPresentation_PSp43

noncomputable def varphi : FreeGroup (Fin 2) →* PSp43 := FreeGroup.lift presGen

theorem varphi_surjective : Function.Surjective varphi :=
  isPresentation_presGen.lift_surjective

theorem varphi_ker :
    varphi.ker = Subgroup.normalClosure (wordSet CFSG.LieType.Multipliers.U42.rels) :=
  isPresentation_presGen.ker_lift

theorem ker_varphi_le_ker_freeRho : varphi.ker ≤ freeRho.ker := by
  rw [varphi_ker]
  exact Subgroup.normalClosure_le_normal (fun r hr => freeRho_wordSet_rels r hr)

noncomputable def rhoBar : FreeGroup (Fin 2) ⧸ varphi.ker →*
    Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  QuotientGroup.lift (N := varphi.ker) freeRho ker_varphi_le_ker_freeRho

noncomputable def quotientEquiv : FreeGroup (Fin 2) ⧸ varphi.ker ≃* PSp43 :=
  QuotientGroup.quotientKerEquivOfSurjective (φ := varphi) varphi_surjective

theorem quotientEquiv_mk_of (i : Fin 2) :
    quotientEquiv (QuotientGroup.mk (FreeGroup.of i)) = presGen i := by
  rw [quotientEquiv]
  change QuotientGroup.kerLift varphi (QuotientGroup.mk (FreeGroup.of i)) = presGen i
  rw [QuotientGroup.kerLift_mk]
  simp [varphi]

noncomputable def rho : PSp43 →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2) :=
  rhoBar.comp quotientEquiv.symm.toMonoidHom

theorem rho_gen (i : Fin 2) : rho (presGen i) = genUnit i := by
  rw [rho, MonoidHom.comp_apply]
  have hsymm : quotientEquiv.symm (presGen i) = QuotientGroup.mk (FreeGroup.of i) := by
    rw [MulEquiv.symm_apply_eq]
    exact (quotientEquiv_mk_of i).symm
  change rhoBar (quotientEquiv.symm (presGen i)) = genUnit i
  rw [hsymm]
  simp [rhoBar, freeRho]

theorem rho_xElt : rho xElt = MxUnit := by
  have h := rho_gen 0
  simpa [presGen, img2, genUnit] using h

theorem rho_yElt : rho yElt = MyUnit := by
  have h := rho_gen 1
  simpa [presGen, img2, genUnit] using h

@[expose] noncomputable def act (a : PSp43) (v : V) : V :=
  ((rho a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ v

theorem act_one (v : V) : act 1 v = v := by
  simp [act]

theorem act_mul (a b : PSp43) (v : V) : act (a * b) v = act a (act b v) := by
  rw [act, act, act, map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem act_add (a : PSp43) (v w : V) : act a (v + w) = act a v + act a w := by
  simp [act, Matrix.mulVec_add]

theorem act_neg (a : PSp43) (v : V) : act a (-v) = -act a v := by
  exact Matrix.mulVec_neg v ((rho a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
    Matrix (Fin 8) (Fin 8) (ZMod 2))

theorem act_zero (a : PSp43) : act a 0 = 0 := by
  simp [act]

@[ext]
structure SpinExt where
  v : V
  a : PSp43

namespace SpinExt

@[expose] noncomputable def mul (p q : SpinExt) : SpinExt :=
  ⟨p.v + act p.a q.v, p.a * q.a⟩

@[expose] noncomputable def inv (p : SpinExt) : SpinExt :=
  ⟨act p.a⁻¹ (-p.v), p.a⁻¹⟩

noncomputable instance : Group SpinExt where
  mul := mul
  one := ⟨0, 1⟩
  inv := inv
  mul_assoc p q r := by
    apply SpinExt.ext
    · funext x
      change (p.v + act p.a q.v) x + act (p.a * q.a) r.v x =
        (p.v + act p.a (q.v + act q.a r.v)) x
      rw [act_mul, act_add]
      exact add_assoc _ _ _
    · change (p.a * q.a) * r.a = p.a * (q.a * r.a)
      rw [mul_assoc]
  one_mul p := by
    apply SpinExt.ext
    · funext x
      change (0 + act 1 p.v) x = p.v x
      simp [act]
    · change 1 * p.a = p.a
      rw [one_mul]
  mul_one p := by
    apply SpinExt.ext
    · funext x
      change (p.v + act p.a 0) x = p.v x
      simp [act]
    · change p.a * 1 = p.a
      rw [mul_one]
  inv_mul_cancel p := by
    apply SpinExt.ext
    · funext x
      change (act p.a⁻¹ (-p.v) + act p.a⁻¹ p.v) x = (0 : V) x
      rw [act_neg]
      exact congrFun (neg_add_cancel (act p.a⁻¹ p.v)) x
    · change p.a⁻¹ * p.a = 1
      rw [inv_mul_cancel]

theorem mul_apply (p q : SpinExt) : p * q = ⟨p.v + act p.a q.v, p.a * q.a⟩ := rfl

theorem inv_apply (p : SpinExt) : p⁻¹ = ⟨act p.a⁻¹ (-p.v), p.a⁻¹⟩ := rfl

theorem one_apply : (1 : SpinExt) = ⟨0, 1⟩ := rfl

def proj : SpinExt →* PSp43 where
  toFun p := p.a
  map_one' := rfl
  map_mul' p q := rfl

def inl : Multiplicative V →* SpinExt where
  toFun v := ⟨v.toAdd, 1⟩
  map_one' := by
    apply SpinExt.ext
    · rfl
    · rfl
  map_mul' v w := by
    apply SpinExt.ext
    · change Multiplicative.toAdd (v * w) = Multiplicative.toAdd v + act 1 (Multiplicative.toAdd w)
      simp [act]
    · change (1 : PSp43) = 1 * 1
      simp

theorem inl_apply (v : V) : inl (Multiplicative.ofAdd v) = ⟨v, 1⟩ := by
  apply SpinExt.ext
  · rfl
  · rfl

theorem inl_injective : Function.Injective inl := by
  intro v w h
  simpa [inl] using congrArg SpinExt.v h

theorem range_inl_eq_ker_proj : inl.range = proj.ker := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    change (inl v).a = 1
    rfl
  · intro hp
    have ha : p.a = 1 := hp
    refine ⟨Multiplicative.ofAdd p.v, ?_⟩
    apply SpinExt.ext
    · rfl
    · change 1 = p.a
      rw [ha]

theorem proj_surjective : Function.Surjective proj := fun a => ⟨⟨0, a⟩, rfl⟩

def kerEquivV : proj.ker ≃ V where
  toFun p := p.1.v
  invFun v := ⟨⟨v, 1⟩, by change (⟨v, 1⟩ : SpinExt).a = 1; rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply SpinExt.ext
    · rfl
    · change 1 = p.1.a
      have hp : p.1.a = 1 := p.2
      rw [hp]
  right_inv v := rfl

theorem card_ker : Nat.card proj.ker = 2 ^ 8 := by
  rw [Nat.card_congr kerEquivV, Nat.card_fun, Nat.card_zmod]
  norm_num

def equivProd : SpinExt ≃ V × PSp43 where
  toFun p := (p.v, p.a)
  invFun p := ⟨p.1, p.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by cases p; rfl

theorem card : Nat.card SpinExt = 2 ^ 8 * 25920 := by
  rw [Nat.card_congr equivProd, Nat.card_prod, Nat.card_fun, Nat.card_zmod, card_PSp43]
  norm_num

end SpinExt

end Presentation

end CFSG.RankThree.GF2n.Parrott
