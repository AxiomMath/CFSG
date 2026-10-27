module

public import CFSG.Monster.B.Classical.UnitarySixClass
public import Mathlib.GroupTheory.SemidirectProduct
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.Classical.UnitarySix

open CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open scoped LinearAlgebra.Projectivization

@[expose] def betaV (v : V) : V := fun i => bar (v i)

theorem betaV_betaV (v : V) : betaV (betaV v) = v := funext fun i => bar_bar (v i)

theorem betaV_injective : Function.Injective betaV := fun v w h => by
  rw [← betaV_betaV v, h, betaV_betaV]

theorem betaV_ne_zero {v : V} (hv : v ≠ 0) : betaV v ≠ 0 := fun h =>
  hv (betaV_injective (h.trans (funext fun _ => bar_zero).symm))

theorem betaV_smul (c : F4) (v : V) : betaV (c • v) = bar c • betaV v :=
  funext fun i => bar_mul c (v i)

theorem herm_betaV (v w : V) : herm (betaV v) (betaV w) = bar (herm v w) := by
  rw [herm, herm, bar_sum]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [bar_mul]
  rfl

@[expose] def betaM (A : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4 := A.map bar

@[expose] noncomputable def barHom : F4 →+* F4 := frobeniusF4.toRingHom

theorem barHom_apply (a : F4) : barHom a = bar a := frobeniusF4_apply a

theorem coe_barHom : ⇑barHom = bar := funext barHom_apply

theorem betaM_mulVec (A : Matrix (Fin 6) (Fin 6) F4) (v : V) :
    betaV (A *ᵥ v) = betaM A *ᵥ betaV v := by
  funext i
  have := RingHom.map_mulVec barHom A v i
  rw [coe_barHom] at this
  exact this

theorem betaM_mul (A B : Matrix (Fin 6) (Fin 6) F4) : betaM (A * B) = betaM A * betaM B := by
  have := Matrix.map_mul (L := A) (M := B) (f := barHom)
  rw [coe_barHom] at this
  exact this

theorem betaM_one : betaM 1 = 1 := by
  ext i j
  rw [betaM, Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem betaM_betaM (A : Matrix (Fin 6) (Fin 6) F4) : betaM (betaM A) = A := by
  ext i j
  exact bar_bar (A i j)

theorem det_betaM (A : Matrix (Fin 6) (Fin 6) F4) : (betaM A).det = bar A.det := by
  have := RingHom.map_det barHom A
  rw [coe_barHom] at this
  exact this.symm

theorem isIsometry_betaM {A : Matrix (Fin 6) (Fin 6) F4} (hA : IsIsometry A) :
    IsIsometry (betaM A) := by
  intro x y
  rw [← betaV_betaV x, ← betaV_betaV y, ← betaM_mulVec, ← betaM_mulVec, herm_betaV, herm_betaV,
    hA]

@[expose] noncomputable def betaSU : MulAut (SU frobeniusF4 6) where
  toFun g := mkSU (betaM ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
    (by rw [det_betaM, det_of_mem, bar_one]) (isIsometry_betaM (isIsometry_of_mem g))
  invFun g := mkSU (betaM ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
    (by rw [det_betaM, det_of_mem, bar_one]) (isIsometry_betaM (isIsometry_of_mem g))
  left_inv g := SU_ext (by rw [coe_mkSU, coe_mkSU, betaM_betaM])
  right_inv g := SU_ext (by rw [coe_mkSU, coe_mkSU, betaM_betaM])
  map_mul' g g' := SU_ext (by
    simp only [coe_mkSU, coe_SU_mul, betaM_mul])

theorem coe_betaSU (g : SU frobeniusF4 6) :
    (((betaSU g : SU frobeniusF4 6) : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      betaM ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := rfl

theorem betaSU_scalars : scalars ≤ scalars.comap betaSU.toMonoidHom := by
  intro z hz
  obtain ⟨a, ha⟩ := mem_scalars.1 hz
  rw [Subgroup.mem_comap, mem_scalars]
  refine ⟨bar a, ?_⟩
  change betaM _ = _
  rw [ha]
  ext i j
  simp only [betaM, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

@[expose] noncomputable def betaL : MulAut ProjSU where
  toFun := QuotientGroup.map _ _ betaSU.toMonoidHom betaSU_scalars
  invFun := QuotientGroup.map _ _ betaSU.toMonoidHom betaSU_scalars
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g =>
      simp only [QuotientGroup.map_mk]
      congr 1
      exact SU_ext (by rw [MulEquiv.coe_toMonoidHom, coe_betaSU, coe_betaSU, betaM_betaM])
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H g =>
      simp only [QuotientGroup.map_mk]
      congr 1
      exact SU_ext (by rw [MulEquiv.coe_toMonoidHom, coe_betaSU, coe_betaSU, betaM_betaM])
  map_mul' := map_mul _

theorem betaL_mk (g : SU frobeniusF4 6) : betaL (g : ProjSU) = (betaSU g : ProjSU) := rfl

theorem betaL_mul_self : betaL * betaL = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [MulAut.mul_apply, betaL_mk, betaL_mk, MulAut.one_apply]
    congr 1
    exact SU_ext (by rw [coe_betaSU, coe_betaSU, betaM_betaM])

@[expose] noncomputable def betaPow (ε : ZMod 2) : MulAut ProjSU := if ε = 0 then 1 else betaL

theorem zmod2_cases' : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem betaPow_add (x y : ZMod 2) : betaPow (x + y) = betaPow x * betaPow y := by
  rcases zmod2_cases' x with rfl | rfl <;> rcases zmod2_cases' y with rfl | rfl
  · simp [betaPow]
  · simp [betaPow]
  · simp [betaPow]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
    simp only [betaPow, ite_true, show ¬((1 : ZMod 2) = 0) by decide, ite_false,
      betaL_mul_self]

@[expose] noncomputable def betaHom : Multiplicative (ZMod 2) →* MulAut ProjSU where
  toFun ε := betaPow (Multiplicative.toAdd ε)
  map_one' := by simp [betaPow]
  map_mul' _ _ := betaPow_add _ _

abbrev LBeta : Type := ProjSU ⋊[betaHom] Multiplicative (ZMod 2)

@[expose] noncomputable def betaElt : LBeta := SemidirectProduct.inr (Multiplicative.ofAdd 1)

theorem orderOf_betaElt : orderOf betaElt = 2 := by
  rw [betaElt, orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective]
  rw [orderOf_ofAdd_eq_addOrderOf]
  exact ZMod.addOrderOf_one 2

theorem herm_betaV_self_eq_zero {v : V} (hv : herm v v = 0) : herm (betaV v) (betaV v) = 0 := by
  rw [herm_betaV, hv, bar_zero]

@[expose] noncomputable def betaPt (p : IsoPt) : IsoPt :=
  pt (betaV p.1.rep) (betaV_ne_zero (rep_ne_zero p)) (herm_betaV_self_eq_zero (isIsoPt_of p))

theorem betaPt_pt (v : V) (hv0 : v ≠ 0) (hv : herm v v = 0) :
    betaPt (pt v hv0 hv) = pt (betaV v) (betaV_ne_zero hv0) (herm_betaV_self_eq_zero hv) := by
  obtain ⟨a, ha⟩ := rep_pt hv0 hv
  rw [betaPt, pt_eq_pt_iff]
  refine ⟨bar (a : F4), ?_⟩
  rw [← betaV_smul, ← ha]
  rfl

theorem betaPt_betaPt (p : IsoPt) : betaPt (betaPt p) = p := by
  induction p using IsoPt.ind with
  | h v hv0 hv =>
    rw [betaPt_pt, betaPt_pt, pt_eq_pt_iff]
    exact ⟨1, by rw [one_smul, betaV_betaV]⟩

theorem betaPt_smul (g : SU frobeniusF4 6) (p : IsoPt) :
    betaPt (g • p) = betaSU g • betaPt p := by
  induction p using IsoPt.ind with
  | h v hv0 hv =>
    rw [smul_pt, betaPt_pt, betaPt_pt, smul_pt, pt_eq_pt_iff]
    refine ⟨1, ?_⟩
    rw [one_smul, smul_def, smul_def, coe_betaSU, betaM_mulVec]

@[expose] noncomputable def betaPerm : Equiv.Perm IsoPt where
  toFun := betaPt
  invFun := betaPt
  left_inv := betaPt_betaPt
  right_inv := betaPt_betaPt

theorem betaPerm_mul_self : betaPerm * betaPerm = 1 := Equiv.ext betaPt_betaPt

@[expose] noncomputable def betaPermHom : Multiplicative (ZMod 2) →* Equiv.Perm IsoPt where
  toFun ε := if Multiplicative.toAdd ε = 0 then 1 else betaPerm
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : Equiv.Perm IsoPt) else betaPerm) =
        (if x = 0 then 1 else betaPerm) * (if y = 0 then 1 else betaPerm) := by
      intro x y
      rcases zmod2_cases' x with rfl | rfl <;> rcases zmod2_cases' y with rfl | rfl
      · simp
      · simp
      · simp
      · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
        simp only [ite_true, show ¬((1 : ZMod 2) = 0) by decide, ite_false, betaPerm_mul_self]
    exact key _ _

theorem projAct_betaPow (ε : ZMod 2) (x : ProjSU) :
    projAct (betaPow ε x) = betaPermHom (Multiplicative.ofAdd ε) * projAct x *
      (betaPermHom (Multiplicative.ofAdd ε))⁻¹ := by
  rcases zmod2_cases' ε with rfl | rfl
  · simp [betaPow, betaPermHom]
  · induction x using QuotientGroup.induction_on with
    | H g =>
      have h1 : betaPermHom (Multiplicative.ofAdd (1 : ZMod 2)) = betaPerm := by
        simp [betaPermHom, show ¬((1 : ZMod 2) = 0) by decide]
      rw [h1]
      simp only [betaPow, show ¬((1 : ZMod 2) = 0) by decide, ite_false, betaL_mk]
      refine Equiv.ext fun p => ?_
      rw [projAct_mk, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, projAct_mk]
      have hinv : betaPerm⁻¹ = betaPerm := by
        rw [inv_eq_iff_mul_eq_one, betaPerm_mul_self]
      rw [hinv]
      change betaSU g • p = betaPt (g • betaPt p)
      rw [betaPt_smul, betaPt_betaPt]

@[expose] noncomputable def extAct : LBeta →* Equiv.Perm IsoPt :=
  SemidirectProduct.lift projAct betaPermHom fun ε => MonoidHom.ext fun x => by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    exact projAct_betaPow _ x

theorem extAct_inl (x : ProjSU) : extAct (SemidirectProduct.inl x) = projAct x :=
  SemidirectProduct.lift_inl _ _ _ x

theorem extAct_inr (ε : Multiplicative (ZMod 2)) :
    extAct (SemidirectProduct.inr ε) = betaPermHom ε :=
  SemidirectProduct.lift_inr _ _ _ ε

theorem extAct_betaElt : extAct betaElt = betaPerm := by
  rw [betaElt, extAct, SemidirectProduct.lift_inr]
  simp [betaPermHom, show ¬((1 : ZMod 2) = 0) by decide]

theorem omega_point :
    herm (Pi.single 0 1 + F4.ω • Pi.single 1 1) (Pi.single 0 1 + F4.ω • Pi.single 1 1) = 0 ∧
      (Pi.single 0 1 + F4.ω • Pi.single 1 1 : V) ≠ 0 ∧
      ∀ c : F4, c • (Pi.single 0 1 + F4.ω • Pi.single 1 1 : V) ≠
        betaV (Pi.single 0 1 + F4.ω • Pi.single 1 1) := by
  decide +kernel

theorem betaV_single (j : Fin 6) : betaV (Pi.single j 1) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simp [betaV]
  · simp [betaV, Pi.single_eq_of_ne h]

theorem betaPt_stdPt (j : Fin 6) : betaPt (stdPt j) = stdPt j := by
  rw [stdPt, betaPt_pt, pt_eq_pt_iff]
  exact ⟨1, by rw [one_smul, betaV_single]⟩

theorem betaV_pair : ∀ i j : Fin 6, (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)] →
    betaV (Pi.single i 1 + Pi.single j 1) = Pi.single i 1 + Pi.single j 1 := by
  decide +kernel

theorem betaPt_pairPt (i j : Fin 6) (hij : (i, j) ∈ [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)]) :
    betaPt (pt _ (pair_isotropic i j hij).2 (pair_isotropic i j hij).1) =
      pt _ (pair_isotropic i j hij).2 (pair_isotropic i j hij).1 := by
  rw [betaPt_pt, pt_eq_pt_iff]
  exact ⟨1, by rw [one_smul, betaV_pair i j hij]⟩

theorem extAct_injective : Function.Injective extAct := by
  rw [injective_iff_map_eq_one]
  intro y hy
  rw [← SemidirectProduct.inl_left_mul_inr_right y, map_mul, extAct_inl, extAct_inr] at hy
  rcases zmod2_cases' (Multiplicative.toAdd y.right) with h0 | h1
  · have hr : y.right = 1 := by
      rw [← ofAdd_toAdd y.right, h0]
      rfl
    have hb : betaPermHom y.right = 1 := by rw [hr, map_one]
    rw [hb, mul_one] at hy
    have hl : y.left = 1 := projAct_injective (hy.trans (map_one _).symm)
    exact SemidirectProduct.ext hl hr
  · exfalso
    have hb : betaPermHom y.right = betaPerm := by
      change (if Multiplicative.toAdd y.right = 0 then 1 else betaPerm) = betaPerm
      rw [h1, ite_eq_right (by decide)]
    rw [hb] at hy
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective y.left
    have hfix : ∀ p, g • betaPt p = p := fun p => by
      have := congrArg (fun π : Equiv.Perm IsoPt => π p) hy
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this
      rw [← hg, projAct_mk] at this
      exact this
    have hscal : g ∈ scalars := mem_scalars_of_fix g
      (fun j => by have := hfix (stdPt j); rwa [betaPt_stdPt] at this)
      (fun i j hij => by
        have := hfix (pt _ (pair_isotropic i j hij).2 (pair_isotropic i j hij).1)
        rwa [betaPt_pairPt] at this)
    obtain ⟨hω, hω0, hωne⟩ := omega_point
    have h1 := hfix (pt _ hω0 hω)
    rw [scalar_smul_eq g hscal, betaPt_pt, pt_eq_pt_iff] at h1
    obtain ⟨c, hc⟩ := h1
    exact hωne c hc

theorem unitary_six_isotropic_point_graph :
    isoGraph.IsSRGWith 693 180 51 45 ∧
    (∀ p q : IsoPt, ∃ x : ProjSU, projAct x p = q) ∧
    (∀ p q p' q' : IsoPt, isoGraph.Adj p q → isoGraph.Adj p' q' →
      ∃ x : ProjSU, projAct x p = p' ∧ projAct x q = q') ∧
    (∀ p q p' q' : IsoPt, p ≠ q → ¬isoGraph.Adj p q → p' ≠ q' → ¬isoGraph.Adj p' q' →
      ∃ x : ProjSU, projAct x p = p' ∧ projAct x q = q') ∧
    (∀ g : SU frobeniusF4 6, (∀ p : IsoPt, g • p = p) ↔ g ∈ scalars) ∧
    Function.Injective projAct ∧
    (∀ x : ProjSU, extAct (SemidirectProduct.inl x) = projAct x) ∧
    orderOf betaElt = 2 ∧
    (∀ (v : V) (hv0 : v ≠ 0) (hv : herm v v = 0),
      extAct betaElt (pt v hv0 hv) =
        pt (betaV v) (betaV_ne_zero hv0) (herm_betaV_self_eq_zero hv)) ∧
    Function.Injective extAct ∧
    (∀ (v : V) (hv0 : v ≠ 0) (hv : herm v v = 0), tPt (pt v hv0 hv) = (transvec v hv : ProjSU)) ∧
    Function.Injective tPt ∧ Set.range tPt = rankOneClass ∧
    rankOneClass = {y | IsConj (tPt (stdPt 0)) y} ∧
    (∀ (x : ProjSU) (p : IsoPt), tPt (projAct x p) = x * tPt p * x⁻¹) ∧
    (∀ p q : IsoPt, isoGraph.Adj p q → orderOf (tPt p * tPt q) = 2) ∧
    (∀ p q : IsoPt, p ≠ q → ¬isoGraph.Adj p q → orderOf (tPt p * tPt q) = 3) ∧
    ∀ p q : IsoPt, isoGraph.Adj p q ↔ p ≠ q ∧ Commute (tPt p) (tPt q) :=
  ⟨isSRGWith, projAct_transitive, projAct_transitive_adj, projAct_transitive_nonadj,
    fix_all_iff_mem_scalars, projAct_injective, extAct_inl, orderOf_betaElt,
    fun v hv0 hv => by rw [extAct_betaElt]; exact betaPt_pt v hv0 hv, extAct_injective, tPt_pt,
    tPt_injective, range_tPt, rankOneClass_eq_conj, tPt_projAct,
    fun _ _ h => orderOf_tPt_mul_adj h, fun _ _ hpq h => orderOf_tPt_mul_nonadj hpq h,
    adj_iff_commute⟩

end CFSG.Monster.B.Classical.UnitarySix
