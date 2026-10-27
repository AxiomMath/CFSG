module

public import CFSG.Monster.B.Final.Elements
public import CFSG.Monster.B.Gen.Transfer
public import CFSG.Monster.B.Gen.Generation
public import CFSG.Monster.B.Gen.Max2Assembly
public import CFSG.Monster.B.Gen.EbarPairing
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3049
public import Certificates.Certificate3109
public import Certificates.Certificate3027

public section

namespace CFSG.Monster.B

open Matrix MulOpposite Bin CFSG.Blueprint

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem Tmat_isUnit : IsUnit Tmat := pinned_facts.2.2.2.2.2.2.1

theorem Tmat_mul_inv : Tmat * Tmat⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 Tmat_isUnit)

theorem Tmat_inv_mul : Tmat⁻¹ * Tmat = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 Tmat_isUnit)

@[expose] noncomputable def Tunit : MatBˣ := Tmat_isUnit.unit

theorem coe_Tunit : (Tunit : MatB) = Tmat := rfl

theorem coe_Tunit_inv : ((Tunit⁻¹ : MatBˣ) : MatB) = Tmat⁻¹ := by
  rw [Matrix.coe_units_inv, coe_Tunit]

theorem Qn_25 : Qn 25 = Dyadic.Qmat 25 := Qn_eq 25

section Assembly

variable (β : Cbar →* GL (Fin 4370) (ZMod 2)) (g : ℕ → Cbar)
  (hg : ∀ j < 26, ((betaRow β (op (g j)) : MatBˣ) : MatB) = Qn j)

include hg in
theorem Qn_isUnit : ∀ j < 26, IsUnit (Qn j) := fun j hj => by
  rw [← hg j hj]
  exact Units.isUnit _

include hg in
theorem exists_iota
    (hβ : Function.Injective β) (hτ : g 25 = taubar) (a : Sbp)
    (ha : ((betaRow β a : MatBˣ) : MatB) = Fmat) :
    ∃ ι : NativeSporadic.B →* Sbp, Function.Injective ι ∧
      ∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹ := by
  obtain ⟨-, -, -, -, hFT, hQT, -⟩ := pair_matrix_facts
  have h₁ : (Tunit : MatB) * genA₁ * ((Tunit⁻¹ : MatBˣ) : MatB) = betaRow β a := by
    rw [coe_Tunit, coe_Tunit_inv, ha, ← hFT, Matrix.mul_assoc, Tmat_mul_inv, Matrix.mul_one]
  have h₂ : (Tunit : MatB) * genA₂ * ((Tunit⁻¹ : MatBˣ) : MatB) = betaRow β (op taubar) := by
    rw [coe_Tunit, coe_Tunit_inv, ← hτ, hg 25 (by norm_num), Qn_25, ← hQT, Matrix.mul_assoc,
      Tmat_mul_inv, Matrix.mul_one]
  obtain ⟨ι, hι, hιβ⟩ := exists_embedding_of_intertwiner (betaRow β) (betaRow_injective hβ) genA₁
    genA₂ Tunit a (op taubar) h₁ h₂
  refine ⟨ι, hι, fun X => ?_⟩
  have h := hιβ X
  rw [coe_Tunit, coe_Tunit_inv] at h
  exact h

include hg in
theorem xbar_eq_xS (hg0 : g 0 ∈ Ebar) (hg1 : g 1 ∈ Jbar) (hX1 : Xm Qn ≠ 1) : op xbar = xS g := by
  set f : Cbar := g 1 * g 0 * (g 1)⁻¹ with hf
  have hfE : f ∈ Ebar := by
    have := conj_mem_Ebar (Jbar.inv_mem hg1) hg0
    rwa [inv_inv] at this
  have hmE : f * g 0 ∈ Ebar := Ebar.mul_mem hfE hg0
  have hyE : (f * g 0) ^ 2 ∈ Ebar := Ebar.pow_mem hmE 2
  have hxS : xS g = op ((f * g 0) ^ 2) := by
    rw [xS, op_pow, op_mul, hf, op_mul, op_mul, op_inv]
    group
  have hpsi : psiBar ⟨(f * g 0) ^ 2, hyE⟩ = 1 := by
    have e : (⟨(f * g 0) ^ 2, hyE⟩ : Ebar) = (⟨f * g 0, hmE⟩ : Ebar) ^ 2 := rfl
    rw [e, map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, ← Nat.cast_smul_eq_nsmul (ZMod 2),
      show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_smul]
  rcases (psiBar_eq_one_iff _).1 hpsi with h | h
  · exfalso
    apply hX1
    rw [← betaRow_xS β g hg, hxS, show (f * g 0) ^ 2 = 1 from congrArg Subtype.val h, op_one,
      map_one, Units.val_one]
  · rw [hxS, show (f * g 0) ^ 2 = xbar from congrArg Subtype.val h]

end Assembly

section Members

variable (g : ℕ → Cbar)

theorem op_mem_op {H : Subgroup Cbar} {x : Cbar} (h : x ∈ H) : op x ∈ H.op := h

theorem wordS_mem (H : Subgroup Cbar) (w : List ℕ) (hw : ∀ j ∈ w, g j ∈ H) : wordS g w ∈ H.op := by
  unfold wordS
  refine list_prod_mem fun y hy => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  exact op_mem_op (hw j hj)

theorem basisWord_letters_range : ∀ j ∈ basisWord, 1 ≤ j ∧ j ≤ 24 := by
  intro j hj
  simp only [basisWord, List.mem_cons, List.mem_nil_iff, or_false] at hj
  omega

theorem eS_mem (hg0 : g 0 ∈ Ebar) (hgJ : ∀ j, 1 ≤ j → j ≤ 24 → g j ∈ Jbar) (i : ℕ) :
    (eS g i).unop ∈ Ebar := by
  have hP : wordS g (basisWord.take (basisLens.getD i 0)) ∈ Jbar.op :=
    wordS_mem g Jbar _ fun j hj => by
      obtain ⟨h1, h2⟩ := basisWord_letters_range j (List.mem_of_mem_take hj)
      exact hgJ j h1 h2
  have hP' : (wordS g (basisWord.take (basisLens.getD i 0))).unop⁻¹ ∈ Jbar := Jbar.inv_mem hP
  have h := conj_mem_Ebar hP' hg0
  rw [inv_inv] at h
  rw [eS, unop_mul, unop_mul, unop_inv, unop_op, ← mul_assoc]
  exact h

end Members

section Max2S

variable (g : ℕ → Cbar) (ι : NativeSporadic.B →* Sbp)

@[expose] noncomputable def zS : Sbp := ι DB

@[expose] noncomputable def zqS : Sbp := op xbar * (Dyadic.bridgeZE.map (eS g)).prod

@[expose] noncomputable def uS : Sbp :=
  ι (wordTwo cB dB bridgeU * (wordTwo cB dB bridgeV)⁻¹) *
    (WS g * ((WS g)⁻¹ * zS ι * WS g * op xbar) ^ 3 * zqS g)

@[expose] noncomputable def etaS : NativeSporadic.B →* Sbp :=
  (MulAut.conj (uS g ι)⁻¹).toMonoidHom.comp ι

theorem etaS_apply
    (s : NativeSporadic.B) : etaS g ι s = (uS g ι)⁻¹ * ι s * uS g ι := by
  simp [etaS]

variable (β : Cbar →* GL (Fin 4370) (ZMod 2))
  (hg : ∀ j < 26, ((betaRow β (op (g j)) : MatBˣ) : MatB) = Qn j)
  (hιβ : ∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹)
  (hx : op xbar = xS g)

include hιβ in
theorem betaRow_zS :
    ((betaRow β (zS ι) : MatBˣ) : MatB) = zm Tmat dMat := by
  rw [zS, hιβ, bMat_DB]; rfl

include hg hιβ hx in
theorem betaRow_kS :
    ((betaRow β ((WS g)⁻¹ * zS ι * WS g * op xbar) : MatBˣ) : MatB) =
    km Qn Tmat dMat := by
  rw [map_mul, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_mul,
    Matrix.coe_units_inv, betaRow_WS β g hg, betaRow_zS ι β hιβ, hx, betaRow_xS β g hg]
  rfl

theorem betaRow_list_prod (l : List Sbp) :
    ((betaRow β l.prod : MatBˣ) : MatB) = (l.map fun s => ((betaRow β s : MatBˣ) : MatB)).prod := by
  induction l with
  | nil => rw [List.prod_nil, map_one, Units.val_one, List.map_nil, List.prod_nil]
  | cons s l ih => rw [List.prod_cons, map_mul, Units.val_mul, ih, List.map_cons, List.prod_cons]

include hg hx in
theorem betaRow_zqS : ((betaRow β (zqS g) : MatBˣ) : MatB) = zqm Qn := by
  rw [zqS, map_mul, Units.val_mul, hx, betaRow_xS β g hg, betaRow_list_prod, List.map_map, zqm]
  exact congrArg _ (congrArg List.prod (List.map_congr_left fun i _ => betaRow_eS β g hg i))

theorem bMat_inv (s : NativeSporadic.B) : bMat s⁻¹ = (bMat s)⁻¹ :=
  (Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one])).symm

theorem bMat_wordTwo (w : List Bool) :
    bMat (wordTwo cB dB w) = wordTwo cMat dMat w := by
  rw [map_wordTwo, bMat_cB, bMat_dB]

include hg hιβ hx in
theorem betaRow_uS :
    ((betaRow β (uS g ι) : MatBˣ) : MatB) = um Qn Tmat cMat dMat := by
  have h1 : ((betaRow β (ι (wordTwo cB dB bridgeU * (wordTwo cB dB bridgeV)⁻¹)) : MatBˣ) : MatB) =
      Tmat * (wordTwo cMat dMat bridgeU * (wordTwo cMat dMat bridgeV)⁻¹) * Tmat⁻¹ := by
    rw [hιβ, map_mul, bMat_inv, bMat_wordTwo, bMat_wordTwo]
  have h2 : ((betaRow β (WS g * ((WS g)⁻¹ * zS ι * WS g * op xbar) ^ 3 * zqS g) : MatBˣ) :
      MatB) = uWm Qn Tmat dMat * zqm Qn := by
    rw [map_mul, Units.val_mul, betaRow_zqS g β hg hx, map_mul, Units.val_mul, map_pow,
      Units.val_pow_eq_pow_val, betaRow_WS β g hg, betaRow_kS g ι β hg hιβ hx]
    rfl
  rw [uS, map_mul, Units.val_mul, h1, h2]
  rfl

include hg hιβ hx in
theorem um_isUnit : IsUnit (um Qn Tmat cMat dMat) := by
  rw [← betaRow_uS g ι β hg hιβ hx]
  exact Units.isUnit _

include hg hιβ hx in
theorem C0m_inv :
    (C0m Qn Tmat cMat dMat)⁻¹ = Tmat⁻¹ * um Qn Tmat cMat dMat := by
  have hu := um_isUnit g ι β hg hιβ hx
  rw [C0m, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).1 hu)]

include hg hιβ hx in
theorem betaRow_etaS (s : NativeSporadic.B) :
    ((betaRow β (etaS g ι s) : MatBˣ) : MatB) =
      C0m Qn Tmat cMat dMat * bMat s * (C0m Qn Tmat cMat dMat)⁻¹ := by
  rw [etaS_apply, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    betaRow_uS g ι β hg hιβ hx, hιβ, C0m_inv g ι β hg hιβ hx, C0m]
  simp only [Matrix.mul_assoc]

end Max2S

theorem conj_pow_mat {C M : MatB} (h1 : C⁻¹ * C = 1) :
    ∀ n : ℕ, (C * M * C⁻¹) ^ n = C * M ^ n * C⁻¹
  | 0 => by
    rw [pow_zero, pow_zero, Matrix.mul_one]
    exact (Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)).symm
  | n + 1 => by
    rw [pow_succ, conj_pow_mat h1 n, pow_succ]
    calc C * M ^ n * C⁻¹ * (C * M * C⁻¹) = C * M ^ n * (C⁻¹ * C) * M * C⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = C * (M ^ n * M) * C⁻¹ := by rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem betaRow_op_list_prod (β : Cbar →* GL (Fin 4370) (ZMod 2)) (l : List Cbar) :
    ((betaRow β (op l.prod) : MatBˣ) : MatB) =
      (l.reverse.map fun y => ((betaRow β (op y) : MatBˣ) : MatB)).prod := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.prod_cons, op_mul, map_mul, Units.val_mul, ih, List.reverse_cons, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton]

theorem rowProdM_eq_prod (β : Cbar →* GL (Fin 4370) (ZMod 2)) (Qf : ℕ → MatB) (e : Fin 22 → Cbar)
    (he : ∀ k : Fin 22, ((betaRow β (op (e k)) : MatBˣ) : MatB) = Em Qf k) (r : ℕ)
    (c : Fin 22 → ZMod 2) (hc : ∀ j : Fin 22, c j = if r.testBit j then 1 else 0) :
    rowProdM Qf r = ((((List.finRange 22).map fun j => e j ^ (c j).val).reverse).map
      fun y => ((betaRow β (op y) : MatBˣ) : MatB)).prod := by
  rw [rowProdM, ← List.map_coe_finRange_eq_range, ← List.map_reverse, List.map_map,
    ← List.map_reverse, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
  simp only [Function.comp_apply, op_pow, map_pow, Units.val_pow_eq_pow_val, he, hc]
  by_cases ht : r.testBit j
  · rw [ite_eq_left ht, ite_eq_left ht]; exact (pow_one _).symm
  · rw [ite_eq_right ht, ite_eq_right ht]; exact (pow_zero _).symm

theorem wordIn_kernelWord {G : Type*} [Group G] (a b : G) :
    wordIn a b kernelWord = (a * b⁻¹ * b⁻¹ * a * a * b⁻¹) ^ 14 := by
  unfold wordIn kernelWord
  rw [List.map_flatten, List.prod_flatten, List.map_replicate, List.map_replicate,
    List.prod_replicate]
  simp [letterIn, mul_assoc]

theorem r1Rows_eq : ∀ i < 22, Max2.Native.r1Rows[i]! = quotRows1.getD i 0 := by decide

theorem r2Rows_eq : ∀ i < 22, Max2.Native.r2Rows[i]! = quotRows2.getD i 0 := by decide

theorem gramRows_eq : ∀ i < 22, CFSG.Monster.B.gramRows[i]! = Bin.gramRows.getD i 0 := by decide

section Max2Final

variable (β : Cbar →* GL (Fin 4370) (ZMod 2)) (hβ : Function.Injective β) (g : ℕ → Cbar)
  (hg : ∀ j < 26, ((betaRow β (op (g j)) : MatBˣ) : MatB) = Qn j)
  (hg0 : g 0 ∈ Ebar) (hgJ : ∀ j, 1 ≤ j → j ≤ 24 → g j ∈ Jbar)
  (ι : NativeSporadic.B →* Sbp)
  (hιβ : ∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹)

theorem betaRow_inj {β : Cbar →* GL (Fin 4370) (ZMod 2)} (hβ : Function.Injective β) {s t : Sbp}
    (h : ((betaRow β s : MatBˣ) : MatB) = ((betaRow β t : MatBˣ) : MatB)) : s = t :=
  betaRow_injective hβ (Units.ext h)

theorem mem_Jbar_iff_comm
    {y : Cbar} : y ∈ Jbar ↔ xbar * y = y * xbar := by
  rw [← centralizer_xbar, Subgroup.mem_centralizer_singleton_iff, eq_comm]

include hg hg0 hgJ in
theorem op_xbar_eq : op xbar = xS g :=
  xbar_eq_xS β g hg hg0 (hgJ 1 le_rfl (by norm_num)) (max2_matrix_facts (Qn_isUnit β g hg)).2.1

include hg hg0 hgJ in
theorem betaRow_xbar :
    ((betaRow β (op xbar) : MatBˣ) : MatB) = Xm Qn := by
  rw [op_xbar_eq β g hg hg0 hgJ, betaRow_xS β g hg]

include hg hg0 hgJ hιβ in
theorem betaRow_eta_cB :
    ((betaRow β (etaS g ι cB) : MatBˣ) : MatB) = G1m Qn Tmat cMat dMat := by
  rw [betaRow_etaS g ι β hg hιβ (op_xbar_eq β g hg hg0 hgJ), bMat_cB]
  rfl

include hg hg0 hgJ hιβ in
theorem betaRow_eta_dB :
    ((betaRow β (etaS g ι dB) : MatBˣ) : MatB) = G2m Qn Tmat cMat dMat := by
  rw [betaRow_etaS g ι β hg hιβ (op_xbar_eq β g hg hg0 hgJ), bMat_dB]
  rfl

include hβ hg hg0 hgJ in
theorem unop_mem_Jbar_of_comm
    {s : Sbp} {M : MatB} (hs : ((betaRow β s : MatBˣ) : MatB) = M)
    (hM : M * Xm Qn = Xm Qn * M) : s.unop ∈ Jbar := by
  refine mem_Jbar_iff_comm.2 ?_
  have h : op xbar * s = s * op xbar := by
    apply betaRow_inj hβ
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, hs, betaRow_xbar β g hg hg0 hgJ, hM]
  have h' := congrArg unop h
  rw [unop_mul, unop_mul, unop_op] at h'
  exact h'.symm

include hβ hg hg0 hgJ hιβ in
theorem eta_cB_mem_Jbar :
    (etaS g ι cB).unop ∈ Jbar := by
  obtain ⟨-, -, -, -, -, -, -, hG1X, -⟩ := max2_matrix_facts (Qn_isUnit β g hg)
  exact unop_mem_Jbar_of_comm β hβ g hg hg0 hgJ (betaRow_eta_cB β g hg hg0 hgJ ι hιβ) hG1X

include hβ hg hg0 hgJ hιβ in
theorem eta_dB_mem_Jbar :
    (etaS g ι dB).unop ∈ Jbar := by
  obtain ⟨-, -, -, -, -, -, -, -, hG2X, -⟩ := max2_matrix_facts (Qn_isUnit β g hg)
  exact unop_mem_Jbar_of_comm β hβ g hg hg0 hgJ (betaRow_eta_dB β g hg hg0 hgJ ι hιβ) hG2X

include hg in
theorem betaRow_op_eS (k : Fin 22) :
    ((betaRow β (op (eS g k).unop) : MatBˣ) : MatB) = Em Qn k := by
  rw [op_unop, betaRow_eS β g hg]

theorem exp_eq_of_row {κ : Type*} [Fintype κ] [DecidableEq κ] {v : κ → ZMod 2}
    {A B X : Matrix κ κ (ZMod 2)} {n m : ℕ} (hn : n < 2) (hm : m < 2)
    (hX : v ᵥ* X ≠ v) (hXB : X * B = B * X) (hu : IsUnit (A * B))
    (hgrp : B * A = X ^ n * A * B) (hrow : v ᵥ* (A * B) = v ᵥ* (B * X ^ m * A)) : n = m := by
  have hXmB : X ^ m * B = B * X ^ m := (Commute.pow_left hXB m).eq
  have e1 : B * X ^ m * A = X ^ (m + n) * (A * B) := by
    rw [hXmB.symm, Matrix.mul_assoc, hgrp, pow_add]
    simp only [Matrix.mul_assoc]
  rw [e1] at hrow
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have e2 := congrArg (fun w => w ᵥ* (A * B)⁻¹) hrow
  simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.mul_one, Matrix.vecMul_one] at e2
  by_contra hne
  have hk : m + n = 1 := by omega
  rw [hk, pow_one] at e2
  exact hX e2.symm

theorem psi_eq_of_pair (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (Gm Hm : Matrix (Fin 22) (Fin 22) (ZMod 2)) (hGH : Gm * Hm = 1)
    (hG : ∀ i j, e i * e j = e j * e i * xbar ^ (Gm i j).val) (y : Ebar) (r : Fin 22 → ZMod 2)
    (hy : ∀ j, bW (Multiplicative.toAdd (psiBar y)) (Multiplicative.toAdd (psiBar ⟨e j, he j⟩)) =
      ∑ l, r l * Gm l j) :
    psiBar y = Multiplicative.ofAdd (∑ l, r l • Multiplicative.toAdd (psiBar ⟨e l, he l⟩)) := by
  have hBG : ∀ i j, bW (Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
      (Multiplicative.toAdd (psiBar ⟨e j, he j⟩)) = Gm i j := by
    intro i j
    have h1 := Ebar_mul_eq_mul_xbar_pow ⟨e i, he i⟩ ⟨e j, he j⟩
    rw [hG i j] at h1
    exact (eq_of_xbar_pow_val_eq (mul_left_cancel h1)).symm
  have hli := linearIndependent_psi_of_gram e he Gm Hm hGH hG
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  obtain ⟨c, hc⟩ : ∃ c : Fin 22 → ZMod 2, Multiplicative.toAdd (psiBar y) =
      ∑ k, c k • Multiplicative.toAdd (psiBar ⟨e k, he k⟩) := by
    refine ⟨(psiBasis e he hli).repr (Multiplicative.toAdd (psiBar y)), ?_⟩
    conv_lhs => rw [← (psiBasis e he hli).sum_repr (Multiplicative.toAdd (psiBar y))]
    simp only [psiBasis_apply]
  have hcG : Matrix.vecMul (c - r) Gm = 0 := by
    funext j
    have h := congrArg (fun x => bW x (Multiplicative.toAdd (psiBar ⟨e j, he j⟩))) hc
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hBG,
      hy j] at h
    rw [Matrix.sub_vecMul, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact h.symm
  have hcr : c = r := by
    have e1 : c - r = Matrix.vecMul (Matrix.vecMul (c - r) Gm) Hm := by
      rw [Matrix.vecMul_vecMul, hGH, Matrix.vecMul_one]
    rw [hcG, Matrix.zero_vecMul] at e1
    exact sub_eq_zero.1 e1
  rw [hc, hcr]

theorem betaRow_comm_pow (β : Cbar →* GL (Fin 4370) (ZMod 2)) {y z : Cbar} {n : ℕ}
    (h : y * z = z * y * xbar ^ n) :
    ((betaRow β (op z) : MatBˣ) : MatB) * ((betaRow β (op y) : MatBˣ) : MatB) =
      ((betaRow β (op xbar) : MatBˣ) : MatB) ^ n * ((betaRow β (op y) : MatBˣ) : MatB) *
        ((betaRow β (op z) : MatBˣ) : MatB) := by
  have := congrArg (fun w : Cbar => ((betaRow β (op w) : MatBˣ) : MatB)) h
  simp only [op_mul, op_pow, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val] at this
  simpa only [Matrix.mul_assoc] using this

include hg hg0 hgJ in
theorem gram_rel (i j : Fin 22)
    (_hij : i < j) :
    (eS g i).unop * (eS g j).unop =
      (eS g j).unop * (eS g i).unop * xbar ^ (Max2.decMat CFSG.Monster.B.gramRows i j).val := by
  have hXm := betaRow_xbar β g hg hg0 hgJ
  set e : Fin 22 → Cbar := fun i => (eS g i).unop with he_def
  have he : ∀ i, e i ∈ Ebar := fun i => eS_mem g hg0 hgJ i
  have hEm : ∀ k : Fin 22, ((betaRow β (op (e k)) : MatBˣ) : MatB) = Em Qn k :=
    betaRow_op_eS β g hg
  have hEunit : ∀ k : Fin 22, IsUnit (Em Qn k) := fun k => by
    rw [← hEm k]; exact Units.isUnit _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hvX, hgram, -⟩ :=
    max2_matrix_facts (Qn_isUnit β g hg)
  change e i * e j = e j * e i * xbar ^ (Max2.decMat CFSG.Monster.B.gramRows i j).val
  have hpair := Ebar_mul_eq_mul_xbar_pow ⟨e i, he i⟩ ⟨e j, he j⟩
  set bb := (bW (Multiplicative.toAdd (psiBar ⟨e i, he i⟩))
    (Multiplicative.toAdd (psiBar ⟨e j, he j⟩))).val with hbb
  have hb2 : bb < 2 := ZMod.val_lt _
  have h1 : Em Qn j * Em Qn i = Xm Qn ^ bb * Em Qn i * Em Qn j := by
    have := congrArg (fun y : Cbar => ((betaRow β (op y) : MatBˣ) : MatB)) hpair
    simp only [op_mul, op_pow, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, hEm,
      hXm] at this
    simpa only [Matrix.mul_assoc] using this
  have hXE : Xm Qn * Em Qn j = Em Qn j * Xm Qn := by
    have := congrArg (fun y : Cbar => ((betaRow β (op y) : MatBˣ) : MatB))
      (xbar_comm_of_mem_Ebar (he j))
    simpa only [op_mul, map_mul, Units.val_mul, hEm, hXm] using this
  have hbg : bb = Dyadic.rowBitK Bin.gramRows i j :=
    exp_eq_of_row hb2 (by unfold Dyadic.rowBitK; split_ifs <;> norm_num) hvX hXE
      ((hEunit i).mul (hEunit j)) h1 (hgram i j i.2 j.2)
  have hval : (Max2.decMat CFSG.Monster.B.gramRows i j).val = Dyadic.rowBitK Bin.gramRows i j := by
    rw [Max2.decMat, Matrix.of_apply, gramRows_eq i i.2, Code.bvec_apply, Dyadic.rowBitK]
    by_cases ht : (Bin.gramRows.getD i 0).testBit j
    · rw [ite_eq_left ht, ite_eq_left ht]; rfl
    · rw [ite_eq_right ht, ite_eq_right ht]; rfl
  rw [hval, ← hbg]
  exact hpair

theorem decMat_eq_rowBitK {R : Array ℕ} {R' : List ℕ} (hR : ∀ i < 22, R[i]! = R'.getD i 0)
    (i l : Fin 22) : Max2.decMat R i l = (Dyadic.rowBitK R' i l : ZMod 2) := by
  rw [Max2.decMat, Matrix.of_apply, hR i i.2, Code.bvec_apply, Dyadic.rowBitK]
  split_ifs <;> simp

include hg hg0 hgJ in
theorem conj_rows
    (s : Sbp) (G' : MatB) (rows : Array ℕ) (rows' : List ℕ)
    (hrows : ∀ i < 22, rows[i]! = rows'.getD i 0) (hs : ((betaRow β s : MatBˣ) : MatB) = G')
    (h : s.unop⁻¹ ∈ Jbar)
    (hc : ∀ i j, i < 22 → j < 22 →
      CFSG.KC.BM.e0 ᵥ* (G'⁻¹ * Em Qn i * G' * Em Qn j) =
      CFSG.KC.BM.e0 ᵥ* (Em Qn j * Xm Qn ^ Dyadic.actK rows' i j * (G'⁻¹ * Em Qn i * G')))
    (i : Fin 22) :
    psiBar ⟨(s.unop⁻¹)⁻¹ * (eS g i).unop * s.unop⁻¹, conj_mem_Ebar h (eS_mem g hg0 hgJ i)⟩ =
      Multiplicative.ofAdd (∑ j, Max2.decMat rows i j •
        Multiplicative.toAdd (psiBar ⟨(eS g j).unop, eS_mem g hg0 hgJ j⟩)) := by
  have hXm := betaRow_xbar β g hg hg0 hgJ
  set e : Fin 22 → Cbar := fun i => (eS g i).unop with he_def
  have he : ∀ i, e i ∈ Ebar := fun i => eS_mem g hg0 hgJ i
  have hEm : ∀ k : Fin 22, ((betaRow β (op (e k)) : MatBˣ) : MatB) = Em Qn k :=
    betaRow_op_eS β g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hvX, -⟩ := max2_matrix_facts (Qn_isUnit β g hg)
  have hG := gram_rel_of_lt (Max2.decMat CFSG.Monster.B.gramRows) gram_symm gram_diag
    (gram_rel β g hg hg0 hgJ)
  have hGH : Max2.decMat CFSG.Monster.B.gramRows * Max2.decMat gramInvRows = 1 := by
    rw [← decMat_mulRows, gram_mul_inv_check, decMat_idRows]
  have hfE := conj_mem_Ebar h (he i)
  change psiBar ⟨(s.unop⁻¹)⁻¹ * e i * s.unop⁻¹, hfE⟩ =
    Multiplicative.ofAdd (∑ j, Max2.decMat rows i j • Multiplicative.toAdd (psiBar ⟨e j, he j⟩))
  refine psi_eq_of_pair e he _ _ hGH hG _ (fun l => Max2.decMat rows i l) fun j => ?_
  have hop : op ((s.unop⁻¹)⁻¹ * e i * s.unop⁻¹) = s⁻¹ * op (e i) * s := by
    rw [inv_inv, op_mul, op_mul, op_inv, op_unop, mul_assoc]
  have hF : ((betaRow β (op ((s.unop⁻¹)⁻¹ * e i * s.unop⁻¹)) : MatBˣ) : MatB) =
      G'⁻¹ * Em Qn i * G' := by
    rw [hop, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hs,
      hEm i]
  have hpair := Ebar_mul_eq_mul_xbar_pow ⟨_, hfE⟩ ⟨e j, he j⟩
  set bb := (bW (Multiplicative.toAdd (psiBar ⟨_, hfE⟩))
    (Multiplicative.toAdd (psiBar ⟨e j, he j⟩))).val with hbb
  have h1 := betaRow_comm_pow β (y := (s.unop⁻¹)⁻¹ * e i * s.unop⁻¹) (z := e j) hpair
  rw [hF, hEm j, hXm] at h1
  have hXE : Xm Qn * Em Qn j = Em Qn j * Xm Qn := by
    have := congrArg (fun y : Cbar => ((betaRow β (op y) : MatBˣ) : MatB))
      (xbar_comm_of_mem_Ebar (he j))
    simpa only [op_mul, map_mul, Units.val_mul, hEm, hXm] using this
  have hu : IsUnit (G'⁻¹ * Em Qn i * G' * Em Qn j) := by
    rw [← hF, ← hEm j]
    exact (Units.isUnit _).mul (Units.isUnit _)
  have hbg : bb = Dyadic.actK rows' i j :=
    exp_eq_of_row (ZMod.val_lt _) (ZMod.val_lt _) hvX hXE hu h1 (hc i j i.2 j.2)
  apply ZMod.val_injective
  rw [← hbb, hbg, Dyadic.actK, ← Fin.sum_univ_eq_sum_range]
  refine congrArg ZMod.val (Finset.sum_congr rfl fun l _ => ?_)
  rw [decMat_eq_rowBitK hrows, decMat_eq_rowBitK gramRows_eq, Nat.cast_mul]

theorem cB_mul_self :
    cB * cB = 1 := by
  apply bMat_injective
  rw [map_mul, bMat_cB, map_one]
  exact pinned_facts.1

theorem cB_inv :
    cB⁻¹ = cB := inv_eq_of_mul_eq_one_right cB_mul_self

theorem etaS_cB_inv :
    (etaS g ι cB)⁻¹ = etaS g ι cB := by
  rw [← map_inv (etaS g ι) cB, cB_inv]

theorem op_kernelWord_eta :
    op (wordIn (etaS g ι cB).unop⁻¹ (etaS g ι dB).unop⁻¹ kernelWord) =
      (etaS g ι dB * etaS g ι cB * etaS g ι cB * etaS g ι dB * etaS g ι dB * etaS g ι cB) ^ 14 := by
  rw [wordIn_kernelWord, op_pow]
  refine congrArg (· ^ 14) ?_
  simp only [op_mul, op_inv, op_unop, inv_inv, etaS_cB_inv g ι, mul_assoc]

include hg hg0 hgJ hιβ in
theorem betaRow_kernelWord :
    ((betaRow β (op (wordIn (etaS g ι cB).unop⁻¹ (etaS g ι dB).unop⁻¹ kernelWord)) : MatBˣ) :
      MatB) = Km Qn Tmat cMat dMat := by
  rw [wordIn_kernelWord, op_pow, map_pow, Units.val_pow_eq_pow_val]
  simp only [op_mul, op_inv, op_unop, inv_inv, etaS_cB_inv g ι]
  simp only [map_mul, Units.val_mul, betaRow_eta_cB β g hg hg0 hgJ ι hιβ,
    betaRow_eta_dB β g hg hg0 hgJ ι hιβ]
  rw [Km]
  simp only [Matrix.mul_assoc]

include hβ hg hg0 hgJ hιβ in
theorem Jbar_le_eta :
    Jbar ≤ ((Subgroup.closure ({cB, dB} : Set NativeSporadic.B)).map (etaS g ι)).unop := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hc1, hc2, hK1, hKX, -⟩ := max2_matrix_facts (Qn_isUnit β g hg)
  set K := Subgroup.closure ({cB, dB} : Set NativeSporadic.B) with hK
  set G := (K.map (etaS g ι)).unop with hG
  set a' : Cbar := (etaS g ι cB).unop⁻¹ with ha'
  set b' : Cbar := (etaS g ι dB).unop⁻¹ with hb'
  have hcK : cB ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hdK : dB ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have haG : a' ∈ G := by
    show op a' ∈ K.map (etaS g ι)
    rw [ha', op_inv, op_unop, ← map_inv]
    exact Subgroup.mem_map_of_mem _ (K.inv_mem hcK)
  have hbG : b' ∈ G := by
    show op b' ∈ K.map (etaS g ι)
    rw [hb', op_inv, op_unop, ← map_inv]
    exact Subgroup.mem_map_of_mem _ (K.inv_mem hdK)
  have haJ : a' ∈ Jbar := Jbar.inv_mem (eta_cB_mem_Jbar β hβ g hg hg0 hgJ ι hιβ)
  have hbJ : b' ∈ Jbar := Jbar.inv_mem (eta_dB_mem_Jbar β hβ g hg hg0 hgJ ι hιβ)
  have hR1 := conj_rows β g hg hg0 hgJ (etaS g ι cB) (G1m Qn Tmat cMat dMat)
    Max2.Native.r1Rows quotRows1 r1Rows_eq (betaRow_eta_cB β g hg hg0 hgJ ι hιβ) haJ hc1
  have hR2 := conj_rows β g hg hg0 hgJ (etaS g ι dB) (G2m Qn Tmat cMat dMat)
    Max2.Native.r2Rows quotRows2 r2Rows_eq (betaRow_eta_dB β g hg hg0 hgJ ι hιβ) hbJ hc2
  have hKw := betaRow_kernelWord β g hg hg0 hgJ ι hιβ
  have hw1 : wordIn a' b' kernelWord ≠ 1 := by
    intro h
    apply hK1
    rw [← hKw, h, op_one, map_one, Units.val_one]
  have hwx : wordIn a' b' kernelWord ≠ xbar := by
    intro h
    apply hKX
    rw [← hKw, h, betaRow_xbar β g hg hg0 hgJ]
  have key := Jbar_le_of_max2_cert G haG hbG haJ hbJ (fun i => (eS g i).unop)
    (fun i => eS_mem g hg0 hgJ i) (gram_rel β g hg hg0 hgJ)
  rw [Max2.coe_R1u] at key
  rw [Max2.coe_R2u] at key
  exact key hR1 hR2 hw1 hwx

end Max2Final

theorem iota_surjective
    (β : Cbar →* GL (Fin 4370) (ZMod 2)) (hβ : Function.Injective β)
    (g : ℕ → Cbar) (hg : ∀ j < 26, ((betaRow β (op (g j)) : MatBˣ) : MatB) = Qn j)
    (hτ : g 25 = taubar) (hg0 : g 0 ∈ Ebar) (hgJ : ∀ j, 1 ≤ j → j ≤ 24 → g j ∈ Jbar)
    (ι : NativeSporadic.B →* Sbp)
    (hιβ : ∀ X, ((betaRow β (ι X) : MatBˣ) : MatB) = Tmat * bMat X * Tmat⁻¹) :
    Function.Surjective ι := by
  have hJle := Jbar_le_eta β hβ g hg hg0 hgJ ι hιβ
  obtain ⟨hX2, hX1, -, -, -, -, huzu, -, -, -, -, -, -, -, -, hX'X, hWY⟩ :=
    max2_matrix_facts (Qn_isUnit β g hg)
  have hx := xbar_eq_xS β g hg hg0 (hgJ 1 le_rfl (by norm_num)) hX1
  have hXm : ((betaRow β (op xbar) : MatBˣ) : MatB) = Xm Qn := by rw [hx, betaRow_xS β g hg]
  obtain ⟨-, -, hd48, -, -, -, -, -, hDW⟩ := pinned_facts
  have hQ3 : Qn 25 ^ 3 = 1 := by rw [Qn_25]; exact pair_matrix_facts.2.2.2.2.2.2.2.1
  have hτm : ((betaRow β (op taubar) : MatBˣ) : MatB) = Qn 25 := by rw [← hτ, hg 25 (by norm_num)]
  have hQinv : (Qn 25)⁻¹ = Qn 25 ^ 2 := by
    apply Matrix.inv_eq_right_inv
    rw [← pow_succ']; exact hQ3
  set K := Subgroup.closure ({cB, dB} : Set NativeSporadic.B)
  set u := uS g ι
  have hC0inv := C0m_inv g ι β hg hιβ hx
  have hu := um_isUnit g ι β hg hιβ hx
  have hud := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 Tmat_isUnit
  have hC01 : (C0m Qn Tmat cMat dMat)⁻¹ * C0m Qn Tmat cMat dMat = 1 := by
    rw [hC0inv, C0m]
    calc Tmat⁻¹ * um Qn Tmat cMat dMat * ((um Qn Tmat cMat dMat)⁻¹ * Tmat)
        = Tmat⁻¹ * (um Qn Tmat cMat dMat * (um Qn Tmat cMat dMat)⁻¹) * Tmat := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hud, Matrix.mul_one, Matrix.nonsing_inv_mul _ hTd]
  have hXC : Xm Qn = C0m Qn Tmat cMat dMat * dMat ^ 24 * (C0m Qn Tmat cMat dMat)⁻¹ := by
    rw [← huzu, hC0inv, C0m, zm]
    simp only [Matrix.mul_assoc]
  have hηW : ((betaRow β (u⁻¹ * ι W'B * u) : MatBˣ) : MatB) =
      C0m Qn Tmat cMat dMat * W'm dMat genA₂ * (C0m Qn Tmat cMat dMat)⁻¹ := by
    rw [← etaS_apply, betaRow_etaS g ι β hg hιβ hx, bMat_W'B]
  have hx'm : ((betaRow β ((op taubar)⁻¹ * op xbar * op taubar) : MatBˣ) : MatB) = X'm Qn := by
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hτm, hXm,
      hQinv]
    rfl
  have hS : Subgroup.closure (insert (op taubar) (Jbar.op : Set Sbp)) = ⊤ := by
    have h := congrArg Subgroup.op closure_insert_taubar_Jbar
    rw [Subgroup.op_closure, Subgroup.op_top] at h
    rw [← h]
    congr 1
    ext s
    simp only [Set.mem_insert_iff, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_op]
    constructor
    · rintro (h | h)
      · left; rw [h, unop_op]
      · right; exact h
    · rintro (h | h)
      · left; rw [← op_unop s, h]
      · right; exact h
  have hJ : ∀ s, s ∈ Jbar.op ↔ s * op xbar = op xbar * s := by
    intro s
    rw [Subgroup.mem_op, mem_Jbar_iff_comm]
    constructor
    · intro h
      have := congrArg op h
      rwa [op_mul, op_mul, op_unop] at this
    · intro h
      have := congrArg unop h
      rwa [unop_mul, unop_mul, unop_op] at this
  have hJK : ∀ s ∈ Jbar.op, ∃ k ∈ K, s = u⁻¹ * ι k * u := by
    intro s hs
    obtain ⟨k, hk, hks⟩ := hJle hs
    exact ⟨k, hk, by rw [← etaS_apply]; exact hks.symm⟩
  have hx2 : op xbar * op xbar = 1 := by
    apply betaRow_inj hβ
    rw [map_mul, Units.val_mul, hXm, ← sq, hX2, map_one, Units.val_one]
  have hcomm : ((op taubar)⁻¹ * op xbar * op taubar) * op xbar =
      op xbar * ((op taubar)⁻¹ * op xbar * op taubar) := by
    apply betaRow_inj hβ
    rw [(betaRow β).map_mul ((op taubar)⁻¹ * op xbar * op taubar) (op xbar),
      (betaRow β).map_mul (op xbar) ((op taubar)⁻¹ * op xbar * op taubar), Units.val_mul,
      Units.val_mul, hx'm, hXm, hX'X]
  have hDD : DB * DB = 1 := by
    apply bMat_injective
    rw [map_mul, bMat_DB, map_one, ← pow_add]
    exact hd48
  have hWW : W'B * W'B = 1 := by
    rw [W'B]
    calc bA₂⁻¹ * DB * bA₂ * (bA₂⁻¹ * DB * bA₂) = bA₂⁻¹ * (DB * DB) * bA₂ := by group
      _ = 1 := by rw [hDD, mul_one, inv_mul_cancel]
  have hw : (u⁻¹ * ι W'B * u) * (u⁻¹ * ι W'B * u) = 1 := by
    calc (u⁻¹ * ι W'B * u) * (u⁻¹ * ι W'B * u) = u⁻¹ * ι (W'B * W'B) * u := by
          rw [map_mul]; group
      _ = 1 := by rw [hWW, map_one, mul_one, inv_mul_cancel]
  have hk : (op xbar * (u⁻¹ * ι W'B * u)) ^ (2 * 2 + 1) = 1 := by
    apply betaRow_inj hβ
    rw [map_pow, map_mul, Units.val_pow_eq_pow_val, Units.val_mul, hXm, hηW, hXC, map_one,
      Units.val_one]
    have e : C0m Qn Tmat cMat dMat * dMat ^ 24 * (C0m Qn Tmat cMat dMat)⁻¹ *
        (C0m Qn Tmat cMat dMat * W'm dMat genA₂ * (C0m Qn Tmat cMat dMat)⁻¹) =
        C0m Qn Tmat cMat dMat * (dMat ^ 24 * W'm dMat genA₂) * (C0m Qn Tmat cMat dMat)⁻¹ := by
      calc _ = C0m Qn Tmat cMat dMat * dMat ^ 24 *
            ((C0m Qn Tmat cMat dMat)⁻¹ * C0m Qn Tmat cMat dMat) * W'm dMat genA₂ * (C0m Qn Tmat cMat dMat)⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hC01, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, conj_pow_mat hC01, W'm, sq, show 2 * 2 + 1 = 5 by norm_num, hDW, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_det_of_left_inverse hC01))]
  have hl : ((u⁻¹ * ι W'B * u) * ((op taubar)⁻¹ * op xbar * op taubar)) ^ (2 * 2 + 1) = 1 := by
    apply betaRow_inj hβ
    rw [map_pow, map_mul, Units.val_pow_eq_pow_val, Units.val_mul, hηW, hx'm, map_one,
      Units.val_one]
    have e : C0m Qn Tmat cMat dMat * W'm dMat genA₂ * (C0m Qn Tmat cMat dMat)⁻¹ * X'm Qn =
        C0m Qn Tmat cMat dMat * (W'm dMat genA₂ * Y'm Qn Tmat cMat dMat) *
          (C0m Qn Tmat cMat dMat)⁻¹ := by
      rw [Y'm]
      calc _ = C0m Qn Tmat cMat dMat * W'm dMat genA₂ * (C0m Qn Tmat cMat dMat)⁻¹ * X'm Qn *
            (C0m Qn Tmat cMat dMat * (C0m Qn Tmat cMat dMat)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_det_of_left_inverse hC01)), Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [e, conj_pow_mat hC01, show 2 * 2 + 1 = 5 by norm_num, hWY, Matrix.mul_one,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_det_of_left_inverse hC01))]
  exact surjective_of_transfer ι u K hS hJ hJK hx2 hcomm W'B hw hk hl

theorem isSimpleGroup_B_of
    (β : Cbar →* GL (Fin 4370) (ZMod 2)) (hβ : Function.Injective β)
    (g : ℕ → Cbar) (hg : ∀ j < 26, ((betaRow β (op (g j)) : MatBˣ) : MatB) = Qn j)
    (hτ : g 25 = taubar) (hg0 : g 0 ∈ Ebar) (hgJ : ∀ j, 1 ≤ j → j ≤ 24 → g j ∈ Jbar)
    (a : Sbp) (ha : ((betaRow β a : MatBˣ) : MatB) = Fmat) : IsSimpleGroup NativeSporadic.B := by
  obtain ⟨ι, hι, hιβ⟩ := exists_iota β g hg hβ hτ a ha
  exact isSimpleGroup_of_bijective ι hι (iota_surjective β hβ g hg hτ hg0 hgJ ι hιβ)

end CFSG.Monster.B
