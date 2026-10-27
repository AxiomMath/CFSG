module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.Model
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RepNontriv
import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
import CFSG.ClassicalInvolution.SL2Facts
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module Matrix CFSG.Open CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
open CFSG.QuasithinUnique.Setup.SL2Modules (uElt lElt dElt)
open scoped MatrixGroups

variable {K : Type} [Field K]

section SL2

theorem dElt_mul (a b : Kˣ) : dElt (a * b) = dElt a * dElt b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [dElt, Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul, mul_comm]

theorem dElt_conj_uElt (z : Kˣ) (s : K) :
    dElt z * uElt s * (dElt z)⁻¹ = uElt ((z : K) ^ 2 * s) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [dElt, uElt, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring

theorem dElt_inv_conj_lElt (z : Kˣ) (s : K) :
    (dElt z)⁻¹ * lElt s * dElt z = lElt ((z : K) ^ 2 * s) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [dElt, lElt, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring

theorem uElt_neg (s : K) : uElt (-s) = (uElt s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← CFSG.QuasithinUnique.Setup.SL2Modules.uElt_add, neg_add_cancel,
    CFSG.QuasithinUnique.Setup.SL2Modules.uElt_zero]

theorem lElt_add (s t : K) : lElt (s + t) = lElt s * lElt t := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [lElt, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lElt_neg (s : K) : lElt (-s) = (lElt s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← lElt_add, neg_add_cancel]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lElt]

theorem exists_unit_sq_ne_one [Fintype K] [CharP K 2] (hK : 3 ≤ Fintype.card K) :
    ∃ z : Kˣ, (z : K) ^ 2 ≠ 1 := by
  classical
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := fun a _ => by
      by_cases h0 : a = 0
      · simp [h0]
      · simp [h a h0]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ] at this
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨Units.mk0 a ha0, fun h => ha1 ?_⟩
  have h2 : (a - 1) ^ 2 = 0 := by
    simp only [Units.val_mk0] at h
    have h3 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h - (a - 1) * h3
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  exact sub_eq_zero.mp this

theorem sl2_fix_of_dElt_fix [Fintype K] [CharP K 2] (hK : 3 ≤ Fintype.card K) {Y : Type*}
    [AddCommGroup Y] [Module K Y] (σ : SL(2, K) →* Module.End K Y) (W : Submodule K Y)
    (hW : ∀ g, ∀ w ∈ W, σ g w ∈ W) (hd : ∀ c : Kˣ, ∀ w ∈ W, σ (dElt c) w = w) :
    ∀ g, ∀ w ∈ W, σ g w = w := by
  let S : Subgroup SL(2, K) :=
    { carrier := {g | ∀ w ∈ W, σ g w = w}
      mul_mem' := fun {a b} ha hb w hw => by
        rw [map_mul, Module.End.mul_apply, hb w hw, ha w hw]
      one_mem' := fun w _ => by rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha w hw => by
        have h1 := ha _ (hW a⁻¹ w hw)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h1
        exact h1.symm }
  have hcomm : ∀ a b : SL(2, K), a ∈ S → ∀ w ∈ W, σ (a * b * a⁻¹ * b⁻¹) w = w := by
    intro a b ha w hw
    have h1 : σ b⁻¹ w ∈ W := hW _ w hw
    calc σ (a * b * a⁻¹ * b⁻¹) w = σ (a * b) (σ a⁻¹ (σ b⁻¹ w)) := by
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      _ = σ (a * b) (σ b⁻¹ w) := by rw [S.inv_mem ha _ h1]
      _ = σ (a * b * b⁻¹) w := by rw [map_mul σ (a * b) b⁻¹, Module.End.mul_apply]
      _ = w := by rw [mul_inv_cancel_right, ha w hw]
  obtain ⟨z, hz⟩ := exists_unit_sq_ne_one hK
  have hz' : (z : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hdS : ∀ c : Kˣ, dElt c ∈ S := fun c w hw => hd c w hw
  have hU : ∀ t : K, uElt t ∈ S := by
    intro t
    set s := t / ((z : K) ^ 2 - 1)
    have hst : uElt t = (dElt z * uElt s * (dElt z)⁻¹) * (uElt s)⁻¹ := by
      rw [dElt_conj_uElt, ← uElt_neg, ← CFSG.QuasithinUnique.Setup.SL2Modules.uElt_add]
      congr 1
      rw [show (z : K) ^ 2 * s + -s = ((z : K) ^ 2 - 1) * s by ring, mul_div_cancel₀ _ hz']
    rw [hst]
    exact hcomm _ _ (hdS z)
  have hL : ∀ t : K, lElt t ∈ S := by
    intro t
    set s := t / ((z : K) ^ 2 - 1)
    have hst : lElt t = ((dElt z)⁻¹ * lElt s * dElt z) * (lElt s)⁻¹ := by
      rw [dElt_inv_conj_lElt, ← lElt_neg, ← lElt_add]
      congr 1
      rw [show (z : K) ^ 2 * s + -s = ((z : K) ^ 2 - 1) * s by ring, mul_div_cancel₀ _ hz']
    rw [hst]
    have := hcomm (dElt z)⁻¹ (lElt s) (S.inv_mem (hdS z))
    rwa [inv_inv] at this
  have htop : S = ⊤ := by
    rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower,
      Subgroup.closure_le]
    rintro g (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact hU t
    · exact hL t
  intro g w hw
  have hg : g ∈ S := htop ▸ Subgroup.mem_top g
  exact hg w hw

end SL2

section Semisimple

variable {Y : Type*} [AddCommGroup Y] [Module K Y]

theorem pow_pred_idem {P : Module.End K Y} {q : ℕ} (hq : 2 ≤ q) (hP : P ^ q = P) :
    P ^ (q - 1) * P ^ (q - 1) = P ^ (q - 1) ∧ P * P ^ (q - 1) = P ∧ P ^ (q - 1) * P = P := by
  have h1 : P * P ^ (q - 1) = P := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hP]
  have h2 : P ^ (q - 1) * P = P := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega), hP]
  refine ⟨?_, h1, h2⟩
  rw [← pow_add, show q - 1 + (q - 1) = q + (q - 2) by omega, pow_add, hP, ← pow_succ',
    show q - 2 + 1 = q - 1 by omega]

end Semisimple

section Torus

@[expose] noncomputable def dEltHom : Kˣ →* SL(2, K) where
  toFun := dElt
  map_one' := dElt_one
  map_mul' := dElt_mul

@[expose] noncomputable def dSlotHom (l : Fin 3) : Kˣ →* StatedSp 3 K :=
  (slotSL l).comp dEltHom

theorem dSlotHom_apply (l : Fin 3) (c : Kˣ) : dSlotHom l c = dSlot l c := rfl

variable [Fintype K] [CharP K 2]

theorem dSlot_pow_card (l : Fin 3) (c : Kˣ) : dSlot l c ^ Fintype.card K = dSlot l c := by
  rw [← dSlotHom_apply, ← map_pow]
  congr 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, FiniteField.pow_card]

theorem dSlot_commute (l m : Fin 3) (c c' : Kˣ) : Commute (dSlot l c) (dSlot m c') := by
  rw [dSlot_eq_levi, dSlot_eq_levi]
  exact levi_diagGL_commute _ _

theorem sub_one_pow_two_pow {Y : Type*} [AddCommGroup Y] [Module K Y] (A : Module.End K Y)
    (n : ℕ) : (A - 1) ^ (2 ^ n) = A ^ (2 ^ n) - 1 := by
  have h2 : (2 : Module.End K Y) = 0 := by
    rw [← map_ofNat (algebraMap K (Module.End K Y)) 2, CharTwo.two_eq_zero, map_zero]
  have hneg : (-1 : Module.End K Y) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
  have hsq : ∀ B : Module.End K Y, (B - 1) ^ 2 = B ^ 2 - 1 := by
    intro B
    have e : (B - 1) ^ 2 = B ^ 2 - 2 * B + 1 := by noncomm_ring
    rw [e, h2, zero_mul, sub_zero, sub_eq_add_neg, hneg]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, hsq, ← pow_mul]

variable {Y : Type} [AddCommGroup Y] [Module K Y]

theorem torus_pow_card (ρ : Representation K (StatedSp 3 K) Y) (l : Fin 3) (c : Kˣ) :
    (ρ (dSlot l c) - 1) ^ Fintype.card K = ρ (dSlot l c) - 1 := by
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [hn, sub_one_pow_two_pow, ← map_pow, ← hn, dSlot_pow_card]

@[expose] def fixT (ρ : Representation K (StatedSp 3 K) Y) (l : Fin 3) : Submodule K Y where
  carrier := {y | ∀ c : Kˣ, ρ (dSlot l c) y = y}
  add_mem' {a b} ha hb c := by rw [map_add, ha c, hb c]
  zero_mem' c := map_zero _
  smul_mem' r y hy c := by rw [map_smul, hy c]

@[expose] def SingleCoord (ρ : Representation K (StatedSp 3 K) Y) : Prop :=
  ∀ l m : Fin 3, l ≠ m → fixT ρ l ⊔ fixT ρ m = ⊤

theorem torus_mul_eq_zero {ρ : Representation K (StatedSp 3 K) Y} (hsc : SingleCoord ρ)
    {l m : Fin 3} (hlm : l ≠ m) (c c' : Kˣ) :
    (ρ (dSlot l c) - 1) * (ρ (dSlot m c') - 1) = 0 := by
  ext y
  have hy : y ∈ fixT ρ l ⊔ fixT ρ m := by rw [hsc l m hlm]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  have hcomm : (ρ (dSlot l c) - 1) * (ρ (dSlot m c') - 1) =
      (ρ (dSlot m c') - 1) * (ρ (dSlot l c) - 1) := by
    have hc : Commute (ρ (dSlot l c)) (ρ (dSlot m c')) := (dSlot_commute l m c c').map ρ
    exact ((hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)).eq
  have hb0 : (ρ (dSlot m c') - 1) b = 0 := by
    rw [LinearMap.sub_apply, hb c', Module.End.one_apply, sub_self]
  have ha0 : (ρ (dSlot l c) - 1) a = 0 := by
    rw [LinearMap.sub_apply, ha c, Module.End.one_apply, sub_self]
  have e1 : ((ρ (dSlot l c) - 1) * (ρ (dSlot m c') - 1)) a = 0 := by
    rw [hcomm, Module.End.mul_apply, ha0, map_zero]
  have e2 : ((ρ (dSlot l c) - 1) * (ρ (dSlot m c') - 1)) b = 0 := by
    rw [Module.End.mul_apply, hb0, map_zero]
  rw [map_add, e1, e2, add_zero, LinearMap.zero_apply]

end Torus

section Core

variable [Fintype K] [CharP K 2] {Y : Type} [AddCommGroup Y] [Module K Y]
variable {ρ : Representation K (StatedSp 3 K) Y}

local notation "Pt" ρ:max l:max c:max => (ρ (dSlot l c) - 1 : Module.End K Y)

omit [Fintype K] [CharP K 2] in
theorem Pt_apply_eq_zero_iff (ρ : Representation K (StatedSp 3 K) Y) (l : Fin 3) (c : Kˣ) (y : Y) :
    (Pt ρ l c) y = 0 ↔ ρ (dSlot l c) y = y := by
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem two_le_card : 2 ≤ Fintype.card K := by
  have := Fintype.one_lt_card (α := K)
  omega

theorem zeta_sub_one (hsc : SingleCoord ρ) (c : Kˣ) :
    (ρ (zeta c) - 1 : Module.End K Y) = Pt ρ 0 c + Pt ρ 1 c + Pt ρ 2 c := by
  have h01 := torus_mul_eq_zero hsc (show (0 : Fin 3) ≠ 1 by decide) c c
  have h02 := torus_mul_eq_zero hsc (show (0 : Fin 3) ≠ 2 by decide) c c
  have h12 := torus_mul_eq_zero hsc (show (1 : Fin 3) ≠ 2 by decide) c c
  have e : ρ (zeta c) = (Pt ρ 0 c + 1) * (Pt ρ 1 c + 1) * (Pt ρ 2 c + 1) := by
    rw [zeta_eq_mul, map_mul, map_mul, sub_add_cancel, sub_add_cancel, sub_add_cancel]
  rw [e]
  simp only [mul_add, add_mul, one_mul, mul_one, h01, h02, h12, zero_add]
  abel

theorem sum_three_pow {A B C : Module.End K Y} (hAB : A * B = 0) (hAC : A * C = 0)
    (hBA : B * A = 0) (hBC : B * C = 0) (hCA : C * A = 0) (hCB : C * B = 0) :
    ∀ n : ℕ, 1 ≤ n → (A + B + C) ^ n = A ^ n + B ^ n + C ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hA : A ^ n * B = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hAB, mul_zero]
    have hA' : A ^ n * C = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hAC, mul_zero]
    have hB : B ^ n * A = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hBA, mul_zero]
    have hB' : B ^ n * C = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hBC, mul_zero]
    have hC : C ^ n * A = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hCA, mul_zero]
    have hC' : C ^ n * B = 0 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [pow_succ, mul_assoc, hCB, mul_zero]
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, hA, hA', hB, hB', hC, hC', ← pow_succ, zero_add, add_zero]

@[expose] def zeroSp (ρ : Representation K (StatedSp 3 K) Y) : Submodule K Y :=
  fixT ρ 0 ⊓ fixT ρ 1 ⊓ fixT ρ 2

theorem zeta_sub_one_pow (hsc : SingleCoord ρ) (c : Kˣ) :
    (ρ (zeta c) - 1 : Module.End K Y) ^ Fintype.card K = ρ (zeta c) - 1 := by
  have hne : ∀ {l m : Fin 3}, l ≠ m → Pt ρ l c * Pt ρ m c = 0 :=
    fun hlm => torus_mul_eq_zero hsc hlm c c
  rw [zeta_sub_one hsc, sum_three_pow (hne (by decide)) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (hne (by decide)) (hne (by decide)) _ (by have := two_le_card (K := K); omega),
    torus_pow_card, torus_pow_card, torus_pow_card]

@[expose] def stabSub {G : Type*} [Group G] (σ : Representation K G Y) (y : Y) : Subgroup G where
  carrier := {g | σ g y = y}
  mul_mem' {a b} ha hb := by
    show σ (a * b) y = y
    rw [map_mul, Module.End.mul_apply, show σ b y = y from hb, show σ a y = y from ha]
  one_mem' := by show σ 1 y = y; rw [map_one, Module.End.one_apply]
  inv_mem' {a} ha := by
    show σ a⁻¹ y = y
    have h : σ a y = y := ha
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

omit [CharP K 2] in
theorem exists_gen : ∃ c₀ : Kˣ, ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀ :=
  IsCyclic.exists_generator

omit [CharP K 2] in
theorem mem_fixT_iff_gen {c₀ : Kˣ} (hgen : ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀) (l : Fin 3)
    (y : Y) : y ∈ fixT ρ l ↔ ρ (dSlot l c₀) y = y := by
  refine ⟨fun h => h c₀, fun h c => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hgen c)
  rw [← dSlotHom_apply, map_zpow]
  exact Subgroup.zpow_mem _ (show dSlotHom l c₀ ∈ stabSub ρ y from h) k

theorem mem_zeroSp_iff (hsc : SingleCoord ρ) {c₀ : Kˣ}
    (hgen : ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀) (y : Y) :
    y ∈ zeroSp ρ ↔ (ρ (zeta c₀) - 1 : Module.End K Y) y = 0 := by
  have hq := two_le_card (K := K)
  have hne : ∀ {l m : Fin 3}, l ≠ m → Pt ρ l c₀ * Pt ρ m c₀ = 0 :=
    fun hlm => torus_mul_eq_zero hsc hlm c₀ c₀
  rw [zeta_sub_one hsc]
  have key : ∀ l : Fin 3, (Pt ρ 0 c₀ + Pt ρ 1 c₀ + Pt ρ 2 c₀) y = 0 → (Pt ρ l c₀) y = 0 := by
    intro l h
    have hsq : ((Pt ρ l c₀) * (Pt ρ l c₀)) y = 0 := by
      have h1 : (Pt ρ l c₀ * (Pt ρ 0 c₀ + Pt ρ 1 c₀ + Pt ρ 2 c₀)) y = 0 := by
        rw [Module.End.mul_apply, h, map_zero]
      fin_cases l <;> simpa [mul_add, hne (show (0 : Fin 3) ≠ 1 by decide),
        hne (show (0 : Fin 3) ≠ 2 by decide), hne (show (1 : Fin 3) ≠ 0 by decide),
        hne (show (1 : Fin 3) ≠ 2 by decide), hne (show (2 : Fin 3) ≠ 0 by decide),
        hne (show (2 : Fin 3) ≠ 1 by decide)] using h1
    have hpow := torus_pow_card ρ l c₀
    have e : Fintype.card K = (Fintype.card K - 2) + 2 := by omega
    rw [← hpow, e, pow_add, sq, Module.End.mul_apply, hsq, map_zero]
  constructor
  · intro hy
    have h0 : (Pt ρ 0 c₀) y = 0 :=
      (Pt_apply_eq_zero_iff ρ 0 c₀ y).mpr (hy.1.1 c₀)
    have h1 : (Pt ρ 1 c₀) y = 0 :=
      (Pt_apply_eq_zero_iff ρ 1 c₀ y).mpr (hy.1.2 c₀)
    have h2 : (Pt ρ 2 c₀) y = 0 :=
      (Pt_apply_eq_zero_iff ρ 2 c₀ y).mpr (hy.2 c₀)
    rw [LinearMap.add_apply, LinearMap.add_apply, h0, h1, h2, add_zero, add_zero]
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (mem_fixT_iff_gen hgen 0 y).mpr ((Pt_apply_eq_zero_iff ρ 0 c₀ y).mp (key 0 h))
    · exact (mem_fixT_iff_gen hgen 1 y).mpr ((Pt_apply_eq_zero_iff ρ 1 c₀ y).mp (key 1 h))
    · exact (mem_fixT_iff_gen hgen 2 y).mpr ((Pt_apply_eq_zero_iff ρ 2 c₀ y).mp (key 2 h))

@[expose] noncomputable def proj0 (ρ : Representation K (StatedSp 3 K) Y) (c₀ : Kˣ) :
    Module.End K Y :=
  1 - (ρ (zeta c₀) - 1) ^ (Fintype.card K - 1)

theorem proj0_mem (hsc : SingleCoord ρ) {c₀ : Kˣ} (hgen : ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀)
    (y : Y) : proj0 ρ c₀ y ∈ zeroSp ρ := by
  have hq := two_le_card (K := K)
  rw [mem_zeroSp_iff hsc hgen, proj0, ← Module.End.mul_apply, mul_sub, mul_one, ← pow_succ',
    Nat.sub_add_cancel (by omega), zeta_sub_one_pow hsc, sub_self, LinearMap.zero_apply]

theorem proj0_commute_levi (c₀ : Kˣ) (A : GL (Fin 3) K) : Commute (ρ (levi A)) (proj0 ρ c₀) := by
  have h : Commute (ρ (levi A)) (ρ (zeta c₀)) := ((zeta_commute c₀ A).map ρ).symm
  exact (Commute.one_right _).sub_right ((h.sub_right (Commute.one_right _)).pow_right _)

theorem proj0_range (hsc : SingleCoord ρ) (c₀ : Kˣ) (l : Fin 3) (z : Y) :
    proj0 ρ c₀ ((Pt ρ l c₀) z) = 0 := by
  have hq := two_le_card (K := K)
  have hne : ∀ {l m : Fin 3}, l ≠ m → Pt ρ l c₀ * Pt ρ m c₀ = 0 :=
    fun hlm => torus_mul_eq_zero hsc hlm c₀ c₀
  have hQ : (ρ (zeta c₀) - 1 : Module.End K Y) * Pt ρ l c₀ = Pt ρ l c₀ * Pt ρ l c₀ := by
    rw [zeta_sub_one hsc]
    fin_cases l <;> simp [add_mul, hne (show (0 : Fin 3) ≠ 1 by decide),
      hne (show (0 : Fin 3) ≠ 2 by decide), hne (show (1 : Fin 3) ≠ 0 by decide),
      hne (show (1 : Fin 3) ≠ 2 by decide), hne (show (2 : Fin 3) ≠ 0 by decide),
      hne (show (2 : Fin 3) ≠ 1 by decide)]
  have hpow : ∀ n : ℕ, (ρ (zeta c₀) - 1 : Module.End K Y) ^ n * Pt ρ l c₀ =
      Pt ρ l c₀ ^ n * Pt ρ l c₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : (ρ (zeta c₀) - 1 : Module.End K Y) * Pt ρ l c₀ ^ n =
          Pt ρ l c₀ ^ n * (ρ (zeta c₀) - 1) := by
        have h1 : Commute (ρ (zeta c₀) - 1 : Module.End K Y) (Pt ρ l c₀) := by
          have : Commute (ρ (zeta c₀)) (ρ (dSlot l c₀)) := by
            have e1 : zeta c₀ = levi (diagGL fun _ => c₀) := zeta_eq_levi_diagGL c₀
            rw [e1, dSlot_eq_levi]
            exact (levi_diagGL_commute _ _).map ρ
          exact (this.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
        exact (h1.pow_right n).eq
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hc, mul_assoc, hQ, ← mul_assoc, ← pow_succ]
  have e := hpow (Fintype.card K - 1)
  rw [← pow_succ, Nat.sub_add_cancel (by omega), torus_pow_card] at e
  rw [proj0, LinearMap.sub_apply, Module.End.one_apply, ← Module.End.mul_apply, e, sub_self]

theorem proj0_of_mem_M (hsc : SingleCoord ρ) (c₀ : Kˣ) {m : Y}
    (hm : m ∈ fixT ρ 1 ⊓ fixT ρ 2) :
    proj0 ρ c₀ m = m - (Pt ρ 0 c₀ ^ (Fintype.card K - 1)) m := by
  have hinv : ∀ v ∈ fixT ρ 1 ⊓ fixT ρ 2, (Pt ρ 0 c₀) v ∈ fixT ρ 1 ⊓ fixT ρ 2 := by
    intro v hv
    refine ⟨fun c => ?_, fun c => ?_⟩
    · rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← Module.End.mul_apply,
        ← map_mul, ← (dSlot_commute 0 1 c₀ c).eq, map_mul, Module.End.mul_apply, hv.1 c]
    · rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, ← Module.End.mul_apply,
        ← map_mul, ← (dSlot_commute 0 2 c₀ c).eq, map_mul, Module.End.mul_apply, hv.2 c]
  have hagree : ∀ v ∈ fixT ρ 1 ⊓ fixT ρ 2,
      (ρ (zeta c₀) - 1 : Module.End K Y) v = (Pt ρ 0 c₀) v := by
    intro v hv
    rw [zeta_sub_one hsc, LinearMap.add_apply, LinearMap.add_apply,
      (Pt_apply_eq_zero_iff ρ 1 c₀ v).mpr (hv.1 c₀), (Pt_apply_eq_zero_iff ρ 2 c₀ v).mpr (hv.2 c₀),
      add_zero, add_zero]
  have hpow : ∀ n : ℕ, ∀ v ∈ fixT ρ 1 ⊓ fixT ρ 2,
      ((ρ (zeta c₀) - 1 : Module.End K Y) ^ n) v = (Pt ρ 0 c₀ ^ n) v := by
    intro n
    induction n with
    | zero => intro v _; simp
    | succ n ih =>
      intro v hv
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hagree v hv,
        ih _ (hinv v hv)]
  rw [proj0, LinearMap.sub_apply, Module.End.one_apply, hpow _ m hm]

omit [Fintype K] [CharP K 2] in
theorem diagGL_conj_transvectionUnit (τ : Fin 3 → Kˣ) {i j : Fin 3} (hij : i ≠ j) (c : K) :
    diagGL τ * TauCeti.transvectionUnit hij c * (diagGL τ)⁻¹ =
      TauCeti.transvectionUnit hij ((τ i : K) * ((τ j)⁻¹ : Kˣ) * c) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL_inv, TauCeti.coe_transvectionUnit,
    TauCeti.coe_transvectionUnit]
  ext a b
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transvection, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [this]
  · by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp [hab]
      ring
    · simp [hab, h]

omit [Fintype K] [CharP K 2] in
theorem rootE_add {i j : Fin 3} (hij : i ≠ j) (a b : K) :
    rootE hij (a + b) = rootE hij a * rootE hij b := by
  rw [rootE, rootE, rootE, TauCeti.transvectionUnit_add, map_mul]

omit [Fintype K] [CharP K 2] in
theorem rootE_neg {i j : Fin 3} (hij : i ≠ j) (a : K) : rootE hij (-a) = (rootE hij a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootE_add, neg_add_cancel, rootE]
  have : TauCeti.transvectionUnit hij (0 : K) = 1 := by
    apply Units.ext
    simp [Matrix.transvection]
  rw [this, map_one]

omit [Fintype K] [CharP K 2] in
theorem levi_diagGL_conj_rootE (τ : Fin 3 → Kˣ) {i j : Fin 3} (hij : i ≠ j) (c : K) :
    levi (diagGL τ) * rootE hij c * (levi (diagGL τ))⁻¹ =
      rootE hij ((τ i : K) * ((τ j)⁻¹ : Kˣ) * c) := by
  rw [rootE, rootE, ← map_inv, ← map_mul, ← map_mul, diagGL_conj_transvectionUnit]

omit [Fintype K] [CharP K 2] in
theorem levi_diagGL_eq_mul (τ : Fin 3 → Kˣ) :
    levi (diagGL τ) = dSlot 0 (τ 0) * dSlot 1 (τ 1) * dSlot 2 (τ 2) := by
  rw [dSlot_eq_levi, dSlot_eq_levi, dSlot_eq_levi, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL, coe_diagGL, coe_diagGL,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  fin_cases x <;> simp [Pi.mulSingle_apply]

theorem torus_fix_of_mem_zeroSp {y : Y} (hy : y ∈ zeroSp ρ) (τ : Fin 3 → Kˣ) :
    ρ (levi (diagGL τ)) y = y := by
  rw [levi_diagGL_eq_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    hy.2 (τ 2), hy.1.2 (τ 1), hy.1.1 (τ 0)]

theorem levi_mem_zeroSp (hsc : SingleCoord ρ) {c₀ : Kˣ}
    (hgen : ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀) (A : GL (Fin 3) K) {y : Y}
    (hy : y ∈ zeroSp ρ) : ρ (levi A) y ∈ zeroSp ρ := by
  rw [mem_zeroSp_iff hsc hgen] at hy ⊢
  have h : Commute (ρ (levi A)) (ρ (zeta c₀)) := ((zeta_commute c₀ A).map ρ).symm
  have h1 : Commute (ρ (levi A)) (ρ (zeta c₀) - 1) := h.sub_right (Commute.one_right _)
  rw [← Module.End.mul_apply, ← h1.eq, Module.End.mul_apply, hy, map_zero]

theorem rootE_fix_of_mem_zeroSp (hK : 3 ≤ Fintype.card K) (hsc : SingleCoord ρ) {c₀ : Kˣ}
    (hgen : ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀) {i j : Fin 3} (hij : i ≠ j) (c : K) {y : Y}
    (hy : y ∈ zeroSp ρ) : ρ (rootE hij c) y = y := by
  obtain ⟨z, hz⟩ := exists_unit_sq_ne_one hK
  have hz1 : (z : K) - 1 ≠ 0 := by
    intro h
    apply hz
    rw [sub_eq_zero.mp h, one_pow]
  set τ : Fin 3 → Kˣ := Pi.mulSingle i z with hτ
  set t := levi (diagGL τ)
  set r := rootE hij (c / ((z : K) - 1))
  have key : rootE hij c = t * r * t⁻¹ * r⁻¹ := by
    rw [levi_diagGL_conj_rootE, ← rootE_neg, ← rootE_add]
    congr 1
    have hτi : (τ i : K) = z := by simp [hτ]
    have hτj : ((τ j)⁻¹ : Kˣ) = 1 := by simp [hτ, Pi.mulSingle_apply, hij.symm]
    rw [hτi, hτj, Units.val_one, mul_one]
    field_simp
    ring
  have hr : ρ r⁻¹ y ∈ zeroSp ρ := by
    rw [show r⁻¹ = rootE hij (-(c / ((z : K) - 1))) from (rootE_neg hij _).symm]
    exact levi_mem_zeroSp hsc hgen _ hy
  have ht : ρ t⁻¹ (ρ r⁻¹ y) = ρ r⁻¹ y := by
    have : t⁻¹ = levi (diagGL τ⁻¹) := by
      rw [← map_inv]
      congr 1
    rw [this]
    exact torus_fix_of_mem_zeroSp hr _
  calc ρ (rootE hij c) y = ρ t (ρ r (ρ t⁻¹ (ρ r⁻¹ y))) := by
        rw [key, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
          Module.End.mul_apply]
    _ = ρ t (ρ r (ρ r⁻¹ y)) := by rw [ht]
    _ = ρ t y := by rw [← Module.End.mul_apply (ρ r), ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    _ = y := torus_fix_of_mem_zeroSp hy τ

omit [Fintype K] [CharP K 2] in
theorem eq_zero_of_fixed (hirr : ρ.IsIrreducible) (hnt : ∃ g y, ρ g y ≠ y) {y : Y}
    (hfix : ∀ g, ρ g y = y) : y = 0 := by
  obtain ⟨-, hU⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp hirr
  rcases hU (Submodule.span K {y}) (fun g u hu => by
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, hfix g]
    exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self y)) with h | h
  · exact (Submodule.span_singleton_eq_bot.mp h)
  · exfalso
    obtain ⟨g, v, hv⟩ := hnt
    have hvmem : v ∈ Submodule.span K {y} := h ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvmem
    exact hv (by rw [map_smul, hfix g])

theorem slot0_fixed_eq_zero (hK : 3 ≤ Fintype.card K) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g y, ρ g y ≠ y) (hsc : SingleCoord ρ) {y : Y} (hyM : y ∈ fixT ρ 1 ⊓ fixT ρ 2)
    (hfix : ∀ g : SL(2, K), ρ (slotSL 0 g) y = y) : y = 0 := by
  obtain ⟨c₀, hgen⟩ := exists_gen (K := K)
  have hy0 : y ∈ zeroSp ρ := ⟨⟨fun c => hfix (dElt c), hyM.1⟩, hyM.2⟩
  refine eq_zero_of_fixed hirr hnt fun g => ?_
  have htop : stabSub ρ y = ⊤ := by
    rw [eq_top_iff, ← closure_slot_rootE_eq_top, Subgroup.closure_le]
    rintro x (⟨h, rfl⟩ | ⟨i, j, hij, c, rfl⟩)
    · exact hfix h
    · exact rootE_fix_of_mem_zeroSp hK hsc hgen hij c hy0
  exact (htop ▸ Subgroup.mem_top g : g ∈ stabSub ρ y)

omit [Fintype K] [CharP K 2] in
theorem slotSL0_commute_dSlot {l : Fin 3} (hl : l ≠ 0) (g : SL(2, K)) (c : Kˣ) :
    Commute (ρ (slotSL 0 g)) (ρ (dSlot l c)) :=
  ((slotSL_commute hl.symm g (dElt c)).map ρ)

omit [Fintype K] [CharP K 2] in
theorem slotSL0_mem_M (g : SL(2, K)) {m : Y} (hm : m ∈ fixT ρ 1 ⊓ fixT ρ 2) :
    ρ (slotSL 0 g) m ∈ fixT ρ 1 ⊓ fixT ρ 2 := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [← Module.End.mul_apply, ← (slotSL0_commute_dSlot (show (1 : Fin 3) ≠ 0 by decide) g c).eq,
      Module.End.mul_apply, hm.1 c]
  · rw [← Module.End.mul_apply, ← (slotSL0_commute_dSlot (show (2 : Fin 3) ≠ 0 by decide) g c).eq,
      Module.End.mul_apply, hm.2 c]

omit [Fintype K] [CharP K 2] in
@[expose] def Msub (ρ : Representation K (StatedSp 3 K) Y) :
    Subrepresentation (ρ.comp (slotSL 0)) where
  toSubmodule := fixT ρ 1 ⊓ fixT ρ 2
  apply_mem_toSubmodule g _ hm := slotSL0_mem_M (ρ := ρ) g hm

omit [Fintype K] [CharP K 2] in
@[expose] noncomputable def compl12 (ρ : Representation K (StatedSp 3 K) Y) (c₀ : Kˣ) :
    Submodule K Y :=
  LinearMap.range (Pt ρ 1 c₀) ⊔ LinearMap.range (Pt ρ 2 c₀)

theorem compl12_fixT0 (hsc : SingleCoord ρ) (c₀ : Kˣ) {n : Y} (hn : n ∈ compl12 ρ c₀) :
    n ∈ fixT ρ 0 := by
  intro c
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hn
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp ha
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hb
  have h1 := torus_mul_eq_zero hsc (show (0 : Fin 3) ≠ 1 by decide) c c₀
  have h2 := torus_mul_eq_zero hsc (show (0 : Fin 3) ≠ 2 by decide) c c₀
  have e1 : (Pt ρ 0 c) ((Pt ρ 1 c₀) u) = 0 := by
    rw [← Module.End.mul_apply, h1, LinearMap.zero_apply]
  have e2 : (Pt ρ 0 c) ((Pt ρ 2 c₀) v) = 0 := by
    rw [← Module.End.mul_apply, h2, LinearMap.zero_apply]
  have e3 : (Pt ρ 0 c) ((Pt ρ 1 c₀) u + (Pt ρ 2 c₀) v) = 0 := by
    rw [map_add, e1, e2, add_zero]
  exact (Pt_apply_eq_zero_iff ρ 0 c _).mp e3

omit [Fintype K] [CharP K 2] in
theorem slotSL0_Pt_apply {l : Fin 3} (hl : l ≠ 0) (g : SL(2, K)) (c : Kˣ) (u : Y) :
    ρ (slotSL 0 g) ((Pt ρ l c) u) = (Pt ρ l c) (ρ (slotSL 0 g) u) := by
  have h : Commute (ρ (slotSL 0 g)) (Pt ρ l c) :=
    (slotSL0_commute_dSlot hl g c).sub_right (Commute.one_right _)
  rw [← Module.End.mul_apply, h.eq, Module.End.mul_apply]

omit [Fintype K] [CharP K 2] in
theorem slotSL0_mem_compl12 (c₀ : Kˣ) (g : SL(2, K)) {n : Y} (hn : n ∈ compl12 ρ c₀) :
    ρ (slotSL 0 g) n ∈ compl12 ρ c₀ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hn
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp ha
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hb
  rw [map_add, slotSL0_Pt_apply (by decide) g c₀ u, slotSL0_Pt_apply (by decide) g c₀ v]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

theorem slotSL0_fix_compl12 (hK : 3 ≤ Fintype.card K) (hsc : SingleCoord ρ) (c₀ : Kˣ)
    (g : SL(2, K)) {n : Y} (hn : n ∈ compl12 ρ c₀) : ρ (slotSL 0 g) n = n :=
  sl2_fix_of_dElt_fix hK (ρ.comp (slotSL 0)) (compl12 ρ c₀)
    (fun g' _ hw => slotSL0_mem_compl12 c₀ g' hw)
    (fun c w hw => compl12_fixT0 hsc c₀ hw c) g n hn

theorem exists_M_add_compl12 (hsc : SingleCoord ρ) {c₀ : Kˣ}
    (hgen : ∀ c : Kˣ, c ∈ Subgroup.zpowers c₀) (y : Y) :
    ∃ m ∈ fixT ρ 1 ⊓ fixT ρ 2, ∃ n ∈ compl12 ρ c₀, y = m + n := by
  have hq := two_le_card (K := K)
  set q := Fintype.card K
  set E1 := Pt ρ 1 c₀ ^ (q - 1)
  set E2 := Pt ρ 2 c₀ ^ (q - 1)
  obtain ⟨-, hP1E1, -⟩ := pow_pred_idem hq (torus_pow_card ρ 1 c₀)
  obtain ⟨-, hP2E2, -⟩ := pow_pred_idem hq (torus_pow_card ρ 2 c₀)
  have h12 := torus_mul_eq_zero hsc (show (1 : Fin 3) ≠ 2 by decide) c₀ c₀
  have h21 := torus_mul_eq_zero hsc (show (2 : Fin 3) ≠ 1 by decide) c₀ c₀
  have e : q - 1 = (q - 2) + 1 := by omega
  have hP1E2 : Pt ρ 1 c₀ * E2 = 0 := by
    rw [show E2 = Pt ρ 2 c₀ ^ (q - 1) from rfl, e, pow_succ', ← mul_assoc, h12, zero_mul]
  have hP2E1 : Pt ρ 2 c₀ * E1 = 0 := by
    rw [show E1 = Pt ρ 1 c₀ ^ (q - 1) from rfl, e, pow_succ', ← mul_assoc, h21, zero_mul]
  refine ⟨y - E1 y - E2 y, Submodule.mem_inf.mpr ⟨?_, ?_⟩, E1 y + E2 y, ?_, by abel⟩
  · rw [mem_fixT_iff_gen hgen, ← Pt_apply_eq_zero_iff, map_sub, map_sub, ← Module.End.mul_apply,
      hP1E1, ← Module.End.mul_apply, hP1E2, LinearMap.zero_apply, sub_self, sub_zero]
  · rw [mem_fixT_iff_gen hgen, ← Pt_apply_eq_zero_iff, map_sub, map_sub, ← Module.End.mul_apply,
      hP2E1, ← Module.End.mul_apply, hP2E2, LinearMap.zero_apply, sub_zero, sub_self]
  · refine Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨(Pt ρ 1 c₀ ^ (q - 2)) y, ?_⟩)
      (LinearMap.mem_range.mpr ⟨(Pt ρ 2 c₀ ^ (q - 2)) y, ?_⟩)
    · rw [← Module.End.mul_apply, ← pow_succ', ← e]
    · rw [← Module.End.mul_apply, ← pow_succ', ← e]

omit [Fintype K] [CharP K 2] in
theorem invariant_functional_eq_zero (hirr : ρ.IsIrreducible) (hnt : ∃ g y, ρ g y ≠ y)
    (Φ : Y →ₗ[K] K) (hΦ : ∀ g y, Φ (ρ g y) = Φ y) : Φ = 0 := by
  obtain ⟨-, hU⟩ := (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρ).mp hirr
  rcases hU (LinearMap.ker Φ) (fun g u hu => by
    rw [LinearMap.mem_ker, hΦ, LinearMap.mem_ker.mp hu]) with h | h
  · exfalso
    obtain ⟨g, v, hv⟩ := hnt
    apply hv
    have : ρ g v - v ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker, map_sub, hΦ, sub_self]
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · exact LinearMap.ker_eq_top.mp h

theorem slot0_functional_eq_zero (hK : 3 ≤ Fintype.card K) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g y, ρ g y ≠ y) (hsc : SingleCoord ρ)
    (φ : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y) →ₗ[K] K)
    (hφ : ∀ (g : SL(2, K)) (m : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y)),
      φ ⟨ρ (slotSL 0 g) m, slotSL0_mem_M (ρ := ρ) g m.2⟩ = φ m) : φ = 0 := by
  obtain ⟨c₀, hgen⟩ := exists_gen (K := K)
  have hq := two_le_card (K := K)
  set q := Fintype.card K
  have hsub : ∀ y, proj0 ρ c₀ y ∈ fixT ρ 1 ⊓ fixT ρ 2 := fun y =>
    ⟨(proj0_mem hsc hgen y).1.2, (proj0_mem hsc hgen y).2⟩
  have hφP : ∀ m : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y), ∀ v,
      (v : Y) = (Pt ρ 0 c₀ ^ (q - 1)) m → v ∈ fixT ρ 1 ⊓ fixT ρ 2 → ∀ hv,
      φ ⟨v, hv⟩ = 0 := by
    intro m v hvm _ hv
    have hpow : ∀ k : ℕ, (Pt ρ 0 c₀ ^ k) (m : Y) ∈ fixT ρ 1 ⊓ fixT ρ 2 := by
      intro k
      induction k with
      | zero => simpa using m.2
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
        exact Submodule.sub_mem _ (by
          rw [show ρ (dSlot 0 c₀) = ρ (slotSL 0 (dElt c₀)) from rfl]
          exact slotSL0_mem_M _ ih) ih
    set w : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y) := ⟨(Pt ρ 0 c₀ ^ (q - 2)) m, hpow _⟩
    have e : q - 1 = (q - 2) + 1 := by omega
    have hv' : (⟨v, hv⟩ : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y)) =
        ⟨ρ (slotSL 0 (dElt c₀)) w, slotSL0_mem_M _ w.2⟩ - w := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, w]
      rw [hvm, e, pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      rfl
    rw [hv', map_sub, hφ, sub_self]
  have hφproj : ∀ m : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y),
      φ ⟨proj0 ρ c₀ m, hsub m⟩ = φ m := by
    intro m
    have hd : proj0 ρ c₀ m = (m : Y) - (Pt ρ 0 c₀ ^ (q - 1)) m := proj0_of_mem_M hsc c₀ m.2
    have hmem : (Pt ρ 0 c₀ ^ (q - 1)) (m : Y) ∈ fixT ρ 1 ⊓ fixT ρ 2 := by
      have : (Pt ρ 0 c₀ ^ (q - 1)) (m : Y) = (m : Y) - proj0 ρ c₀ m := by rw [hd]; abel
      rw [this]
      exact Submodule.sub_mem _ m.2 (hsub m)
    have hsplit : (⟨proj0 ρ c₀ m, hsub m⟩ : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y)) =
        m - ⟨_, hmem⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sub]
      exact hd
    rw [hsplit, map_sub, hφP m _ rfl hmem hmem, sub_zero]
  set Φ : Y →ₗ[K] K := φ ∘ₗ (LinearMap.codRestrict _ (proj0 ρ c₀) hsub) with hΦdef
  have hΦapp : ∀ y, Φ y = φ ⟨proj0 ρ c₀ y, hsub y⟩ := fun y => rfl
  have hinv : ∀ g y, Φ (ρ g y) = Φ y := by
    intro g y
    have htop : {x | ∀ y, Φ (ρ x y) = Φ y} = (Set.univ : Set (StatedSp 3 K)) := by
      let S : Subgroup (StatedSp 3 K) :=
        { carrier := {x | ∀ y, Φ (ρ x y) = Φ y}
          mul_mem' := fun {a b} ha hb y => by rw [map_mul, Module.End.mul_apply, ha, hb]
          one_mem' := fun y => by rw [map_one, Module.End.one_apply]
          inv_mem' := fun {a} ha y => by
            rw [← ha (ρ a⁻¹ y), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
              Module.End.one_apply] }
      have hS : S = ⊤ := by
        rw [eq_top_iff, ← closure_slot_rootE_eq_top, Subgroup.closure_le]
        rintro x (⟨h, rfl⟩ | ⟨i, j, hij, c, rfl⟩)
        · intro y
          obtain ⟨m, hm, n, hn, rfl⟩ := exists_M_add_compl12 hsc hgen y
          have hn0 : proj0 ρ c₀ n = 0 := by
            obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hn
            obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp ha
            obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hb
            rw [map_add, proj0_range hsc c₀ 1 u, proj0_range hsc c₀ 2 v, add_zero]
          rw [map_add, slotSL0_fix_compl12 (by omega) hsc c₀ h hn, hΦapp, hΦapp]
          have e1 : (⟨proj0 ρ c₀ (ρ (slotSL 0 h) m + n), hsub _⟩ :
              (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y)) =
              ⟨proj0 ρ c₀ (ρ (slotSL 0 h) m), hsub _⟩ := by
            apply Subtype.ext
            simp only
            rw [map_add, hn0, add_zero]
          have e2 : (⟨proj0 ρ c₀ (m + n), hsub _⟩ : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y)) =
              ⟨proj0 ρ c₀ m, hsub _⟩ := by
            apply Subtype.ext
            simp only
            rw [map_add, hn0, add_zero]
          rw [e1, e2]
          have h1 := hφproj ⟨ρ (slotSL 0 h) m, slotSL0_mem_M h hm⟩
          have h2 := hφproj ⟨m, hm⟩
          have h3 := hφ h ⟨m, hm⟩
          simp only at h1 h2 h3
          rw [h1, h2, h3]
        · intro y
          rw [hΦapp, hΦapp]
          congr 1
          apply Subtype.ext
          simp only
          have hcomm : proj0 ρ c₀ * ρ (rootE hij c) = ρ (rootE hij c) * proj0 ρ c₀ :=
            (proj0_commute_levi c₀ (TauCeti.transvectionUnit hij c)).eq.symm
          rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply]
          exact rootE_fix_of_mem_zeroSp (by omega) hsc hgen hij c (proj0_mem hsc hgen y)
      exact Set.eq_univ_of_forall fun x => (hS ▸ Subgroup.mem_top x : x ∈ S)
    have : g ∈ {x | ∀ y, Φ (ρ x y) = Φ y} := htop ▸ Set.mem_univ g
    exact this y
  have hΦ0 := invariant_functional_eq_zero hirr hnt Φ hinv
  ext m
  rw [← hφproj m, LinearMap.zero_apply, ← hΦapp, hΦ0, LinearMap.zero_apply]

open CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.RankThreeUC.S15

theorem quotient_Msub_trivial (hK : 3 ≤ Fintype.card K) (hsc : SingleCoord ρ) (g : SL(2, K)) :
    (Msub ρ).quotient g = 1 := by
  obtain ⟨c₀, hgen⟩ := exists_gen (K := K)
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm, n, hn, rfl⟩ := exists_M_add_compl12 hsc hgen y
  change Submodule.Quotient.mk (ρ (slotSL 0 g) (m + n)) = Submodule.Quotient.mk (m + n)
  rw [Submodule.Quotient.eq, map_add, slotSL0_fix_compl12 hK hsc c₀ g hn,
    show ρ (slotSL 0 g) m + n - (m + n) = ρ (slotSL 0 g) m - m by abel]
  exact Submodule.sub_mem _ (slotSL0_mem_M g hm) hm

omit [Fintype K] [CharP K 2] in
theorem repMultiplicity_trivial_of_trivial {G V : Type} [Group G] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (σ : Representation K G V) (h : ∀ g, σ g = 1) :
    repMultiplicity σ (Representation.trivial K G K) = Module.finrank K V := by
  have key := rep_induction (k := K) (G := G)
    (fun {V} _ _ _ σ => (∀ g, σ g = 1) →
      repMultiplicity σ (Representation.trivial K G K) = Module.finrank K V)
    (fun {V} _ _ _ σ hsub _ => by
      have : Subsingleton σ.asModule := inferInstanceAs (Subsingleton V)
      unfold repMultiplicity
      rw [compositionMultiplicity_of_subsingleton, Module.finrank_zero_of_subsingleton])
    (fun {V} _ _ _ σ hσ ht => by
      obtain ⟨e⟩ := equiv_trivial_of_trivial_isIrreducible σ hσ ht
      rw [repMultiplicity_of_isIrreducible hσ, if_pos ⟨e⟩, e.toLinearEquiv.finrank_eq,
        Module.finrank_self])
    (fun {V} _ _ _ σ W hW1 hW2 ht => by
      rw [repMultiplicity_sub_quot σ W, hW1 (toRepresentation_trivial W ht),
        hW2 (quotient_trivial W ht), add_comm, Submodule.finrank_quotient_add_finrank])
  exact key _ σ rfl h

theorem rec_main (hK : 4 ≤ Fintype.card K) [FiniteDimensional K Y] (hirr : ρ.IsIrreducible)
    (hnt : ∃ g y, ρ g y ≠ y) (hsc : SingleCoord ρ)
    (hone : nontrivCount (ρ.comp (slotSL 0)) = 1) :
    (Msub ρ).toRepresentation.IsIrreducible ∧
      repMultiplicity (ρ.comp (slotSL 0)) (Representation.trivial K SL(2, K) K) +
        Module.finrank K (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y) = Module.finrank K Y := by
  have hK3 : 3 ≤ Fintype.card K := by omega
  have hperf : commutator SL(2, K) = ⊤ :=
    (CFSG.ClassicalInvolution.sl2_isPerfect (by rwa [Nat.card_eq_fintype_card])).commutator_eq_top
  obtain ⟨c₀, hgen⟩ := exists_gen (K := K)
  have hMnt : Nontrivial (Msub ρ).toSubmodule := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    have h0 : nontrivCount (ρ.comp (slotSL 0)) = 0 := by
      refine nontrivCount_eq_zero_of_trivial _ fun g => LinearMap.ext fun y => ?_
      obtain ⟨m, hm, n, hn, rfl⟩ := exists_M_add_compl12 hsc hgen y
      have hm0 : m = 0 := congrArg Subtype.val
        (Subsingleton.elim (⟨m, hm⟩ : (Msub ρ).toSubmodule) 0)
      subst hm0
      rw [zero_add, Module.End.one_apply]
      exact slotSL0_fix_compl12 hK3 hsc c₀ g hn
    omega
  obtain ⟨W, hW⟩ := exists_isCoatom_subrep (Msub ρ).toRepresentation
  have hQirr := quotient_isIrreducible_of_isCoatom _ W hW
  have hWne : W.toSubmodule ≠ ⊤ := fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
  have hQnt : ¬ Nonempty (W.quotient.Equiv (Representation.trivial K SL(2, K) K)) := by
    rintro ⟨e⟩
    let φ : (fixT ρ 1 ⊓ fixT ρ 2 : Submodule K Y) →ₗ[K] K := e.toLinearMap ∘ₗ W.toSubmodule.mkQ
    have hφ0 : φ = 0 := slot0_functional_eq_zero hK3 hirr hnt hsc φ fun g m => by
      have h1 := LinearMap.congr_fun (e.isIntertwining' g) (W.toSubmodule.mkQ m)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply] at h1
      exact h1
    obtain ⟨m, -, hm⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hWne)
    have hne : W.toSubmodule.mkQ m ≠ 0 := by
      rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hφm : φ m = 0 := by rw [hφ0]; rfl
    exact hne (e.toLinearEquiv.injective (hφm.trans (map_zero e.toLinearEquiv).symm))
  have hQ1 : nontrivCount W.quotient = 1 := by
    rw [nontrivCount_of_isIrreducible _ hQirr, if_neg hQnt]
  have h1 := nontrivCount_sub_quot (ρ.comp (slotSL 0)) (Msub ρ)
  have h2 := nontrivCount_sub_quot (Msub ρ).toRepresentation W
  have hW0 : nontrivCount W.toRepresentation = 0 := by omega
  have hWt := trivial_of_nontrivCount_eq_zero hperf W.toRepresentation hW0
  have hWbot : W = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    show W.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    refine slot0_fixed_eq_zero hK3 hirr hnt hsc w.2 fun g => ?_
    have h := LinearMap.congr_fun (hWt g) ⟨w, hw⟩
    rw [Module.End.one_apply] at h
    exact congrArg (fun x : W.toSubmodule => ((x : (Msub ρ).toSubmodule) : Y)) h
  have hMirr : (Msub ρ).toRepresentation.IsIrreducible := by
    rw [hWbot] at hW
    exact isSimpleOrder_iff_isCoatom_bot.mpr hW
  refine ⟨hMirr, ?_⟩
  have hMtriv :
      ¬ Nonempty ((Msub ρ).toRepresentation.Equiv (Representation.trivial K SL(2, K) K)) := by
    rintro ⟨e⟩
    obtain ⟨m, hm0⟩ := exists_ne (0 : (Msub ρ).toSubmodule)
    apply hm0
    apply Subtype.ext
    refine slot0_fixed_eq_zero hK3 hirr hnt hsc m.2 fun g => ?_
    have h := LinearMap.congr_fun (e.isIntertwining' g) m
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Representation.trivial_apply] at h
    have h' : (Msub ρ).toRepresentation g m = m := e.toLinearEquiv.injective h
    exact congrArg Subtype.val h'
  rw [repMultiplicity_sub_quot (ρ.comp (slotSL 0)) (Msub ρ),
    repMultiplicity_of_isIrreducible hMirr, if_neg hMtriv, zero_add,
    repMultiplicity_trivial_of_trivial _ (quotient_Msub_trivial hK3 hsc)]
  exact Submodule.finrank_quotient_add_finrank _

end Core

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
