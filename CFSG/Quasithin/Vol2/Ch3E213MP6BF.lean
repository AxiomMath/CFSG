module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BE
public import CFSG.Quasithin.Vol2.Ch3E213MP6BC

public section

namespace CFSG.Quasithin.Ch3E213M.P6B

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt minorAut
  glMat_minorAut minorMap_apply)
open CFSG.Quasithin.SteinbergBS (map_eq_of_map_le)

variable {k : Type} [Field k] [CharP k 2]

theorem mem_of_sq_mem [Finite k] {F₀ : Subfield k} {y : k} (hy : y ^ 2 ∈ F₀) : y ∈ F₀ := by
  have hinj : Function.Injective (fun a : F₀ => a ^ 2) := fun a b hab => by
    have h1 : ((a : k)) ^ 2 ^ 1 = (b : k) ^ 2 ^ 1 := by
      simpa using congrArg Subtype.val hab
    exact Subtype.ext (eq_of_pow_two_pow_eq h1)
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hinj ⟨y ^ 2, hy⟩
  have h1 : (a : k) ^ 2 ^ 1 = y ^ 2 ^ 1 := by
    simpa using congrArg Subtype.val ha
  rw [← eq_of_pow_two_pow_eq h1]
  exact a.2

omit [CharP k 2] in
theorem natAct_mem {F₀ : Subfield k} {x : antiSp k} (hx : x ∈ subfieldSp F₀) {v : Fin 4 → k}
    (hv : ∀ i, v i ∈ F₀) (i : Fin 4) : natAct x v i ∈ F₀ := by
  simp only [natAct, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  exact F₀.add_mem (F₀.add_mem (F₀.add_mem (F₀.mul_mem (hx i 0) (hv 0))
    (F₀.mul_mem (hx i 1) (hv 1))) (F₀.mul_mem (hx i 2) (hv 2))) (F₀.mul_mem (hx i 3) (hv 3))

omit [CharP k 2] in
theorem spBil_mem {F₀ : Subfield k} {v w : Fin 4 → k} (hv : ∀ i, v i ∈ F₀) (hw : ∀ i, w i ∈ F₀) :
    spBil v w ∈ F₀ := by
  rw [spBil_apply]
  exact F₀.add_mem (F₀.add_mem (F₀.add_mem (F₀.mul_mem (hv 0) (hw 3)) (F₀.mul_mem (hv 1) (hw 2)))
    (F₀.mul_mem (hv 2) (hw 1))) (F₀.mul_mem (hv 3) (hw 0))

omit [CharP k 2] in
theorem single_mem (F₀ : Subfield k) (j i : Fin 4) : (Pi.single j 1 : Fin 4 → k) i ∈ F₀ := by
  rw [Pi.single_apply]
  split_ifs
  exacts [F₀.one_mem, F₀.zero_mem]

omit [CharP k 2] in
theorem row_two_ne {c : antiSp k} {κ : k}
    (h : ∀ i, glMat (c : GL (Fin 4) k) 2 i = κ * glMat (c : GL (Fin 4) k) 3 i) : False := by
  have h1 : glMat (c : GL (Fin 4) k) * glMat ((c⁻¹ : antiSp k) : GL (Fin 4) k) = 1 :=
    (c : GL (Fin 4) k).mul_inv
  have e22 := congrFun (congrFun h1 2) 2
  have e32 := congrFun (congrFun h1 3) 2
  rw [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply_eq] at e22
  rw [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply_ne (by decide)] at e32
  rw [h 0, h 1, h 2, h 3] at e22
  have : (1 : k) = 0 := by linear_combination -e22 + κ * e32
  exact one_ne_zero this

theorem exists_isUpper_conj_c2 [Finite k] {F₀ : Subfield k} {c : antiSp k} {β γ : k}
    (hβ : β ≠ 0) (hγ : γ ≠ 0)
    (hz : uElt 0 β γ 0 ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom) :
    ∃ c' : antiSp k, IsUpper c' ∧ (subfieldSp F₀).map (MulAut.conj c').toMonoidHom =
      (subfieldSp F₀).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨x, hx, hxe⟩ := hz
  change c * x * c⁻¹ = uElt 0 β γ 0 at hxe
  have hcx : ∀ v, natAct c (natAct x v) = natAct (uElt 0 β γ 0) (natAct c v) := fun v => by
    rw [← natAct_mul, ← natAct_mul, ← hxe]
    group
  have hq : ∀ v, spBil v (natAct x v) = γ * natAct c v 3 ^ 2 := fun v => by
    rw [← spBil_natAct c, hcx, spBil_natAct_uElt_center]
  obtain ⟨j, hj⟩ := exists_three_ne_zero c
  have hcj : natAct c (Pi.single j 1) 3 = glMat (c : GL (Fin 4) k) 3 j := natAct_single_apply c 3 j
  have hμ : ∀ i, glMat (c : GL (Fin 4) k) 3 i / glMat (c : GL (Fin 4) k) 3 j ∈ F₀ := fun i => by
    apply mem_of_sq_mem
    have hi : γ * glMat (c : GL (Fin 4) k) 3 i ^ 2 ∈ F₀ := by
      rw [← natAct_single_apply c 3 i, ← hq]
      exact spBil_mem (single_mem F₀ i) (natAct_mem hx (single_mem F₀ i))
    have hj' : γ * glMat (c : GL (Fin 4) k) 3 j ^ 2 ∈ F₀ := by
      rw [← hcj, ← hq]
      exact spBil_mem (single_mem F₀ j) (natAct_mem hx (single_mem F₀ j))
    have e : (glMat (c : GL (Fin 4) k) 3 i / glMat (c : GL (Fin 4) k) 3 j) ^ 2 =
        (γ * glMat (c : GL (Fin 4) k) 3 i ^ 2) / (γ * glMat (c : GL (Fin 4) k) 3 j ^ 2) := by
      field_simp
    rw [e]
    exact F₀.div_mem hi hj'
  set vv : Fin 4 → Fin 4 → k := fun i => Pi.single i 1 -
    (glMat (c : GL (Fin 4) k) 3 i / glMat (c : GL (Fin 4) k) 3 j) • Pi.single j 1 with hvv
  have hvc : ∀ i m, natAct c (vv i) m = glMat (c : GL (Fin 4) k) m i -
      glMat (c : GL (Fin 4) k) 3 i / glMat (c : GL (Fin 4) k) 3 j * glMat (c : GL (Fin 4) k) m j :=
    fun i m => by
      simp only [hvv, natAct_sub, natAct_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        natAct_single_apply]
  have hv3 : ∀ i, natAct c (vv i) 3 = 0 := fun i => by
    rw [hvc, div_mul_cancel₀ _ hj, sub_self]
  obtain ⟨i, hi⟩ : ∃ i, natAct c (vv i) 2 ≠ 0 := by
    by_contra hc
    push Not at hc
    refine row_two_ne (c := c)
      (κ := glMat (c : GL (Fin 4) k) 2 j / glMat (c : GL (Fin 4) k) 3 j) fun i => ?_
    have := hc i
    rw [hvc, sub_eq_zero] at this
    rw [this]
    ring
  have hu'3 : natAct c (Pi.single j 1) 3 ≠ 0 := by rw [hcj]; exact hj
  have hvF : ∀ m, vv i m ∈ F₀ := fun m => by
    simp only [hvv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact F₀.sub_mem (single_mem F₀ i m) (F₀.mul_mem (hμ i) (single_mem F₀ j m))
  set w := natAct x (vv i) - vv i with hw
  set w' := natAct x (Pi.single j 1) - Pi.single j 1 with hw'
  have hcw : natAct c w = (β * natAct c (vv i) 2) • Pi.single 0 1 := by
    rw [hw, natAct_sub, hcx, natAct_uElt_center]
    funext m
    fin_cases m <;> simp [hv3 i]
  have hcw' : natAct c w' = (γ * natAct c (Pi.single j 1) 3 + β * natAct c (Pi.single j 1) 2) •
      Pi.single 0 1 + (β * natAct c (Pi.single j 1) 3) • Pi.single 1 1 := by
    rw [hw', natAct_sub, hcx, natAct_uElt_center]
    funext m
    fin_cases m <;> simp
  have hwF : ∀ m, w m ∈ F₀ := fun m => by
    rw [hw, Pi.sub_apply]
    exact F₀.sub_mem (natAct_mem hx hvF m) (hvF m)
  have hwF' : ∀ m, w' m ∈ F₀ := fun m => by
    rw [hw', Pi.sub_apply]
    exact F₀.sub_mem (natAct_mem hx (single_mem F₀ j) m) (single_mem F₀ j m)
  set w₀ : Fin 4 → ↥F₀ := fun m => ⟨w m, hwF m⟩ with hw₀
  set w₀' : Fin 4 → ↥F₀ := fun m => ⟨w' m, hwF' m⟩ with hw₀'
  have hli : LinearIndependent ↥F₀ ![w₀, w₀'] := by
    rw [LinearIndependent.pair_iff]
    intro p q hpq
    have hk : (p : k) • w + (q : k) • w' = 0 := by
      ext m
      have h1 := congrArg Subtype.val (congrFun hpq m)
      simpa [hw₀, hw₀'] using h1
    have hc := congrArg (natAct c) hk
    rw [natAct_add, natAct_smul, natAct_smul, hcw, hcw',
      show natAct c 0 = 0 from Matrix.mulVec_zero _] at hc
    have e0 := congrFun hc 0
    have e1 := congrFun hc 1
    have e1' : (q : k) * (β * natAct c (Pi.single j 1) 3) = 0 := by
      simpa [Pi.single_apply] using e1
    have hq : (q : k) = 0 := (mul_eq_zero.1 e1').resolve_right (mul_ne_zero hβ hu'3)
    have e0' : (p : k) * (β * natAct c (vv i) 2) = 0 := by
      simpa [Pi.single_apply, hq] using e0
    have hp : (p : k) = 0 := (mul_eq_zero.1 e0').resolve_right (mul_ne_zero hβ hi)
    exact ⟨Subtype.ext hp, Subtype.ext hq⟩
  have hww : spBil w₀ w₀' = 0 := by
    apply Subtype.val_injective
    rw [spBil_coe]
    change spBil w w' = 0
    rw [← spBil_natAct c, hcw, hcw', spBil_apply]
    simp
  obtain ⟨z₀, hz0, hz1⟩ := exists_antiSp_flag hli hww
  have hzmem : subAntiSp F₀ z₀ ∈ subfieldSp F₀ := range_subAntiSp F₀ ▸ ⟨z₀, rfl⟩
  have hze : ∀ m : Fin 4, natAct (subAntiSp F₀ z₀) (Pi.single m 1) =
      fun l => ((natAct (k := ↥F₀) z₀ (Pi.single m 1) l : ↥F₀) : k) := fun m => by
    rw [← natAct_subAntiSp, coe_single]
  have hze0 : natAct (subAntiSp F₀ z₀) (Pi.single 0 1) = w := by
    rw [hze, hz0]
  have hze1 : natAct (subAntiSp F₀ z₀) (Pi.single 1 1) = w' := by
    rw [hze, hz1]
  have hcol' : ∀ (l m : Fin 4), glMat ((c * subAntiSp F₀ z₀ : antiSp k) : GL (Fin 4) k) l m =
      natAct c (natAct (subAntiSp F₀ z₀) (Pi.single m 1)) l := fun l m => by
    rw [← natAct_single_apply, natAct_mul]
  refine ⟨c * subAntiSp F₀ z₀, ?_, ?_⟩
  · refine isUpper_of_flag ?_ ?_ ?_ ?_ ?_ <;>
      (rw [hcol']; simp [hze0, hze1, hcw, hcw'])
  · have hcomp : (MulAut.conj (c * subAntiSp F₀ z₀)).toMonoidHom =
        (MulAut.conj c).toMonoidHom.comp (MulAut.conj (subAntiSp F₀ z₀)).toMonoidHom := by
      ext g
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
        Function.comp_apply]
      group
    rw [hcomp, ← Subgroup.map_map, map_conj_eq_of_mem hzmem]

section Minor

variable [Finite k]

theorem map_minorAut_subfieldSp (F₀ : Subfield k) :
    (subfieldSp F₀).map (minorAut k).toMonoidHom = subfieldSp F₀ := by
  refine map_eq_of_map_le ?_ le_rfl
  rintro _ ⟨g, hg, rfl⟩ A B
  change glMat (minorAut k g : GL (Fin 4) k) A B ∈ F₀
  rw [glMat_minorAut, minorMap_apply]
  exact F₀.sub_mem (F₀.mul_mem (hg _ _) (hg _ _)) (F₀.mul_mem (hg _ _) (hg _ _))

theorem map_symm_minorAut_conj_subfieldSp (F₀ : Subfield k) (c₁ : antiSp k) :
    ((subfieldSp F₀).map (MulAut.conj c₁).toMonoidHom).map (minorAut k).symm.toMonoidHom =
      (subfieldSp F₀).map (MulAut.conj ((minorAut k).symm c₁)).toMonoidHom := by
  have hS : (subfieldSp F₀).map (minorAut k).symm.toMonoidHom = subfieldSp F₀ := by
    conv_lhs => rw [← map_minorAut_subfieldSp F₀]
    rw [Subgroup.map_map]
    convert Subgroup.map_id (subfieldSp F₀)
    ext y
    simp
  conv_rhs => rw [← hS]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [map_mul, map_inv]

end Minor

end CFSG.Quasithin.Ch3E213M.P6B
