module

public import CFSG.LocalAnalysis.StandardType.GGResE6DependentDualOrbits
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import CFSG.LocalAnalysis.StandardType.ZS.ReflPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.E6DependentDualSeven.Classification

open CFSG.StandardType
open CFSG.StandardType.E6DependentDualSeven
open Module

abbrev F3 := ZMod 3
abbrev W7 := Fin 7 → F3

@[expose] def sixCoeff (rho : Module.Dual F3 W7) : U :=
  fun i => rho (Pi.single i.castSucc (1 : F3))

@[expose] def lastCoeff (rho : Module.Dual F3 W7) : F3 := rho axis

@[simp] lemma sixCoeff_apply (rho : Module.Dual F3 W7) (i : Fin 6) :
    sixCoeff rho i = rho (Pi.single i.castSucc (1 : F3)) := rfl

@[simp] lemma lastCoeff_apply (rho : Module.Dual F3 W7) : lastCoeff rho = rho axis := rfl

lemma single_last_eq_axis : (Pi.single (6 : Fin 7) (1 : F3) : W7) = axis := by
  rfl

lemma if_eq_single (i : Fin 7) :
    (fun j : Fin 7 => if i = j then (1 : F3) else 0) = Pi.single i 1 := by
  funext j
  by_cases h : i = j
  · simp [Pi.single_apply, h]
  · have h' : j ≠ i := fun hji => h hji.symm
    simp [Pi.single_apply, h, h']

lemma rho_apply_ofUT (rho : Module.Dual F3 W7) (u : U) (t : F3) :
    rho (ofUT u t) = dotU (sixCoeff rho) u + lastCoeff rho * t := by
  conv_lhs =>
    rw [LinearMap.pi_apply_eq_sum_univ rho (ofUT u t)]
    rw [Fin.sum_univ_castSucc
      (f := fun j : Fin 7 =>
        (ofUT u t) j • rho (fun i => if j = i then 1 else 0))]
  simp only [ofUT, Fin.snoc_castSucc, Fin.snoc_last, smul_eq_mul, sixCoeff,
    lastCoeff, dotU, if_eq_single]
  have hlast : rho (Pi.single (Fin.last 6) (1 : F3)) = rho axis := by
    rw [show (Fin.last 6 : Fin 7) = (6 : Fin 7) from six_last.symm,
      single_last_eq_axis]
  rw [hlast]
  simp [mul_comm]

lemma dotU_sub (a x y : U) : dotU a (x - y) = dotU a x - dotU a y := by
  unfold dotU
  simp_rw [Pi.sub_apply, mul_sub]
  exact Finset.sum_sub_distrib
    (f := fun j : Fin 6 => a j * x j) (g := fun j : Fin 6 => a j * y j)

lemma s_ofUT (i : Fin 6) (u : U) (t : F3) :
    s i (ofUT u t) = ofUT (sU i u) t := by
  have h := lwordProd_apply [i] (ofUT u t)
  simpa [lwordProd, applyUWord, sU] using h

lemma dotU_kvec_sU_all :
    ∀ (i : Fin 6) (u : U), dotU kvec (sU i u) = dotU kvec u := by
  decide +kernel

lemma dotU_kvec_sU (i : Fin 6) (u : U) : dotU kvec (sU i u) = dotU kvec u :=
  dotU_kvec_sU_all i u

lemma dotU_smul_left (lam : F3) (a b : U) : dotU (lam • a) b = lam * dotU a b := by
  simp only [dotU, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rho_invariant_of_sixCoeff_kvec_any_last
    (rho : Module.Dual K V7) {lam : K}
    (hb : sixCoeff rho = lam • kvec) :
    ∀ i : Fin 6, ∀ x : V7, rho (s i x) = rho x := by
  intro i x
  rw [show x = ofUT (ucoord x) (tcoord x) from (ofUT_ucoord_tcoord x).symm]
  rw [s_ofUT, rho_apply_ofUT, rho_apply_ofUT]
  have hk : dotU (sixCoeff rho) (sU i (ucoord x)) = dotU (sixCoeff rho) (ucoord x) := by
    rw [hb, dotU_smul_left, dotU_smul_left, dotU_kvec_sU]
  rw [hk]

lemma rho_invariant_of_sixCoeff_kvec (rho : Module.Dual F3 W7) {lam : F3}
    (haxis : rho axis = 1) (hb : sixCoeff rho = lam • kvec) :
    ∀ i : Fin 6, ∀ x : W7, rho (s i x) = rho x :=
  rho_invariant_of_sixCoeff_kvec_any_last rho hb

lemma exists_s_moves_rep :
    ∀ idx : Fin 8, idx ≠ 0 → idx ≠ 4 →
      ∃ i : Fin 6, sU i (reps idx) ≠ reps idx := by
  decide +kernel

lemma applyUWord_zero (w : List (Fin 6)) : applyUWord w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [applyUWord_cons]
      have hs : sU i 0 = 0 := by
        funext j
        simp [sU]
      rw [hs, ih]

lemma lwordProd_axis (w : List (Fin 6)) : lwordProd w axis = axis := by
  have h0 : ucoord axis = 0 := by
    funext i
    fin_cases i <;> decide +kernel
  have h1 : tcoord axis = 1 := by
    decide +kernel
  rw [lwordProd_apply, h0, h1, applyUWord_zero]
  ext i
  fin_cases i <;> decide +kernel

lemma dotU_rowDiff_eq_zero (rho : Module.Dual F3 W7) {w : List (Fin 6)} {y : U}
    (hfix : ∀ x : W7, rho (lwordProd w x) = rho x) :
    dotU (sixCoeff rho) (applyUWord w y - y) = 0 := by
  have h := hfix (ofUT y 0)
  rw [lwordProd_apply] at h
  simp only [ucoord_ofUT, tcoord_ofUT] at h
  change rho (ofUT (applyUWord w y) 0) = rho (ofUT y 0) at h
  rw [rho_apply_ofUT, rho_apply_ofUT] at h
  simp only [mul_zero, add_zero] at h
  rw [dotU_sub, h, sub_self]

lemma constraintOK_eq_true_of_rows (idx : Fin 8) (b : U)
    (h : ∀ r ∈ constraintRows idx, dotU b (rowDiff r) = 0) :
    constraintOK idx b = true := by
  rw [constraintOK, List.all_eq_true]
  intro r hr
  have h0 := h r hr
  simpa [rowDiff, h0]

lemma conj_reflection_eq (g : W7 ≃ₗ[F3] W7) {u : W7} {φ : Module.Dual F3 W7}
    (hφ : φ u = 2) (hφ' : (φ.comp g.symm.toLinearMap) (g u) = 2) :
    g * Module.reflection hφ * g⁻¹ = Module.reflection hφ' := by
  apply LinearEquiv.ext
  intro x
  change g (g.symm x - φ (g.symm x) • u) = x - φ (g.symm x) • g u
  rw [map_sub, map_smul, g.apply_symm_apply]

lemma nonzero_rep_contradiction
    (idx : Fin 8) (h0 : idx ≠ 0) (h4 : idx ≠ 4)
    {lam : F3} {rho' : Module.Dual F3 W7} {v' : W7} {t : F3}
    (H : Subgroup (W7 ≃ₗ[F3] W7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    (hself' : rho' v' = 2)
    (hr' : Module.reflection hself' ∈ H)
    (haxis' : rho' axis = 1)
    (hb : sixCoeff rho' = lam • kvec)
    (hv' : v' = ofUT (reps idx) t) : False := by
  have hinv := rho_invariant_of_sixCoeff_kvec rho' haxis' hb
  obtain ⟨i, hi⟩ := exists_s_moves_rep idx h0 h4
  have hne : s i v' ≠ v' := by
    intro h
    apply hi
    have hc := congrArg ucoord h
    simpa [hv', s_ofUT, ucoord_ofUT] using hc
  have hroot : rho' (s i v') = 2 := by
    rw [hinv i v', hself']
  let rho'' : Module.Dual F3 W7 := rho'.comp (s i).symm.toLinearMap
  have hρ'' : rho'' = rho' := by
    apply LinearMap.ext
    intro x
    have h := hinv i ((s i).symm x)
    simpa [rho''] using h.symm
  have hroot'' : rho'' (s i v') = 2 := by
    rw [hρ'']
    exact hroot
  have hconj : s i * Module.reflection hself' * (s i)⁻¹ =
      Module.reflection hroot'' :=
    conj_reflection_eq (s i) hself' hroot''
  have hrefl : Module.reflection hroot'' = Module.reflection hroot := by
    ext x
    rw [Module.reflection_apply, Module.reflection_apply, hρ'']
  have hmem : Module.reflection hroot ∈ H := by
    rw [← hrefl, ← hconj]
    exact H.mul_mem (H.mul_mem (hs i) hr') (H.inv_mem (hs i))
  have heq := CFSG.StandardType.QTwoLin.reflection_root_eq_of_transvectionFree hTF hself' hroot hr' hmem
  exact hne heq.symm

lemma dotU_rep4_all :
    ∀ c d : F3, dotU (c • k0vec + d • e5vec) (reps (4 : Fin 8)) = c + d := by
  decide +kernel

lemma reps_four_eq_u72 :
    reps (4 : Fin 8) =
      CFSG.StandardType.E6DependentDualSeven.At72.u72 := by
  decide +kernel

lemma root72_ofUT (c d : F3) :
    ofUT (reps (4 : Fin 8)) (2 - c - d) =
      CFSG.StandardType.E6DependentDualSeven.At72.root c d := by
  rw [reps_four_eq_u72]
  rfl

lemma alpha72_apply_ofUT (c d : F3) (u : U) (t : F3) :
    CFSG.StandardType.E6DependentDualSeven.At72.alpha c d (ofUT u t) =
      dotU (c • k0vec + d • e5vec) u + t := by
  have hsix : sixCoeff (CFSG.StandardType.E6DependentDualSeven.At72.alpha c d) =
      c • k0vec + d • e5vec := by
    funext i
    fin_cases i <;>
      simp [sixCoeff, CFSG.StandardType.E6DependentDualSeven.At72.alpha,
        E6DependentDualSeven.coord, k0vec, e5vec] <;> ring
  have hlast : lastCoeff (CFSG.StandardType.E6DependentDualSeven.At72.alpha c d) = 1 := by
    simp [lastCoeff, CFSG.StandardType.E6DependentDualSeven.At72.alpha,
      E6DependentDualSeven.coord, axis, tU]
  rw [rho_apply_ofUT, hsix, hlast]
  simp

theorem ucoord_eq_zero_of_normalized
    (H : Subgroup (W7 ≃ₗ[F3] W7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    {v : W7} {rho : Module.Dual F3 W7}
    (hself : rho v = 2)
    (hr : Module.reflection hself ∈ H)
    (haxis : rho axis = 1) :
    ucoord v = 0 := by
  let w : List (Fin 6) := normWord (ucoord v)
  let g : W7 ≃ₗ[F3] W7 := lwordProd w
  have hg : g ∈ H := lwordProd_mem hs w
  let v' : W7 := g v
  let rho' : Module.Dual F3 W7 := rho.comp g.symm.toLinearMap
  have hself' : rho' v' = 2 := by
    simp [rho', v', hself]
  have hconj : g * Module.reflection hself * g⁻¹ = Module.reflection hself' :=
    conj_reflection_eq g hself hself'
  have hr' : Module.reflection hself' ∈ H := by
    rw [← hconj]
    exact H.mul_mem (H.mul_mem hg hr) (H.inv_mem hg)
  have hgaxis : g axis = axis := lwordProd_axis w
  have hgsaxis : g.symm axis = axis := by
    have := congrArg g.symm hgaxis
    simpa using this.symm
  have haxis' : rho' axis = 1 := by
    simp [rho', hgsaxis, haxis]
  have hnorm := normWord_spec (ucoord v)
  generalize hidx : normIdx (ucoord v) = idx
  have hrep : applyUWord w (ucoord v) = reps idx := by
    simpa [w, hidx] using hnorm.2
  have hv' : v' = ofUT (reps idx) (tcoord v) := by
    simp [v', g, w, lwordProd_apply, hrep]
  have hconstraint : constraintOK idx (sixCoeff rho') = true := by
    apply constraintOK_eq_true_of_rows
    intro r hr
    have hg_r : lwordProd r.word ∈ H := lwordProd_mem hs r.word
    have hfix_r : lwordProd r.word v' = v' := by
      rw [hv', lwordProd_apply]
      simp only [ucoord_ofUT, tcoord_ofUT]
      rw [word_fixes_rep (idx := idx) hr]
    have hform :=
      CFSG.StandardType.QTwoLin.reflection_form_fixed_of_root_stabilizer
        hTF hself' hr' hg_r hfix_r
    exact dotU_rowDiff_eq_zero rho' hform
  have hallowed := allowed_of_constraintOK idx (sixCoeff rho') hconstraint
  fin_cases idx
  ·
    have hv0 : v' = ofUT (0 : U) (tcoord v) := by
      have hz : (![0, 0, 0, 0, 0, 0] : U) = 0 := by decide
      simpa [reps, repsList, hz] using hv'
    have ht : tcoord v = 2 := by
      have h := hself'
      rw [hv0, rho_apply_ofUT, lastCoeff_apply, haxis'] at h
      simpa [dotU] using h
    have hv2 : v' = (2 : F3) • axis := by
      rw [hv0, ht]
      ext i
      fin_cases i <;> decide +kernel
    have hv_axis : v = (2 : F3) • axis := by
      calc
        v = g.symm v' := by simp [v']
        _ = g.symm ((2 : F3) • axis) := by rw [hv2]
        _ = (2 : F3) • g.symm axis := by simp
        _ = (2 : F3) • axis := by rw [hgsaxis]
    rw [hv_axis]
    decide +kernel
  ·
    change ∃ lam : F3, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exfalso
    exact nonzero_rep_contradiction (idx := 1) (by decide) (by decide)
      H hTF hs hself' hr' haxis' hb (by simpa using hv')
  ·
    change ∃ lam : F3, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exfalso
    exact nonzero_rep_contradiction (idx := 2) (by decide) (by decide)
      H hTF hs hself' hr' haxis' hb (by simpa using hv')
  ·
    change ∃ lam : F3, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exfalso
    exact nonzero_rep_contradiction (idx := 3) (by decide) (by decide)
      H hTF hs hself' hr' haxis' hb (by simpa using hv')
  ·
    change ∃ c d : F3, sixCoeff rho' = c • k0vec + d • e5vec at hallowed
    rcases hallowed with ⟨c, d, hb⟩
    have hv4 : v' = ofUT (reps (4 : Fin 8)) (tcoord v) := by
      simpa using hv'
    have ht : tcoord v = 2 - c - d := by
      have h := hself'
      rw [hv4, rho_apply_ofUT, hb, lastCoeff_apply, haxis'] at h
      rw [dotU_rep4_all c d] at h
      linear_combination h
    have hvroot : v' = CFSG.StandardType.E6DependentDualSeven.At72.root c d := by
      rw [hv4, ht]
      exact root72_ofUT c d
    have hrho : rho' = CFSG.StandardType.E6DependentDualSeven.At72.alpha c d := by
      apply LinearMap.ext
      intro x
      rw [show x = ofUT (ucoord x) (tcoord x) from (ofUT_ucoord_tcoord x).symm]
      rw [rho_apply_ofUT, hb, lastCoeff_apply, haxis', alpha72_apply_ofUT]
      simp
    have hrefl : Module.reflection hself' =
        CFSG.StandardType.E6DependentDualSeven.At72.rCD c d := by
      apply LinearEquiv.ext
      intro x
      rw [Module.reflection_apply, CFSG.StandardType.E6DependentDualSeven.At72.rCD,
        Module.reflection_apply, hrho, hvroot]
    have hrCD : CFSG.StandardType.E6DependentDualSeven.At72.rCD c d ∈ H := by
      rw [← hrefl]
      exact hr'
    exfalso
    exact CFSG.StandardType.E6DependentDualSeven.At72.no_transvectionFree_subgroup_at72
      c d H hTF hs hrCD
  ·
    change ∃ lam : F3, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exfalso
    exact nonzero_rep_contradiction (idx := 5) (by decide) (by decide)
      H hTF hs hself' hr' haxis' hb (by simpa using hv')
  ·
    change ∃ lam : F3, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exfalso
    exact nonzero_rep_contradiction (idx := 6) (by decide) (by decide)
      H hTF hs hself' hr' haxis' hb (by simpa using hv')
  ·
    change ∃ lam : F3, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exfalso
    exact nonzero_rep_contradiction (idx := 7) (by decide) (by decide)
      H hTF hs hself' hr' haxis' hb (by simpa using hv')

lemma eq_smul_axis_of_ucoord_eq_zero {v : W7} (hv : ucoord v = 0) :
    v = tcoord v • axis := by
  rw [← ofUT_ucoord_tcoord v, hv]
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [ofUT, axis, tU, tcoord, Pi.smul_apply, smul_eq_mul]
  · fin_cases i <;> rfl

theorem ucoord_eq_zero_of_axis_ne_zero
    (H : Subgroup (W7 ≃ₗ[F3] W7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    {v : W7} {rho : Module.Dual F3 W7}
    (hself : rho v = 2)
    (hr : Module.reflection hself ∈ H)
    (haxis : rho axis ≠ 0) :
    ucoord v = 0 := by
  let c : F3 := rho axis
  have hc : c ≠ 0 := haxis
  let rho' : Module.Dual F3 W7 := c⁻¹ • rho
  let v' : W7 := c • v
  have hself' : rho' v' = 2 := by
    simp only [rho', v', LinearMap.smul_apply, map_smul, smul_eq_mul]
    rw [hself]
    field_simp [hc]
  have haxis' : rho' axis = 1 := by
    simp only [rho', LinearMap.smul_apply, smul_eq_mul]
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hc
  have hrefl : Module.reflection hself' = Module.reflection hself := by
    apply LinearEquiv.ext
    intro x
    rw [Module.reflection_apply, Module.reflection_apply]
    change x - (rho' x) • v' = x - rho x • v
    rw [show rho' x = c⁻¹ * rho x by rfl, show v' = c • v by rfl, smul_smul]
    have hscalar : (c⁻¹ * rho x) * c = rho x := by
      calc
        (c⁻¹ * rho x) * c = c⁻¹ * (rho x * c) := by ring
        _ = c⁻¹ * (c * rho x) := by rw [mul_comm (rho x) c]
        _ = (c⁻¹ * c) * rho x := by ring
        _ = rho x := by rw [inv_mul_cancel₀ hc, one_mul]
    rw [hscalar]
  have hr' : Module.reflection hself' ∈ H := by
    rw [hrefl]
    exact hr
  have hvc : ucoord v' = 0 :=
    ucoord_eq_zero_of_normalized H hTF hs hself' hr' haxis'
  have hvc' : c • ucoord v = 0 := by
    have hucoord : ucoord v' = c • ucoord v := by
      funext i
      rfl
    rw [hucoord] at hvc
    exact hvc
  exact (smul_eq_zero.mp hvc').resolve_left hc

theorem reflection_commutes_simple_of_ucoord_eq_zero
    (H : Subgroup (W7 ≃ₗ[F3] W7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    {v : W7} {rho : Module.Dual F3 W7}
    (hself : rho v = 2)
    (hr : Module.reflection hself ∈ H)
    (hv : ucoord v = 0) :
    ∀ i : Fin 6, Commute (Module.reflection hself) (s i) := by
  intro i
  have hv_axis : v = tcoord v • axis := eq_smul_axis_of_ucoord_eq_zero hv
  have hsv : s i v = v := by
    rw [hv_axis, map_smul, s_fixes_axis]
  have hfix : ∀ x : W7, rho (s i x) = rho x :=
    CFSG.StandardType.QTwoLin.reflection_form_fixed_of_root_stabilizer
      hTF hself hr (hs i) hsv
  have hself' : (rho.comp (s i).symm.toLinearMap) (s i v) = 2 := by
    simpa using hself
  have hconj : s i * Module.reflection hself * (s i)⁻¹ =
      Module.reflection hself' :=
    conj_reflection_eq (s i) hself hself'
  have hfun : rho.comp (s i).symm.toLinearMap = rho := by
    apply LinearMap.ext
    intro x
    have h := hfix ((s i).symm x)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hrefl : Module.reflection hself' = Module.reflection hself := by
    apply LinearEquiv.ext
    intro x
    rw [Module.reflection_apply, Module.reflection_apply, hfun, hsv]
  have hconj' : s i * Module.reflection hself * (s i)⁻¹ = Module.reflection hself := by
    rw [hconj, hrefl]
  have hcomm : s i * Module.reflection hself = Module.reflection hself * s i := by
    calc
      s i * Module.reflection hself =
          (s i * Module.reflection hself * (s i)⁻¹) * s i := by group
      _ = Module.reflection hself * s i := by rw [hconj']
  exact hcomm.symm

theorem reflection_eq_of_ucoord_eq_zero
    (H : Subgroup (W7 ≃ₗ[F3] W7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    {v w : W7} {rho sigma : Module.Dual F3 W7}
    (hv : ucoord v = 0) (hw : ucoord w = 0)
    (hself : rho v = 2) (hself' : sigma w = 2)
    (hr : Module.reflection hself ∈ H)
    (hr' : Module.reflection hself' ∈ H) :
    Module.reflection hself = Module.reflection hself' := by
  have hv_axis : v = tcoord v • axis := eq_smul_axis_of_ucoord_eq_zero hv
  have hw_axis : w = tcoord w • axis := eq_smul_axis_of_ucoord_eq_zero hw
  set tv : F3 := tcoord v
  set tw : F3 := tcoord w
  have htv : tv ≠ 0 := by
    intro h0
    have hzero : rho v = 0 := by
      rw [hv_axis, h0, zero_smul, map_zero]
    rw [hself] at hzero
    exact (by decide : (2 : F3) ≠ 0) hzero
  have hw_span : w ∈ Submodule.span F3 ({v} : Set W7) := by
    rw [Submodule.mem_span_singleton]
    refine ⟨tw * tv⁻¹, ?_⟩
    rw [hw_axis, hv_axis, smul_smul, mul_assoc, inv_mul_cancel₀ htv, mul_one]
  exact CFSG.StandardType.ZS.reflection_eq_of_mem_span (p := 3) (by decide) hTF
    hself hself' hr hr' hw_span

theorem reflection_commute_closure_of_ucoord_eq_zero
    (H : Subgroup (W7 ≃ₗ[F3] W7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    {v : W7} {rho : Module.Dual F3 W7}
    (hself : rho v = 2)
    (hr : Module.reflection hself ∈ H)
    (hv : ucoord v = 0) :
    ∀ g ∈ Subgroup.closure (Set.range s),
      Commute (Module.reflection hself) g := by
  have hcomm : ∀ i : Fin 6, Commute (Module.reflection hself) (s i) :=
    reflection_commutes_simple_of_ucoord_eq_zero H hTF hs hself hr hv
  have hle : Subgroup.closure (Set.range s) ≤
      Subgroup.centralizer ({Module.reflection hself} : Set (W7 ≃ₗ[F3] W7)) := by
    rw [Subgroup.closure_le]
    rintro g ⟨i, rfl⟩
    change s i ∈ Subgroup.centralizer ({Module.reflection hself} : Set (W7 ≃ₗ[F3] W7))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcomm i).eq
  intro g hg
  have hg' := hle hg
  rw [Subgroup.mem_centralizer_iff] at hg'
  exact hg' (Module.reflection hself) (Set.mem_singleton _)

end CFSG.StandardType.E6DependentDualSeven.Classification

namespace CFSG.StandardType.E6DependentDualSeven.FullAxisZero

open CFSG.StandardType.E6DependentDualSeven
open CFSG.StandardType.E6DependentDualSeven.Classification
open Module

lemma alpha0_apply_ofUT (c d : K) (u : U) (t : K) :
    At72AxisZero.alpha0 c d (ofUT u t) = dotU (c • k0vec + d • e5vec) u := by
  have hsix : sixCoeff (At72AxisZero.alpha0 c d) = c • k0vec + d • e5vec := by
    funext i
    fin_cases i <;>
      simp [sixCoeff, At72AxisZero.alpha0, E6DependentDualSeven.coord, k0vec,
        e5vec] <;> ring
  have hlast : lastCoeff (At72AxisZero.alpha0 c d) = 0 := by
    simp [lastCoeff, At72AxisZero.alpha0, E6DependentDualSeven.coord, axis, tU]
  rw [rho_apply_ofUT, hsix, hlast]
  simp

lemma nonzero_rep_contradiction_zero_axis
    (idx : Fin 8) (h0 : idx ≠ 0) (h4 : idx ≠ 4)
    {lam : K} {rho' : Module.Dual K V7} {v' : V7} {t : K}
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    (hself' : rho' v' = 2)
    (hr' : Module.reflection hself' ∈ H)
    (hb : sixCoeff rho' = lam • kvec)
    (hv' : v' = ofUT (reps idx) t) : False := by
  have hinv := rho_invariant_of_sixCoeff_kvec_any_last rho' hb
  obtain ⟨i, hi⟩ := exists_s_moves_rep idx h0 h4
  have hne : s i v' ≠ v' := by
    intro h
    apply hi
    have hc := congrArg ucoord h
    simpa [hv', s_ofUT, ucoord_ofUT] using hc
  have hroot : rho' (s i v') = 2 := by
    rw [hinv i v', hself']
  let rho'' : Module.Dual K V7 := rho'.comp (s i).symm.toLinearMap
  have hρ'' : rho'' = rho' := by
    apply LinearMap.ext
    intro x
    have h := hinv i ((s i).symm x)
    simpa [rho''] using h.symm
  have hroot'' : rho'' (s i v') = 2 := by
    rw [hρ'']
    exact hroot
  have hconj : s i * Module.reflection hself' * (s i)⁻¹ =
      Module.reflection hroot'' :=
    conj_reflection_eq (s i) hself' hroot''
  have hrefl : Module.reflection hroot'' = Module.reflection hroot := by
    ext x
    rw [Module.reflection_apply, Module.reflection_apply, hρ'']
  have hmem : Module.reflection hroot ∈ H := by
    rw [← hrefl, ← hconj]
    exact H.mul_mem (H.mul_mem (hs i) hr') (H.inv_mem (hs i))
  have heq := CFSG.StandardType.QTwoLin.reflection_root_eq_of_transvectionFree
    hTF hself' hroot hr' hmem
  exact hne heq.symm

theorem reflection_mem_closure_of_axis_zero
    (H : Subgroup (V7 ≃ₗ[K] V7))
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hs : ∀ i : Fin 6, s i ∈ H)
    {v : V7} {rho : Module.Dual K V7}
    (hself : rho v = 2)
    (hr : Module.reflection hself ∈ H)
    (haxis : rho axis = 0) :
    Module.reflection hself ∈ Subgroup.closure (Set.range s) := by
  let w : List (Fin 6) := normWord (ucoord v)
  let g : V7 ≃ₗ[K] V7 := lwordProd w
  have hg : g ∈ H := lwordProd_mem hs w
  let v' : V7 := g v
  let rho' : Module.Dual K V7 := rho.comp g.symm.toLinearMap
  have hself' : rho' v' = 2 := by simp [rho', v', hself]
  have hconj : g * Module.reflection hself * g⁻¹ = Module.reflection hself' :=
    conj_reflection_eq g hself hself'
  have hr' : Module.reflection hself' ∈ H := by
    rw [← hconj]
    exact H.mul_mem (H.mul_mem hg hr) (H.inv_mem hg)
  have hgaxis : g axis = axis := lwordProd_axis w
  have hgsaxis : g.symm axis = axis := by
    have := congrArg g.symm hgaxis
    simpa using this.symm
  have haxis' : rho' axis = 0 := by
    simp [rho', hgsaxis, haxis]
  have hnorm := normWord_spec (ucoord v)
  generalize hidx : normIdx (ucoord v) = idx
  have hrep : applyUWord w (ucoord v) = reps idx := by
    simpa [w, hidx] using hnorm.2
  have hv' : v' = ofUT (reps idx) (tcoord v) := by
    simp [v', g, w, lwordProd_apply, hrep]
  have hconstraint : constraintOK idx (sixCoeff rho') = true := by
    apply constraintOK_eq_true_of_rows
    intro r hr
    have hg_r : lwordProd r.word ∈ H := lwordProd_mem hs r.word
    have hfix_r : lwordProd r.word v' = v' := by
      rw [hv', lwordProd_apply]
      simp only [ucoord_ofUT, tcoord_ofUT]
      rw [word_fixes_rep (idx := idx) hr]
    have hform :=
      CFSG.StandardType.QTwoLin.reflection_form_fixed_of_root_stabilizer
        hTF hself' hr' hg_r hfix_r
    exact dotU_rowDiff_eq_zero rho' hform
  have hallowed := allowed_of_constraintOK idx (sixCoeff rho') hconstraint
  let W : Subgroup (V7 ≃ₗ[K] V7) := Subgroup.closure (Set.range s)
  have hgen : ∀ i : Fin 6, s i ∈ W := fun i =>
    Subgroup.subset_closure (show s i ∈ Set.range s from ⟨i, rfl⟩)
  have hgW : g ∈ W := lwordProd_mem hgen w
  have hs5W : s 5 ∈ W := hgen 5
  fin_cases idx
  ·
    exfalso
    have hv0 : v' = ofUT (0 : U) (tcoord v) := by
      have hz : (![0, 0, 0, 0, 0, 0] : U) = 0 := by decide
      simpa [reps, repsList, hz] using hv'
    have h := hself'
    rw [hv0, rho_apply_ofUT, lastCoeff_apply, haxis'] at h
    have h02 : (0 : K) = 2 := by simpa [dotU] using h
    exact (by decide : (0 : K) ≠ 2) h02
  ·
    exfalso
    change ∃ lam : K, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exact nonzero_rep_contradiction_zero_axis (idx := 1) (by decide) (by decide)
      H hTF hs hself' hr' hb (by simpa using hv')
  ·
    exfalso
    change ∃ lam : K, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exact nonzero_rep_contradiction_zero_axis (idx := 2) (by decide) (by decide)
      H hTF hs hself' hr' hb (by simpa using hv')
  ·
    exfalso
    change ∃ lam : K, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exact nonzero_rep_contradiction_zero_axis (idx := 3) (by decide) (by decide)
      H hTF hs hself' hr' hb (by simpa using hv')
  ·
    change ∃ c d : K, sixCoeff rho' = c • k0vec + d • e5vec at hallowed
    rcases hallowed with ⟨c, d, hb⟩
    have hv4 : v' = ofUT (reps (4 : Fin 8)) (tcoord v) := by simpa using hv'
    have hcd : c + d = 2 := by
      have h := hself'
      rw [hv4, rho_apply_ofUT, hb, lastCoeff_apply, haxis'] at h
      rw [dotU_rep4_all c d] at h
      simpa using h
    have hvT : v' = At72AxisZero.vT (tcoord v) := by
      rw [hv4, At72AxisZero.vT, reps_four_eq_u72]
      rfl
    have hrho : rho' = At72AxisZero.alpha0 c d := by
      apply LinearMap.ext
      intro x
      rw [show x = ofUT (ucoord x) (tcoord x) from (ofUT_ucoord_tcoord x).symm]
      rw [rho_apply_ofUT, hb, lastCoeff_apply, haxis', alpha0_apply_ofUT]
      simp
    have hselfA : At72AxisZero.alpha0 c d (At72AxisZero.vT (tcoord v)) = 2 := by
      rw [← hrho, ← hvT]
      exact hself'
    have hrefl : Module.reflection hselfA = Module.reflection hself' := by
      apply LinearEquiv.ext
      intro x
      rw [Module.reflection_apply, Module.reflection_apply, hrho, hvT]
    have hrA : Module.reflection hselfA ∈ H := by
      rw [hrefl]
      exact hr'
    obtain ⟨hc0, hd2, ht0⟩ :=
      At72AxisZero.no_transvectionFree_axis_zero
        c d (tcoord v) hcd H hTF hs hselfA hrA
    subst hc0
    subst hd2
    have hAeq : Module.reflection hselfA = At72AxisZero.r0 0 2 0 (by decide) := by
      unfold At72AxisZero.r0
      apply LinearEquiv.ext
      intro x
      rw [Module.reflection_apply, Module.reflection_apply, ht0]
    have hr'_s5 : Module.reflection hself' = s 5 := by
      rw [← hrefl, hAeq, At72AxisZero.r0_zero_two_zero_eq_s5]
    have hconj_s5 : g * Module.reflection hself * g⁻¹ = s 5 := by
      rw [hconj, hr'_s5]
    have hr_eq : Module.reflection hself = g⁻¹ * s 5 * g := by
      calc
        Module.reflection hself = g⁻¹ * (g * Module.reflection hself * g⁻¹) * g := by
          group
        _ = g⁻¹ * s 5 * g := by rw [hconj_s5]
    have hmem : Module.reflection hself ∈ W := by
      rw [hr_eq]
      exact W.mul_mem (W.mul_mem (W.inv_mem hgW) hs5W) hgW
    simpa [W] using hmem
  ·
    exfalso
    change ∃ lam : K, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exact nonzero_rep_contradiction_zero_axis (idx := 5) (by decide) (by decide)
      H hTF hs hself' hr' hb (by simpa using hv')
  ·
    exfalso
    change ∃ lam : K, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exact nonzero_rep_contradiction_zero_axis (idx := 6) (by decide) (by decide)
      H hTF hs hself' hr' hb (by simpa using hv')
  ·
    exfalso
    change ∃ lam : K, sixCoeff rho' = lam • kvec at hallowed
    rcases hallowed with ⟨lam, hb⟩
    exact nonzero_rep_contradiction_zero_axis (idx := 7) (by decide) (by decide)
      H hTF hs hself' hr' hb (by simpa using hv')

end CFSG.StandardType.E6DependentDualSeven.FullAxisZero

namespace CFSG.StandardType

open E6DependentDualSeven E6DependentDualSeven.Classification
  E6DependentDualSeven.FullAxisZero

theorem ggWeylJoin_of_e6DualSeven
    {G : Type} [Group G] [Finite G] {Bs L K : Subgroup G}
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    (S : Finset Λ) (hS : S.card = 2) (ha1 : 1 ≤ Nat.card Λa)
    {ML : CoxeterMatrix Λ} {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    (hML : GGIsWeylMatrix ML) (hMK : GGIsWeylMatrix MK)
    (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs))
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    (hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure
      (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    {e : Fin 6 ≃ Λ}
    {ι7 : Additive ↥Bs ≃+ W7}
    (hs : ∀ i : Fin 6, ggLin (p := 3) ι7 (φ (Sum.inl (e i))) = s i)
    (v : Λa → W7) (rho : Λa → Module.Dual F3 W7)
    (hlin_add : ∀ (a : Λa) (x : W7),
      ggLin (p := 3) ι7 (φ (Sum.inr a)) x = x - rho a x • v a)
    (hself : ∀ a, rho a (v a) = 2)
    {H : Subgroup (W7 ≃ₗ[F3] W7)}
    (hTF : CFSG.StandardType.QTwoLin.TransvectionFree H)
    (hsimple : ∀ i : Fin 6, s i ∈ H)
    (hHmem : ∀ a, ggLin (p := 3) ι7 (φ (Sum.inr a)) ∈ H)
    (hHmap : H = (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map
      (ggLin (p := 3) ι7)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hmapAL : (ggAutomizer L Bs).map (ggLin (p := 3) ι7) =
      Subgroup.closure (Set.range s) := by
    rw [hclosL, MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      refine ⟨e.symm i, ?_⟩
      rw [← hs (e.symm i), e.apply_symm_apply]
    · rintro ⟨i, rfl⟩
      exact ⟨φ (Sum.inl (e i)), ⟨e i, rfl⟩, hs i⟩
  have hmemL (i : Λ) : φ (Sum.inl i) ∈ ggAutomizer L Bs := by
    rw [hclosL]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  have hrefl_add (a : Λa) :
      Module.reflection (hself a) = ggLin (p := 3) ι7 (φ (Sum.inr a)) := by
    ext x
    rw [Module.reflection_apply, hlin_add a x]
  have hr_mem (a : Λa) : Module.reflection (hself a) ∈ H := by
    rw [hrefl_add a]
    exact hHmem a
  have hmem_of_axis_zero (a : Λa) (hzero : rho a axis = 0) :
      φ (Sum.inr a) ∈ ggAutomizer L Bs := by
    have hclass : Module.reflection (hself a) ∈ Subgroup.closure (Set.range s) :=
      reflection_mem_closure_of_axis_zero H hTF hsimple (hself a) (hr_mem a) hzero
    have himg : ggLin (p := 3) ι7 (φ (Sum.inr a)) ∈
        (ggAutomizer L Bs).map (ggLin (p := 3) ι7) := by
      rw [hmapAL]
      rw [← hrefl_add a]
      exact hclass
    rw [Subgroup.mem_map] at himg
    obtain ⟨x, hx, hxeq⟩ := himg
    have hx' : x = φ (Sum.inr a) := ggLin_injective (p := 3) ι7 hxeq
    simpa [hx'] using hx
  have hnonzero_of_not_mem {a : Λa}
      (hnot : φ (Sum.inr a) ∉ ggAutomizer L Bs) : rho a axis ≠ 0 := by
    intro hzero
    exact hnot (hmem_of_axis_zero a hzero)
  have haxial_of_not_mem {a : Λa}
      (hnot : φ (Sum.inr a) ∉ ggAutomizer L Bs) : ucoord (v a) = 0 :=
    ucoord_eq_zero_of_axis_ne_zero H hTF hsimple (hself a) (hr_mem a)
      (hnonzero_of_not_mem hnot)
  have hcentral_of_not_mem {a : Λa}
      (hnot : φ (Sum.inr a) ∉ ggAutomizer L Bs) :
      ∀ x ∈ ggAutomizer L Bs, φ (Sum.inr a) * x = x * φ (Sum.inr a) := by
    intro x hx
    have hcomm := reflection_commute_closure_of_ucoord_eq_zero H hTF hsimple
      (hself a) (hr_mem a) (haxial_of_not_mem hnot)
    have hximg : ggLin (p := 3) ι7 x ∈ Subgroup.closure (Set.range s) := by
      rw [← hmapAL]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hc := (hcomm (ggLin (p := 3) ι7 x) hximg).eq
    apply ggLin_injective (p := 3) ι7
    simpa [hrefl_add a, map_mul] using hc
  have hsame_axis {a b : Λa}
      (ha : φ (Sum.inr a) ∉ ggAutomizer L Bs)
      (hb : φ (Sum.inr b) ∉ ggAutomizer L Bs) :
      φ (Sum.inr a) = φ (Sum.inr b) := by
    have heq := reflection_eq_of_ucoord_eq_zero H hTF
      (haxial_of_not_mem ha) (haxial_of_not_mem hb)
      (hself a) (hself b) (hr_mem a) (hr_mem b)
    apply ggLin_injective (p := 3) ι7
    rw [hrefl_add a, hrefl_add b] at heq
    exact heq
  have hrange : Set.range (fun o : {i : Λ // i ∉ S} ⊕ Λa =>
      φ (o.map Subtype.val id)) =
      Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a) := by
    ext g
    constructor
    · rintro ⟨o, rfl⟩
      rcases o with j | a
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hgen : ggAutomizer K Bs = Subgroup.closure
      (Set.range fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) := by
    rw [hclosK, hrange]
  have hNontrivial : Nontrivial ({i : Λ // i ∉ S} ⊕ Λa) := by
    have hcardΛ : Fintype.card Λ = 6 := by
      simpa using (Fintype.card_congr e).symm
    have hcardIn : Fintype.card {j : Λ // j ∈ S} = S.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext j
      simp
    have hcardSurv : Fintype.card {j : Λ // j ∉ S} = 4 := by
      rw [Fintype.card_subtype_compl (fun j : Λ => j ∈ S), hcardIn, hcardΛ, hS]
    have hcardA : Fintype.card Λa = Nat.card Λa := by
      rw [Nat.card_eq_fintype_card]
    have hcardΓ : 2 ≤ Fintype.card ({i : Λ // i ∉ S} ⊕ Λa) := by
      rw [Fintype.card_sum, hcardSurv, hcardA]
      omega
    exact Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hAKleAL : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    by_cases hall : ∀ a : Λa, φ (Sum.inr a) ∈ ggAutomizer L Bs
    · refine ggSimple_all_mem_of_choice hMK fK
        (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) hfK hgen
        1 ?_ ?_
      · intro x hx
        simp
      · intro o
        rcases o with j | a
        · exact Or.inl (hmemL j.val)
        · exact Or.inl (hall a)
    · rw [not_forall] at hall
      obtain ⟨a0, ha0⟩ := hall
      let r : MulAut ↥Bs := φ (Sum.inr a0)
      have hrAL : ∀ x ∈ ggAutomizer L Bs, r * x = x * r := by
        simpa [r] using hcentral_of_not_mem ha0
      have hchoice : ∀ o : {i : Λ // i ∉ S} ⊕ Λa,
          φ (o.map Subtype.val id) ∈ ggAutomizer L Bs ∨
            φ (o.map Subtype.val id) = r := by
        intro o
        rcases o with j | a
        · exact Or.inl (hmemL j.val)
        · by_cases ha : φ (Sum.inr a) ∈ ggAutomizer L Bs
          · exact Or.inl ha
          · exact Or.inr (by simpa [r] using hsame_axis ha ha0)
      refine ggSimple_all_mem_of_choice hMK fK
        (fun o : {i : Λ // i ∉ S} ⊕ Λa => φ (o.map Subtype.val id)) hfK hgen
        r hrAL hchoice
  have hAeq : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizer L Bs :=
    sup_eq_left.mpr hAKleAL
  rw [hAeq]
  exact ⟨Λ, ML, hML, fL, fun i => by
    simpa [hfL i] using hrefl (Sum.inl i)⟩

theorem ggWeylJoin_of_e6DualSeven_transport
    {G : Type} [Group G] [Finite G] {Bs L K : Subgroup G}
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    (S : Finset Λ) (hS : S.card = 2) (ha1 : 1 ≤ Nat.card Λa)
    {ML : CoxeterMatrix Λ} {MK : CoxeterMatrix ({i : Λ // i ∉ S} ⊕ Λa)}
    (hML : GGIsWeylMatrix ML) (hMK : GGIsWeylMatrix MK)
    (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs))
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (Sum.inl i))
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    (hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val id))
    (hclosL : ggAutomizer L Bs = Subgroup.closure
      (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (htransport : ∃ (e : Fin 6 ≃ Λ) (ι7 : Additive ↥Bs ≃+ W7)
        (H : Subgroup (W7 ≃ₗ[F3] W7)),
      (∀ i : Fin 6, ggLin (p := 3) ι7 (φ (Sum.inl (e i))) = s i) ∧
      H = (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι7) ∧
      CFSG.StandardType.QTwoLin.TransvectionFree H ∧
      (∀ i : Fin 6, s i ∈ H) ∧
      (∀ a : Λa, ggLin (p := 3) ι7 (φ (Sum.inr a)) ∈ H)) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨e, ι7, H, hs, hHmap, hTF, hsimple, haddmem⟩ := htransport
  have hdata : ∀ a : Λa, ∃ (v : W7) (rho : Module.Dual F3 W7),
      rho v = 2 ∧ ∀ x : W7,
        ggLin (p := 3) ι7 (φ (Sum.inr a)) x = x - rho x • v :=
    fun a => exists_of_ggIsReflection (p := 3) ι7 (hrefl (Sum.inr a))
  choose v rho hdata' using hdata
  have hself : ∀ a, rho a (v a) = 2 := fun a => (hdata' a).1
  have hlin_add : ∀ (a : Λa) (x : W7),
      ggLin (p := 3) ι7 (φ (Sum.inr a)) x = x - rho a x • v a :=
    fun a => (hdata' a).2
  exact ggWeylJoin_of_e6DualSeven S hS ha1 hML hMK φ hrefl fL hfL fK hfK hclosL hclosK
    (e := e) (ι7 := ι7) hs v rho hlin_add hself hTF hsimple haddmem hHmap

end CFSG.StandardType
