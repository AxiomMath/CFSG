module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmExistAux_dRef_axis {n : ℕ} {h : DV n} (h0 : h 0 = 0) :
    dRef (1 : ZMod 3) (dE n 0) h = h := by
  simp [dRef, dB, dE, h0]

private lemma hdRo7DSmExistAux_dRef_axis_self {n : ℕ} (ρ : ZMod 3) (hρ : ρ ≠ 0) :
    dRef ρ (dE n 0) (dE n 0) = -dE n 0 := by
  have hρ2 : ρ * ρ = 1 := (by decide : ∀ ρ : ZMod 3, ρ ≠ 0 → ρ * ρ = 1) ρ hρ
  have hcoef : 2 * dB ρ (dE n 0) (dE n 0) * dB ρ (dE n 0) (dE n 0) = (2 : ZMod 3) := by
    have hb : dB ρ (dE n 0) (dE n 0) = ρ := by simp [dB, dE]
    rw [hb]
    calc 2 * ρ * ρ = 2 * (ρ * ρ) := by ring
      _ = 2 := by rw [hρ2, mul_one]
  rw [dRef, hcoef]
  ext j
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply]
  ring

private lemma hdRo7DSmExistAux_axis_reflect_self {n : ℕ} {ρ : ZMod 3} {r : DGL n}
    (hr : DRefl ρ r (dE n 0)) : r (dE n 0) = -dE n 0 := by
  have hρ : ρ ≠ 0 := by
    intro h0
    apply hr.1
    rw [h0]
    simp [dB, dE]
  rw [dRefl_apply hr]
  exact hdRo7DSmExistAux_dRef_axis_self ρ hρ

private lemma hdRo7DSmExistAux_coord_dStd {n : ℕ} (h : DV n) :
    (dStd n).coord 0 h = h 0 := by
  rw [Module.Basis.coord_apply, Pi.basisFun_repr]

private lemma hdRo7DSmExistAux_dAct_dE {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (c : Fin (n + 1) → ZMod 3) (i : Fin (n + 1)) :
    dAct σ c (dE n i) = c i • dE n (σ i) := by
  ext j
  simp only [dAct, dE, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hj : j = σ i
  · subst hj
    simp
  · have hji : σ.symm j ≠ i := fun h => hj ((Equiv.symm_apply_eq σ).mp h)
    rw [if_neg hj, if_neg hji, mul_zero, mul_zero]

private lemma hdRo7DSmExistAux_move_le {n : ℕ} {ρ : ZMod 3} {r : DGL n} {h : DV n}
    (hr : DRefl ρ r h) (h0 : h 0 = 0) :
    ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0) := by
  rw [ggLinMove_of_dRefl hr]
  exact Submodule.span_le.mpr (by
    rintro x rfl
    show (dStd n).coord 0 x = 0
    rw [hdRo7DSmExistAux_coord_dStd]
    exact h0)

private lemma hdRo7DSmExistAux_shape
    (hNorm : DSmNormLeaf) (hN : DNormalizerLeaf) (hF : DReflFixLeaf)
    {n : ℕ} {H A : Subgroup (DGL n)} (hD : DLinData 3 n (DV n) (dStd n) H A)
    (hno : ¬ ∃ r ∈ H, ∃ ρ : ZMod 3, ρ ≠ 0 ∧ ∃ h : DV n, h 0 = 1 ∧ dSupp h ≠ 0 ∧
      DRefl ρ r h)
    {s : DGL n} (hsH : s ∈ H) (hsR : GGLinRefl s) :
    (∃ h : DV n, h 0 = 0 ∧ DRefl 1 s h) ∨
      (∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ s (dE n 0)) := by
  rcases hNorm hN hF n H A hD s hsH hsR with ⟨h, h0, -, hrefl⟩ | haxis | ⟨ρ, hρ, h, h0, hsupp, hr⟩
  · exact Or.inl ⟨h, h0, hrefl 1 (by decide)⟩
  · exact Or.inr haxis
  · exact absurd ⟨s, hsH, ρ, hρ, h, h0, hsupp, hr⟩ hno

private lemma hdRo7DSmExistAux_internal_fix
    {n : ℕ} {H A : Subgroup (DGL n)} (hD : DLinData 3 n (DV n) (dStd n) H A)
    (hF : DReflFixLeaf) {s : DGL n} (hsH : s ∈ H) (hsR : GGLinRefl s)
    {h : DV n} (h0 : h 0 = 0) (hr : DRefl 1 s h) : s (dE n 0) = dE n 0 := by
  have hfix := hF 3 n (DV n) (dStd n) H A hD s hsH hsR
    (hdRo7DSmExistAux_move_le hr h0)
  rwa [show (dStd n) 0 = dE n 0 by simp [dStd, dE]] at hfix

private theorem hdRo7DSmExistAux_main (hNorm : DSmNormLeaf) (hN : DNormalizerLeaf)
    (hF : DReflFixLeaf) : ∀ (n : ℕ) (H A : Subgroup (DGL n)),
    DLinData 3 n (DV n) (dStd n) H A →
    (∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0)) →
    ∃ r ∈ H, ∃ ρ : ZMod 3, ρ ≠ 0 ∧ ∃ h : DV n, h 0 = 1 ∧ dSupp h ≠ 0 ∧ DRefl ρ r h := by
  intro n H A hD hOut
  obtain ⟨r0, hr0H, hr0Refl, hr0Ext⟩ := hOut
  by_contra hno
  have hr0axis : ∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ r0 (dE n 0) := by
    rcases hdRo7DSmExistAux_shape hNorm hN hF hD hno hr0H hr0Refl with
      ⟨h, h0, hr⟩ | haxis
    · exfalso
      exact hr0Ext (hdRo7DSmExistAux_move_le hr h0)
    · exact haxis
  have hr0sq : r0 * r0 = 1 := (ggLinRefl_of_dRefl (hr0axis 1 (by decide))).1
  obtain ⟨S, hS, hScl, hSconn⟩ := hD.hgen
  have hSshape : ∀ s ∈ S, (∃ h : DV n, h 0 = 0 ∧ DRefl 1 s h) ∨ s = r0 := by
    intro s hs
    rcases hdRo7DSmExistAux_shape hNorm hN hF hD hno (hS s hs).1 (hS s hs).2 with
      ⟨h, h0, hr⟩ | haxis
    · exact Or.inl ⟨h, h0, hr⟩
    · exact Or.inr (dRefl_unique (haxis 1 (by decide)) (hr0axis 1 (by decide)))
  have hr0S : r0 ∈ S := by
    by_contra hnot
    have hfixS : ∀ s ∈ S, s (dE n 0) = dE n 0 := by
      intro s hs
      rcases hSshape s hs with ⟨h, h0, hr⟩ | hs0
      · exact hdRo7DSmExistAux_internal_fix hD hF (hS s hs).1 (hS s hs).2 h0 hr
      · exact absurd (hs0 ▸ hs) hnot
    let K : Subgroup (DGL n) :=
      { carrier := {a | a (dE n 0) = dE n 0}
        one_mem' := rfl
        mul_mem' := by
          intro a c ha hc
          show (a * c) (dE n 0) = dE n 0
          rw [LinearEquiv.mul_apply, hc, ha]
        inv_mem' := by
          intro a ha
          show a.symm (dE n 0) = dE n 0
          apply a.injective
          rw [a.apply_symm_apply, ha] }
    have hHK : H ≤ K := by
      rw [hScl]
      exact (Subgroup.closure_le K).mpr hfixS
    have hr0K : r0 (dE n 0) = dE n 0 := hHK hr0H
    have hr0E : r0 (dE n 0) = -dE n 0 :=
      hdRo7DSmExistAux_axis_reflect_self (hr0axis 1 (by decide))
    have hEq : -dE n 0 = dE n 0 := hr0E.symm.trans hr0K
    have hcoord : (-1 : ZMod 3) = 1 := by
      have := congrFun hEq 0
      simpa [dE] using this
    exact absurd hcoord (by decide)
  have hcommS : ∀ s ∈ S, Commute r0 s := by
    intro s hs
    rcases hSshape s hs with ⟨h, h0, hr⟩ | hs0
    · have hcong : DRefl 1 (r0 * s * r0⁻¹) h := by
        have hconj := dRefl_conj (hr := hr0axis 1 (by decide)) (hs := hr)
        rwa [hdRo7DSmExistAux_dRef_axis h0] at hconj
      have hEq : r0 * s * r0⁻¹ = s := dRefl_unique hcong hr
      have hmul : (r0 * s * r0⁻¹) * r0 = s * r0 := congrArg (fun x : DGL n => x * r0) hEq
      show r0 * s = s * r0
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
    · rw [hs0]
  have hSsing : ∀ t ∈ S, t = r0 := by
    intro t ht
    have hconn : Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ¬ Commute u v) r0 t :=
      hSconn r0 hr0S t ht
    rcases Relation.ReflTransGen.cases_head hconn with h | ⟨c, hstep, hrest⟩
    · exact h.symm
    · exact absurd (hcommS c hstep.2.1) hstep.2.2
  let T : Subgroup (DGL n) :=
    { carrier := {x | x = 1 ∨ x = r0}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · rw [hx, hy]; exact Or.inl (one_mul 1)
        · rw [hx, hy]; exact Or.inr (one_mul r0)
        · rw [hx, hy]; exact Or.inr (mul_one r0)
        · rw [hx, hy]; exact Or.inl hr0sq
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · rw [hx]; exact Or.inl inv_one
        · rw [hx]; exact Or.inr (inv_eq_of_mul_eq_one_right hr0sq) }
  have hHT : H ≤ T := by
    rw [hScl]
    exact (Subgroup.closure_le T).mpr (fun t ht => Or.inr (hSsing t ht))
  have hn2 : 2 ≤ n := by have := hD.hn; omega
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let j : Fin (n + 1) := ⟨2, by omega⟩
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i j
  let c : Fin (n + 1) → ZMod 3 := fun _ => 1
  have hc : ∀ k, c k = 1 ∨ c k = -1 := fun k => Or.inl rfl
  have hdsp : DSPData σ c := by
    refine ⟨?_, rfl, hc, ?_⟩
    · show Equiv.swap i j 0 = 0
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [i]) (by simp [j])]
    · simp [c]
  have hτDSP : DSP 3 (dStd n) (dActL σ c hdsp.2.2.1) := dsp_dActL hdsp
  have hτH : dActL σ c hdsp.2.2.1 ∈ H := hD.hPH _ hτDSP
  have hτcases : dActL σ c hdsp.2.2.1 = 1 ∨ dActL σ c hdsp.2.2.1 = r0 := hHT hτH
  have hτe0 : dActL σ c hdsp.2.2.1 (dE n 0) = dE n 0 := by
    rw [dActL_apply, hdRo7DSmExistAux_dAct_dE σ c 0, hdsp.1]
    simp [c]
  have hτei : dActL σ c hdsp.2.2.1 (dE n i) = dE n j := by
    rw [dActL_apply, hdRo7DSmExistAux_dAct_dE σ c i]
    simp [σ, c]
  have hτne1 : dActL σ c hdsp.2.2.1 ≠ 1 := by
    intro h
    have h1 : dE n j = dE n i := by
      rw [← hτei, h]
      simp
    have hcoord := congrFun h1 j
    simp [dE, i, j] at hcoord
  have hτner0 : dActL σ c hdsp.2.2.1 ≠ r0 := by
    intro h
    have h0 : dE n 0 = -dE n 0 := by
      have h1 : dE n 0 = r0 (dE n 0) :=
        hτe0.symm.trans (congrArg (fun x : DGL n => x (dE n 0)) h)
      exact h1.trans (hdRo7DSmExistAux_axis_reflect_self (hr0axis 1 (by decide)))
    have hcoord : (1 : ZMod 3) = -1 := by
      have := congrFun h0 0
      simpa [dE] using this
    exact absurd hcoord (by decide)
  rcases hτcases with h | h
  · exact hτne1 h
  · exact hτner0 h

theorem dSmExist_holds : DSmExistLeaf := hdRo7DSmExistAux_main

end CFSG.StandardType.HdRo7D.Small
