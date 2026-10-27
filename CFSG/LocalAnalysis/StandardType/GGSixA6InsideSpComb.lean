module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Bound.Init
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.StandardType.A6InsideSp

private lemma exists_affine_of_distinct {a0 a1 a2 b0 b1 b2 : ZMod 3}
    (ha01 : a0 ≠ a1) (ha02 : a0 ≠ a2) (ha12 : a1 ≠ a2)
    (hb01 : b0 ≠ b1) (hb02 : b0 ≠ b2) (hb12 : b1 ≠ b2) :
    ∃ u w : ZMod 3, u ≠ 0 ∧ b0 = u * a0 + w ∧ b1 = u * a1 + w ∧ b2 = u * a2 + w := by
  revert a0 a1 a2 b0 b1 b2
  decide

private lemma affine_coeff_eq_zero {a0 a1 c0 c1 : ZMod 3} (ha01 : a0 ≠ a1)
    (h0 : c0 + c1 * a0 = 0) (h1 : c0 + c1 * a1 = 0) : c0 = 0 ∧ c1 = 0 := by
  have hc1 : c1 = 0 := by
    by_contra hc1
    have h : c1 * a0 = c1 * a1 := by linear_combination h0 - h1
    exact ha01 (mul_left_cancel₀ hc1 h)
  refine ⟨?_, hc1⟩
  simpa [hc1] using h0

theorem exists_pair_or_separating {s : ℕ} (P : (Fin s → ZMod 3) → Prop)
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (k : ZMod 3) f, P f → P (k • f))
    {i₀ a b : Fin s} (ha : a ≠ i₀) (hb : b ≠ i₀) {c d : Fin s → ZMod 3}
    (hcP : P c) (hdP : P d) (hc : ∀ i, c i ≠ 0 ↔ i = i₀)
    (hd : ∀ i, d i = 0 ↔ (i = i₀ ∨ i = a ∨ i = b))
    (hker : ∀ f, P f → f a = 0 → f b = 0 → ∃ α β : ZMod 3, f = α • c + β • d)
    (hsurj : ∀ u v : ZMod 3, ∃ f, P f ∧ f a = u ∧ f b = v) :
    (∃ d', P d' ∧ d' i₀ = 0 ∧ d' ≠ 0 ∧
        3 ≤ (Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0).card ∧
        ∀ f, P f → (∀ i, i ≠ i₀ → d' i = 0 → f i = 0) → ∃ α β : ZMod 3, f = α • c + β • d') ∨
      ∀ i j : Fin s, i ≠ j → ∃ f, P f ∧ f i = 0 ∧ f j ≠ 0 := by
  classical
  have hPneg : ∀ f, P f → P (-f) := by
    intro f hf
    simpa using hsmul (-1) f hf
  have hPsub : ∀ f g, P f → P g → P (f - g) := by
    intro f g hf hg
    simpa [sub_eq_add_neg] using hadd f (-g) hf (hPneg g hg)
  have hc0 : c i₀ ≠ 0 := (hc i₀).mpr rfl
  have hczero : ∀ i, i ≠ i₀ → c i = 0 := by
    intro i hi
    by_contra h
    exact hi ((hc i).mp h)
  have hdi0 : d i₀ = 0 := (hd i₀).mpr (Or.inl rfl)
  have hda : d a = 0 := (hd a).mpr (Or.inr (Or.inl rfl))
  have hdb : d b = 0 := (hd b).mpr (Or.inr (Or.inr rfl))
  have hdne : ∀ i, i ≠ i₀ → i ≠ a → i ≠ b → d i ≠ 0 := by
    intro i h1 h2 h3 h
    rcases (hd i).mp h with h' | h' | h'
    · exact h1 h'
    · exact h2 h'
    · exact h3 h'
  obtain ⟨ga, hgaP, hga_a, hga_b⟩ := hsurj 1 0
  obtain ⟨gb, hgbP, hgb_a, hgb_b⟩ := hsurj 0 1
  set ga' : Fin s → ZMod 3 := ga - (ga i₀ / c i₀) • c with hga'def
  set gb' : Fin s → ZMod 3 := gb - (gb i₀ / c i₀) • c with hgb'def
  have hga'P : P ga' := hPsub ga _ hgaP (hsmul _ c hcP)
  have hgb'P : P gb' := hPsub gb _ hgbP (hsmul _ c hcP)
  have hga'i0 : ga' i₀ = 0 := by
    rw [hga'def]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ (ga i₀) hc0, sub_self]
  have hgb'i0 : gb' i₀ = 0 := by
    rw [hgb'def]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ (gb i₀) hc0, sub_self]
  have hga'a : ga' a = 1 := by
    rw [hga'def]
    simp [hczero a ha, hga_a]
  have hgb'a : gb' a = 0 := by
    rw [hgb'def]
    simp [hczero a ha, hgb_a]
  have hga'b : ga' b = 0 := by
    rw [hga'def]
    simp [hczero b hb, hga_b]
  have hgb'b : gb' b = 1 := by
    rw [hgb'def]
    simp [hczero b hb, hgb_b]
  set R : Finset (Fin s) := Finset.univ \ {i₀, a, b} with hRdef
  have hRmem : ∀ i, i ∈ R ↔ i ≠ i₀ ∧ i ≠ a ∧ i ≠ b := by
    intro i
    rw [hRdef]
    simp
  have hdR : ∀ r ∈ R, d r ≠ 0 := by
    intro r hr
    obtain ⟨h1, h2, h3⟩ := (hRmem r).mp hr
    exact hdne r h1 h2 h3
  set al : Fin s → ZMod 3 := fun r => ga' r / d r with haldef
  set be : Fin s → ZMod 3 := fun r => gb' r / d r with hbedef
  have hal_mul : ∀ r ∈ R, ga' r = al r * d r := by
    intro r hr
    exact (div_mul_cancel₀ (ga' r) (hdR r hr)).symm
  have hbe_mul : ∀ r ∈ R, gb' r = be r * d r := by
    intro r hr
    exact (div_mul_cancel₀ (gb' r) (hdR r hr)).symm
  have decomp : ∀ f, P f → ∃ x y : ZMod 3, f = x • c + y • d + f a • ga' + f b • gb' := by
    intro f hf
    have hP1 : P (f - f a • ga' - f b • gb') :=
      hPsub (f - f a • ga') (f b • gb')
        (hPsub f (f a • ga') hf (hsmul _ _ hga'P)) (hsmul _ _ hgb'P)
    have hza : (f - f a • ga' - f b • gb') a = 0 := by
      simp [hga'a, hgb'a]
    have hzb : (f - f a • ga' - f b • gb') b = 0 := by
      simp [hga'b, hgb'b]
    obtain ⟨x, y, hxy⟩ := hker _ hP1 hza hzb
    refine ⟨x, y, ?_⟩
    rw [← hxy]
    abel
  have heval : ∀ (f : Fin s → ZMod 3) (x y : ZMod 3),
      f = x • c + y • d + f a • ga' + f b • gb' →
      ∀ r ∈ R, f r = d r * (y + f a * al r + f b * be r) := by
    intro f x y hrep r hr
    have hc_r : c r = 0 := hczero r ((hRmem r).mp hr).1
    rw [congrFun hrep r]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc_r, hal_mul r hr,
      hbe_mul r hr, mul_zero, zero_add]
    ring
  by_cases hA : ∃ r ∈ R, ∃ t ∈ R, r ≠ t ∧ al r = al t
  · left
    obtain ⟨r, hrR, t, htR, hrt, halt⟩ := hA
    obtain ⟨hri0, hra, hrb⟩ := (hRmem r).mp hrR
    obtain ⟨hti0, hta, htb⟩ := (hRmem t).mp htR
    set d' : Fin s → ZMod 3 := ga' - al r • d with hd'def
    have hd'P : P d' := hPsub ga' _ hga'P (hsmul _ d hdP)
    have hd'i0 : d' i₀ = 0 := by
      rw [hd'def]
      simp [hga'i0, hdi0]
    have hd'b : d' b = 0 := by
      rw [hd'def]
      simp [hga'b, hdb]
    have hd'a : d' a = 1 := by
      rw [hd'def]
      simp [hga'a, hda]
    have hd'ne : d' ≠ 0 := by
      intro h
      have h1 := congrFun h a
      rw [hd'a] at h1
      have h2 : (1 : ZMod 3) = 0 := by simpa using h1
      exact one_ne_zero h2
    have hd'r : d' r = 0 := by
      rw [hd'def]
      simp [hal_mul r hrR]
    have hd't : d' t = 0 := by
      rw [hd'def]
      simp [hal_mul t htR, halt]
    have hcard : 3 ≤ (Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0).card := by
      have hsub : ({b, r, t} : Finset (Fin s)) ⊆
          Finset.univ.filter (fun i => i ≠ i₀ ∧ d' i = 0) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hd'b⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri0, hd'r⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hti0, hd't⟩
      have h3 : ({b, r, t} : Finset (Fin s)).card = 3 :=
        Finset.card_eq_three.mpr
          ⟨b, r, t, (Ne.symm hrb), (Ne.symm htb), hrt, rfl⟩
      calc 3 = ({b, r, t} : Finset (Fin s)).card := h3.symm
        _ ≤ _ := Finset.card_le_card hsub
    refine ⟨d', hd'P, hd'i0, hd'ne, hcard, ?_⟩
    intro f hf hv
    have hfb : f b = 0 := hv b hb hd'b
    have hfr : f r = 0 := hv r hri0 hd'r
    have hP1 : P (f - f a • d') := hPsub f _ hf (hsmul _ _ hd'P)
    have hza : (f - f a • d') a = 0 := by
      simp [hd'a]
    have hzb : (f - f a • d') b = 0 := by
      simp [hd'b, hfb]
    obtain ⟨x, y, hxy⟩ := hker _ hP1 hza hzb
    have hy0 : y = 0 := by
      have hr : y * d r = 0 := by
        have h := congrFun hxy r
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd'r, hfr,
          hczero r hri0, mul_zero, sub_zero, zero_add] at h
        simpa using h.symm
      exact (mul_eq_zero.mp hr).resolve_right (hdR r hrR)
    have hfin : f - f a • d' = x • c := by
      rw [hxy, hy0, zero_smul, add_zero]
    exact ⟨x, f a, sub_eq_iff_eq_add.mp hfin⟩
  by_cases hB : ∃ r ∈ R, ∃ t ∈ R, r ≠ t ∧ be r = be t
  · left
    obtain ⟨r, hrR, t, htR, hrt, hbet⟩ := hB
    obtain ⟨hri0, hra, hrb⟩ := (hRmem r).mp hrR
    obtain ⟨hti0, hta, htb⟩ := (hRmem t).mp htR
    set d' : Fin s → ZMod 3 := gb' - be r • d with hd'def
    have hd'P : P d' := hPsub gb' _ hgb'P (hsmul _ d hdP)
    have hd'i0 : d' i₀ = 0 := by
      rw [hd'def]
      simp [hgb'i0, hdi0]
    have hd'a : d' a = 0 := by
      rw [hd'def]
      simp [hgb'a, hda]
    have hd'b : d' b = 1 := by
      rw [hd'def]
      simp [hgb'b, hdb]
    have hd'ne : d' ≠ 0 := by
      intro h
      have h1 := congrFun h b
      rw [hd'b] at h1
      have h2 : (1 : ZMod 3) = 0 := by simpa using h1
      exact one_ne_zero h2
    have hd'r : d' r = 0 := by
      rw [hd'def]
      simp [hbe_mul r hrR]
    have hd't : d' t = 0 := by
      rw [hd'def]
      simp [hbe_mul t htR, hbet]
    have hcard : 3 ≤ (Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0).card := by
      have hsub : ({a, r, t} : Finset (Fin s)) ⊆
          Finset.univ.filter (fun i => i ≠ i₀ ∧ d' i = 0) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hd'a⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri0, hd'r⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hti0, hd't⟩
      have h3 : ({a, r, t} : Finset (Fin s)).card = 3 :=
        Finset.card_eq_three.mpr
          ⟨a, r, t, (Ne.symm hra), (Ne.symm hta), hrt, rfl⟩
      calc 3 = ({a, r, t} : Finset (Fin s)).card := h3.symm
        _ ≤ _ := Finset.card_le_card hsub
    refine ⟨d', hd'P, hd'i0, hd'ne, hcard, ?_⟩
    intro f hf hv
    have hfa : f a = 0 := hv a ha hd'a
    have hfr : f r = 0 := hv r hri0 hd'r
    have hP1 : P (f - f b • d') := hPsub f _ hf (hsmul _ _ hd'P)
    have hza : (f - f b • d') a = 0 := by
      simp [hd'a, hfa]
    have hzb : (f - f b • d') b = 0 := by
      simp [hd'b]
    obtain ⟨x, y, hxy⟩ := hker _ hP1 hza hzb
    have hy0 : y = 0 := by
      have hr : y * d r = 0 := by
        have h := congrFun hxy r
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd'r, hfr,
          hczero r hri0, mul_zero, sub_zero, zero_add] at h
        simpa using h.symm
      exact (mul_eq_zero.mp hr).resolve_right (hdR r hrR)
    have hfin : f - f b • d' = x • c := by
      rw [hxy, hy0, zero_smul, add_zero]
    exact ⟨x, f b, sub_eq_iff_eq_add.mp hfin⟩
  have hinjal : ∀ r ∈ R, ∀ t ∈ R, al r = al t → r = t := by
    intro r hr t ht h
    by_contra hne
    exact hA ⟨r, hr, t, ht, hne, h⟩
  have hinjbe : ∀ r ∈ R, ∀ t ∈ R, be r = be t → r = t := by
    intro r hr t ht h
    by_contra hne
    exact hB ⟨r, hr, t, ht, hne, h⟩
  by_cases hR3 : R.card = 3
  ·
    left
    obtain ⟨r0, r1, r2, hr01, hr02, hr12, hReq⟩ := Finset.card_eq_three.mp hR3
    have hr0 : r0 ∈ R := by rw [hReq]; simp
    have hr1 : r1 ∈ R := by rw [hReq]; simp
    have hr2 : r2 ∈ R := by rw [hReq]; simp
    have hal01 : al r0 ≠ al r1 := fun h => hr01 (hinjal r0 hr0 r1 hr1 h)
    have hal02 : al r0 ≠ al r2 := fun h => hr02 (hinjal r0 hr0 r2 hr2 h)
    have hal12 : al r1 ≠ al r2 := fun h => hr12 (hinjal r1 hr1 r2 hr2 h)
    have hbe01 : be r0 ≠ be r1 := fun h => hr01 (hinjbe r0 hr0 r1 hr1 h)
    have hbe02 : be r0 ≠ be r2 := fun h => hr02 (hinjbe r0 hr0 r2 hr2 h)
    have hbe12 : be r1 ≠ be r2 := fun h => hr12 (hinjbe r1 hr1 r2 hr2 h)
    obtain ⟨u, w, hu, hbe0, hbe1, hbe2⟩ :=
      exists_affine_of_distinct hal01 hal02 hal12 hbe01 hbe02 hbe12
    set d' : Fin s → ZMod 3 := (-w) • d - u • ga' + gb' with hd'def
    have hd'P : P d' := by
      rw [hd'def]
      exact hadd ((-w) • d - u • ga') gb'
        (hPsub ((-w) • d) (u • ga') (hsmul _ d hdP) (hsmul _ ga' hga'P)) hgb'P
    have hd'i0 : d' i₀ = 0 := by
      rw [hd'def]
      simp [hdi0, hga'i0, hgb'i0]
    have hd'a : d' a = -u := by
      rw [hd'def]
      simp [hda, hga'a, hgb'a]
    have hd'ne : d' ≠ 0 := by
      intro h
      have h1 := congrFun h a
      rw [hd'a] at h1
      exact hu (neg_eq_zero.mp h1)
    have hdz0 : d' r0 = 0 := by
      rw [hd'def]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hal_mul r0 hr0,
        hbe_mul r0 hr0, hbe0]
      ring
    have hdz1 : d' r1 = 0 := by
      rw [hd'def]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hal_mul r1 hr1,
        hbe_mul r1 hr1, hbe1]
      ring
    have hdz2 : d' r2 = 0 := by
      rw [hd'def]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hal_mul r2 hr2,
        hbe_mul r2 hr2, hbe2]
      ring
    have hcard : 3 ≤ (Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0).card := by
      have hsub : ({r0, r1, r2} : Finset (Fin s)) ⊆
          Finset.univ.filter (fun i => i ≠ i₀ ∧ d' i = 0) := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with h | h | h
        · rw [h]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hRmem r0).mp hr0).1, hdz0⟩
        · rw [h]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hRmem r1).mp hr1).1, hdz1⟩
        · rw [h]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hRmem r2).mp hr2).1, hdz2⟩
      have h3 : ({r0, r1, r2} : Finset (Fin s)).card = 3 :=
        Finset.card_eq_three.mpr ⟨r0, r1, r2, hr01, hr02, hr12, rfl⟩
      calc 3 = ({r0, r1, r2} : Finset (Fin s)).card := h3.symm
        _ ≤ _ := Finset.card_le_card hsub
    refine ⟨d', hd'P, hd'i0, hd'ne, hcard, ?_⟩
    intro f hf hv
    obtain ⟨x, y, hrep⟩ := decomp f hf
    have hz0 : y + f a * al r0 + f b * be r0 = 0 := by
      have h := heval f x y hrep r0 hr0
      rw [hv r0 ((hRmem r0).mp hr0).1 hdz0] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (hdR r0 hr0)
    have hz1 : y + f a * al r1 + f b * be r1 = 0 := by
      have h := heval f x y hrep r1 hr1
      rw [hv r1 ((hRmem r1).mp hr1).1 hdz1] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (hdR r1 hr1)
    have hz2 : y + f a * al r2 + f b * be r2 = 0 := by
      have h := heval f x y hrep r2 hr2
      rw [hv r2 ((hRmem r2).mp hr2).1 hdz2] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (hdR r2 hr2)
    have hl0 : (y + w * f b) + (f a + u * f b) * al r0 = 0 := by
      rw [hbe0] at hz0
      calc (y + w * f b) + (f a + u * f b) * al r0
          = y + f a * al r0 + f b * (u * al r0 + w) := by ring
        _ = 0 := hz0
    have hl1 : (y + w * f b) + (f a + u * f b) * al r1 = 0 := by
      rw [hbe1] at hz1
      calc (y + w * f b) + (f a + u * f b) * al r1
          = y + f a * al r1 + f b * (u * al r1 + w) := by ring
        _ = 0 := hz1
    have hl2 : (y + w * f b) + (f a + u * f b) * al r2 = 0 := by
      rw [hbe2] at hz2
      calc (y + w * f b) + (f a + u * f b) * al r2
          = y + f a * al r2 + f b * (u * al r2 + w) := by ring
        _ = 0 := hz2
    obtain ⟨hy, hfa⟩ := affine_coeff_eq_zero hal01 hl0 hl1
    have hyw : y = -w * f b := by linear_combination hy
    have hfau : f a = -u * f b := by linear_combination hfa
    refine ⟨x, f b, ?_⟩
    calc f = x • c + y • d + f a • ga' + f b • gb' := hrep
      _ = x • c + f b • d' := by
        rw [hyw, hfau, hd'def]
        module
  ·
    right
    intro i j hij
    rcases eq_or_ne j i₀ with hj0 | hj0
    · subst j
      exact ⟨c, hcP, hczero i hij, hc0⟩
    rcases eq_or_ne i i₀ with hi0 | hi0
    · subst i
      rcases eq_or_ne j a with hja | hja
      · subst j
        exact ⟨ga', hga'P, hga'i0, by simp [hga'a]⟩
      rcases eq_or_ne j b with hjb | hjb
      · subst j
        exact ⟨gb', hgb'P, hgb'i0, by simp [hgb'b]⟩
      · have hjr : j ∈ R := (hRmem j).mpr ⟨hj0, hja, hjb⟩
        exact ⟨d, hdP, hdi0, hdR j hjr⟩
    rcases eq_or_ne i a with hia | hia
    · subst i
      have hja : j ≠ a := Ne.symm hij
      rcases eq_or_ne j b with hjb | hjb
      · subst j
        exact ⟨gb', hgb'P, hgb'a, by simp [hgb'b]⟩
      · have hjr : j ∈ R := (hRmem j).mpr ⟨hj0, hja, hjb⟩
        exact ⟨d, hdP, hda, hdR j hjr⟩
    rcases eq_or_ne i b with hib | hib
    · subst i
      have hjb : j ≠ b := Ne.symm hij
      rcases eq_or_ne j a with hja | hja
      · subst j
        exact ⟨ga', hga'P, hga'b, by simp [hga'a]⟩
      · have hjr : j ∈ R := (hRmem j).mpr ⟨hj0, hja, hjb⟩
        exact ⟨d, hdP, hdb, hdR j hjr⟩
    · have hir : i ∈ R := (hRmem i).mpr ⟨hi0, hia, hib⟩
      rcases eq_or_ne j a with hja | hja
      · subst j
        refine ⟨ga' - al i • d, hPsub ga' _ hga'P (hsmul _ d hdP), ?_, ?_⟩
        · simp [hal_mul i hir]
        · simp [hga'a, hda]
      rcases eq_or_ne j b with hjb | hjb
      · subst j
        refine ⟨gb' - be i • d, hPsub gb' _ hgb'P (hsmul _ d hdP), ?_, ?_⟩
        · simp [hbe_mul i hir]
        · simp [hgb'b, hdb]
      · have hjr : j ∈ R := (hRmem j).mpr ⟨hj0, hja, hjb⟩
        have hne : al j ≠ al i := by
          intro h
          exact hij (hinjal j hjr i hir h).symm
        refine ⟨ga' - al i • d, hPsub ga' _ hga'P (hsmul _ d hdP), ?_, ?_⟩
        · simp [hal_mul i hir]
        · have hval : (ga' - al i • d) j = (al j - al i) * d j := by
            simp [hal_mul j hjr]
            ring
          rw [hval]
          exact mul_ne_zero (sub_ne_zero.mpr hne) (hdR j hjr)

end CFSG.StandardType.A6InsideSp
