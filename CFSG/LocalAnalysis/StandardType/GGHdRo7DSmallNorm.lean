module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallClassAux
import CFSG.LocalAnalysis.StandardType.GGQTwoTransvectionFreeRules
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge
import CFSG.LocalAnalysis.StandardType.GGWAutCommon
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType.HdRo7D.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DSmNormAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma hdRo7DSmNormAux_dE_self {n : ℕ} (i : Fin (n + 1)) : dE n i i = 1 := by
  simp [dE]

private lemma hdRo7DSmNormAux_dE_of_ne {n : ℕ} {i j : Fin (n + 1)} (h : j ≠ i) :
    dE n i j = 0 := by
  simp [dE, Pi.single_eq_of_ne h]

private lemma hdRo7DSmNormAux_dStd_apply {n : ℕ} (i : Fin (n + 1)) : dStd n i = dE n i := by
  simp [dStd, dE, Pi.basisFun_apply]

private lemma hdRo7DSmNormAux_dStd_coord {n : ℕ} (i : Fin (n + 1)) (x : DV n) :
    (dStd n).coord i x = x i := by
  simp [dStd, Module.Basis.coord_apply]

private lemma hdRo7DSmNormAux_dB_add_left {n : ℕ} (ρ : ZMod 3) (x y z : DV n) :
    dB ρ (x + y) z = dB ρ x z + dB ρ y z := by
  simp only [dB, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma hdRo7DSmNormAux_dB_dE_zero {n : ℕ} (ρ : ZMod 3) (y : DV n) :
    dB ρ (dE n 0) y = ρ * y 0 := by
  have h0 : ∀ i : Fin n, dE n 0 i.succ = 0 :=
    fun i => hdRo7DSmNormAux_dE_of_ne (Fin.succ_ne_zero i)
  simp only [dB, hdRo7DSmNormAux_dE_self, h0, zero_mul, Finset.sum_const_zero, add_zero,
    mul_one]

private lemma hdRo7DSmNormAux_dB_dE_succ {n : ℕ} (ρ : ZMod 3) (i : Fin n) (y : DV n) :
    dB ρ (dE n i.succ) y = y i.succ := by
  have h0 : dE n i.succ (0 : Fin (n + 1)) = 0 :=
    hdRo7DSmNormAux_dE_of_ne (Fin.succ_ne_zero i).symm
  simp only [dB, h0]
  rw [Finset.sum_eq_single i]
  · rw [hdRo7DSmNormAux_dE_self, one_mul]
    ring
  · intro b _ hb
    rw [hdRo7DSmNormAux_dE_of_ne (fun h : b.succ = i.succ => hb (Fin.succ_inj.mp h)), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma hdRo7DSmNormAux_dB_dE_zero_right {n : ℕ} (ρ : ZMod 3) (y : DV n) :
    dB ρ y (dE n 0) = ρ * y 0 := by
  have h0 : ∀ i : Fin n, dE n 0 i.succ = 0 :=
    fun i => hdRo7DSmNormAux_dE_of_ne (Fin.succ_ne_zero i)
  simp only [dB, hdRo7DSmNormAux_dE_self, h0, mul_zero, Finset.sum_const_zero, add_zero,
    mul_one]

private lemma hdRo7DSmNormAux_move_eq_span {n : ℕ} {r : DGL n} {h : DV n}
    {φ : Module.Dual (ZMod 3) (DV n)} (hφ2 : φ h = 2) (hrf : ∀ v, r v = v - φ v • h) :
    ggLinMove r = Submodule.span (ZMod 3) {h} := by
  apply le_antisymm
  · intro x hx
    change x ∈ LinearMap.range (r.toLinearMap - LinearMap.id) at hx
    rw [LinearMap.mem_range] at hx
    obtain ⟨v, rfl⟩ := hx
    change r v - v ∈ Submodule.span (ZMod 3) {h}
    rw [hrf v]
    rw [show (v - φ v • h) - v = -(φ v • h) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton h)))
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    change h ∈ LinearMap.range (r.toLinearMap - LinearMap.id)
    rw [LinearMap.mem_range]
    refine ⟨h, ?_⟩
    change r h - h = h
    rw [hrf h, hφ2]
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2, neg_one_smul]
    abel

private lemma hdRo7DSmNormAux_shape_of_two {n : ℕ} {h : DV n} {a b : Fin (n + 1)}
    (hne : h ≠ 0) (hsupp : ∀ k, k ≠ a → k ≠ b → h k = 0) :
    dIsD h ∨ dIsO h := by
  by_cases ha : h a = 0
  · have hb : ∀ k, k ≠ b → h k = 0 := by
      intro k hk
      by_cases hka : k = a
      · rw [hka]; exact ha
      · exact hsupp k hka hk
    by_cases hhb : h b = 0
    · exfalso
      apply hne
      funext k
      by_cases hkb : k = b
      · rw [hkb]; exact hhb
      · exact hb k hkb
    · exact Or.inr ⟨b, hhb, hb⟩
  · by_cases hba : b = a
    · have hb : h b ≠ 0 := by rw [hba]; exact ha
      exact Or.inr ⟨b, hb, fun k hk => hsupp k (by rw [← hba]; exact hk) hk⟩
    · by_cases hhb : h b = 0
      · exact Or.inr ⟨a, ha, fun k hk => by
          by_cases hkb : k = b
          · rw [hkb]; exact hhb
          · exact hsupp k hk hkb⟩
      · exact Or.inl ⟨a, b, fun h => hba h.symm, ha, hhb, fun k hka hkb => hsupp k hka hkb⟩

private lemma hdRo7DSmNormAux_supp_of_shape {n : ℕ} {h : DV n} (h0 : h 0 = 0)
    (hs : dIsD h ∨ dIsO h) : dSupp h = 1 ∨ dSupp h = 2 := by
  rcases hs with hD | hO
  · rcases (dIsD_iff h).mp hD with ⟨-, h2⟩ | ⟨hne, -⟩
    · exact Or.inr h2
    · exact absurd h0 hne
  · rcases (dIsO_iff h).mp hO with ⟨-, h1⟩ | ⟨hne, -⟩
    · exact Or.inl h1
    · exact absurd h0 hne

private theorem hdRo7DSmNormAux_caseA {n : ℕ} (hN : DNormalizerLeaf) (hF : DReflFixLeaf)
    {H A : Subgroup (DGL n)} (hD : DLinData 3 n (DV n) (dStd n) H A)
    {r : DGL n} (hrH : r ∈ H) (hr : GGLinRefl r) {h : DV n}
    {φ : Module.Dual (ZMod 3) (DV n)} (hφ2 : φ h = 2)
    (hrf : ∀ v, r v = v - φ v • h) (h0 : h 0 = 0) :
    ∃ h : DV n, h 0 = 0 ∧ (dIsD h ∨ dIsO h) ∧ ∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ r h := by
  have hne : h ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hφ2
    exact hdRo7DSmNormAux_two_ne_zero hφ2.symm
  have hle : ggLinMove r ≤ LinearMap.ker ((dStd n).coord 0) := by
    rw [hdRo7DSmNormAux_move_eq_span hφ2 hrf, Submodule.span_le, Set.singleton_subset_iff]
    exact LinearMap.mem_ker.mpr (by rw [hdRo7DSmNormAux_dStd_coord]; exact h0)
  have hfix : r (dStd n 0) = dStd n 0 :=
    hF 3 n (DV n) (dStd n) H A hD r hrH hr hle
  have hstab : ∀ s, DSP 3 (dStd n) s → DSP 3 (dStd n) (r * s * r⁻¹) :=
    hD.hStab r (hD.hHA hrH) hfix
  have hsp : C2SP 3 (dStd n) r := hN 3 rfl n (by have := hD.hn; omega) (DV n) (dStd n) r hstab hfix
  have hspKeep : C2SP 3 (dStd n) r := hsp
  obtain ⟨σ, c, hσ0, hc0, hc, happ⟩ := hsp
  have happ' : ∀ i : Fin (n + 1), r (dE n i) = c i • dE n (σ i) := fun i => by
    simpa only [hdRo7DSmNormAux_dStd_apply] using happ i
  have hexp : h = ∑ j : Fin (n + 1), h j • dE n j := by
    have h1 := (dStd n).sum_repr h
    simpa [dStd, dE, Pi.basisFun_apply] using h1.symm
  have hsum : φ h = ∑ j : Fin (n + 1), h j * φ (dE n j) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  obtain ⟨a, ha, hφa⟩ : ∃ a : Fin (n + 1), h a ≠ 0 ∧ φ (dE n a) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and] at hall
    have hzero : ∑ j : Fin (n + 1), h j * φ (dE n j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : h j = 0
      · rw [hj, zero_mul]
      · by_cases hφj : φ (dE n j) = 0
        · rw [hφj, mul_zero]
        · exfalso; exact hall j hj hφj
    refine hdRo7DSmNormAux_two_ne_zero ?_
    rw [← hφ2, hsum, hzero]
  have ha0 : a ≠ 0 := by
    intro hae
    exact ha (by rw [hae]; exact h0)
  have hsupp : ∀ k : Fin (n + 1), k ≠ a → k ≠ σ a → h k = 0 := by
    intro k hka hks
    have h1 : dE n a - φ (dE n a) • h = c a • dE n (σ a) := by
      rw [← hrf (dE n a), happ' a]
    have h2 : φ (dE n a) • h = dE n a - c a • dE n (σ a) := by
      rw [← h1]
      abel
    have h3 := congrArg (fun v : DV n => v k) h2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hdRo7DSmNormAux_dE_of_ne hka,
      hdRo7DSmNormAux_dE_of_ne hks, mul_zero, sub_zero] at h3
    exact (mul_eq_zero.mp (by simpa using h3)).resolve_left hφa
  have hshape : dIsD h ∨ dIsO h := hdRo7DSmNormAux_shape_of_two hne hsupp
  have hsupp12 : dSupp h = 1 ∨ dSupp h = 2 := hdRo7DSmNormAux_supp_of_shape h0 hshape
  refine ⟨h, h0, hshape, fun ρ hρ => ?_⟩
  have hhh : dB ρ h h ≠ 0 := by
    rw [dB_self_of_eq ρ h0]
    rcases hsupp12 with h1 | h2
    · rw [h1]; decide
    · rw [h2]; decide
  exact dRefl_of_isometry hφ2 hrf (dB_of_c2sp hspKeep ρ) hhh

private lemma hdRo7DSmNormAux_dB_smul_left {n : ℕ} (ρ c : ZMod 3) (x z : DV n) :
    dB ρ (c • x) z = c * dB ρ x z := by
  simp only [dB, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

private lemma hdRo7DSmNormAux_dFun_eq_zero_iff {n : ℕ} {ρ : ZMod 3} {h v : DV n}
    (hh : dB ρ h h ≠ 0) : dFun ρ h v = 0 ↔ dB ρ h v = 0 := by
  rw [dFun_apply]
  constructor
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (mul_ne_zero (by decide) hh)
    · exact h1
  · intro h0
    simp [h0]

private lemma hdRo7DSmNormAux_dual_expand {n : ℕ} (φ : Module.Dual (ZMod 3) (DV n)) (v : DV n) :
    φ v = v 0 * φ (dE n 0) + ∑ i : Fin n, v i.succ * φ (dE n i.succ) := by
  have hexp : v = ∑ j : Fin (n + 1), v j • dE n j := by
    have h1 := (dStd n).sum_repr v
    simpa [dStd, dE, Pi.basisFun_apply] using h1.symm
  have hsum : φ v = ∑ j : Fin (n + 1), v j * φ (dE n j) := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  rw [hsum, Fin.sum_univ_succ]

private lemma hdRo7DSmNormAux_exists_ne_ne {n : ℕ} (hn : 3 ≤ n) (i k : Fin n) :
    ∃ m : Fin n, m ≠ i ∧ m ≠ k := by
  by_contra hc
  push Not at hc
  have h3 : ∀ m : Fin n, m.val = i.val ∨ m.val = k.val := fun m => by
    by_cases hm : m = i
    · exact Or.inl (congrArg Fin.val hm)
    · exact Or.inr (congrArg Fin.val (hc m hm))
  have e0 := h3 ⟨0, by omega⟩
  have e1 := h3 ⟨1, by omega⟩
  have e2 := h3 ⟨2, by omega⟩
  simp only at e0 e1 e2
  omega

private lemma hdRo7DSmNormAux_zeroPair {n : ℕ} {H A : Subgroup (DGL n)}
    (hD : DLinData 3 n (DV n) (dStd n) H A) {r : DGL n} (hrH : r ∈ H) {h : DV n}
    {φ : Module.Dual (ZMod 3) (DV n)} (hφ2 : φ h = 2) (hrf : ∀ v, r v = v - φ v • h)
    {i j : Fin n} (hij : i ≠ j) {ε : ZMod 3} (hε : ε = 1 ∨ ε = -1) :
    φ (dE n i.succ) + ε * φ (dE n j.succ) = 0 ↔ h i.succ + ε * h j.succ = 0 := by
  have hTF : CFSG.StandardType.QTwoLin.TransvectionFree H := fun g hg hgt =>
    hD.hNoT g (hD.hHA hg) (CFSG.StandardType.HdRo7SU.Small.c2Transv_of_isTransvectionLin g hgt)
  have hs1 : i.succ ≠ j.succ := fun he => hij (Fin.succ_inj.mp he)
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> decide
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> decide
  set g : DV n := dE n i.succ + ε • dE n j.succ with hg
  have hgi : g i.succ = 1 := by
    simp [hg, hdRo7DSmNormAux_dE_self, hdRo7DSmNormAux_dE_of_ne hs1]
  have hgj : g j.succ = ε := by
    simp [hg, hdRo7DSmNormAux_dE_self, hdRo7DSmNormAux_dE_of_ne hs1.symm]
  have hgk : ∀ k, k ≠ i.succ → k ≠ j.succ → g k = 0 := by
    intro k hki hkj
    simp [hg, hdRo7DSmNormAux_dE_of_ne hki, hdRo7DSmNormAux_dE_of_ne hkj]
  have hg0 : g 0 = 0 := hgk 0 (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm
  have hgD : dIsD g := ⟨i.succ, j.succ, hs1, by rw [hgi]; decide, by rw [hgj]; exact hε0, hgk⟩
  have hBg : ∀ w : DV n, dB 1 g w = w i.succ + ε * w j.succ := by
    intro w
    rw [hg, hdRo7DSmNormAux_dB_add_left, hdRo7DSmNormAux_dB_smul_left,
      hdRo7DSmNormAux_dB_dE_succ, hdRo7DSmNormAux_dB_dE_succ]
  have hgg : dB 1 g g ≠ 0 := by
    rw [hBg, hgi, hgj, hεε]
    decide
  obtain ⟨s, hs⟩ := exists_dRefl hgg
  have hsH : s ∈ H := hD.hPH s (dsp_of_dRefl_int hs hg0 hgD)
  have hzp := CFSG.StandardType.QTwoLin.zero_pair_iff_of_transvectionFree (K := ZMod 3) hTF
    hrH hsH hφ2 (dFun_self hs.1) hrf (fun v => dRefl_apply hs v)
  rw [hdRo7DSmNormAux_dFun_eq_zero_iff hs.1, hBg] at hzp
  rw [← hzp, hg, map_add, map_smul, smul_eq_mul]

private lemma hdRo7DSmNormAux_fin_triple : ∀ ai ak am xi xk xm : ZMod 3,
    ((ai + ak = 0 ↔ xi + xk = 0) ∧ (ai - ak = 0 ↔ xi - xk = 0)) →
    ((am + ak = 0 ↔ xm + xk = 0) ∧ (am - ak = 0 ↔ xm - xk = 0)) →
    ((ai + am = 0 ↔ xi + xm = 0) ∧ (ai - am = 0 ↔ xi - xm = 0)) →
    xk ≠ 0 → ai = ak * xk * xi ∧ ak ≠ 0 := by
  decide

private lemma hdRo7DSmNormAux_fin_pairZero : ∀ ai aj xi xj : ZMod 3,
    ((ai + aj = 0 ↔ xi + xj = 0) ∧ (ai - aj = 0 ↔ xi - xj = 0)) → xi = 0 → xj = 0 →
    ai = 0 := by
  decide

private lemma hdRo7DSmNormAux_fin_sq : ∀ a x : ZMod 3, x ≠ 0 → a = a * x * x := by decide

private lemma hdRo7DSmNormAux_fin_unit : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by decide

private lemma hdRo7DSmNormAux_fin_axis : ∀ ρ v : ZMod 3, ρ ≠ 0 →
    2 * (ρ * 1) * (ρ * v) = 2 * v := by
  decide

private lemma hdRo7DSmNormAux_fin_ne : ∀ l f s : ZMod 3, l ≠ 0 → f + l * s = 2 →
    l * f + s ≠ 0 := by
  decide

private lemma hdRo7DSmNormAux_fin_final : ∀ l f s v t : ZMod 3, l ≠ 0 → f + l * s = 2 →
    f * v + l * t = 2 * (l * f + s) * (l * f * v + t) := by
  decide

private theorem hdRo7DSmNormAux_caseB1 {n : ℕ} (hN : DNormalizerLeaf)
    {H A : Subgroup (DGL n)} (hD : DLinData 3 n (DV n) (dStd n) H A)
    {r : DGL n} (hrH : r ∈ H) {h : DV n}
    {φ : Module.Dual (ZMod 3) (DV n)} (hφ2 : φ h = 2)
    (hrf : ∀ v, r v = v - φ v • h) (h1 : h 0 = 1) :
    (∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ r (dE n 0)) ∨
      ∃ ρ : ZMod 3, ρ ≠ 0 ∧ ∃ h' : DV n, h' 0 = 1 ∧ dSupp h' ≠ 0 ∧ DRefl ρ r h' := by
  have hn : 6 ≤ n := hD.hn
  have hzp : ∀ i j : Fin n, i ≠ j →
      ((φ (dE n i.succ) + φ (dE n j.succ) = 0 ↔ h i.succ + h j.succ = 0) ∧
        (φ (dE n i.succ) - φ (dE n j.succ) = 0 ↔ h i.succ - h j.succ = 0)) := by
    intro i j hij
    have hp := hdRo7DSmNormAux_zeroPair hD hrH hφ2 hrf hij (Or.inl rfl)
    have hm := hdRo7DSmNormAux_zeroPair hD hrH hφ2 hrf hij (Or.inr rfl)
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at hp hm
    exact ⟨hp, hm⟩
  have hexp := hdRo7DSmNormAux_dual_expand φ
  by_cases hu : ∀ i : Fin n, h i.succ = 0
  ·
    left
    have hh : h = dE n 0 := by
      funext k
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨i, rfl⟩
      · rw [h1, hdRo7DSmNormAux_dE_self]
      · rw [hu i, hdRo7DSmNormAux_dE_of_ne (Fin.succ_ne_zero i)]
    have ha : ∀ i : Fin n, φ (dE n i.succ) = 0 := by
      intro i
      obtain ⟨j, hji, -⟩ := hdRo7DSmNormAux_exists_ne_ne (by omega) i i
      exact hdRo7DSmNormAux_fin_pairZero _ _ _ _ (hzp i j hji.symm) (hu i) (hu j)
    have hφv : ∀ v, φ v = v 0 * φ (dE n 0) := by
      intro v
      rw [hexp v]
      simp [ha]
    have hφ0 : φ (dE n 0) = 2 := by
      rw [← hφ2, hφv h, h1, one_mul]
    intro ρ hρ
    refine ⟨?_, fun v => ?_⟩
    · rw [hdRo7DSmNormAux_dB_dE_zero, hdRo7DSmNormAux_dE_self, mul_one]
      exact hρ
    · rw [hrf v, hφv v, hφ0, hh, dRef, hdRo7DSmNormAux_dB_dE_zero, hdRo7DSmNormAux_dB_dE_zero,
        hdRo7DSmNormAux_dE_self, hdRo7DSmNormAux_fin_axis ρ (v 0) hρ, mul_comm (v 0) 2]
  ·
    right
    push Not at hu
    obtain ⟨k, hk⟩ := hu
    obtain ⟨i₀, hi₀k, -⟩ := hdRo7DSmNormAux_exists_ne_ne (by omega) k k
    obtain ⟨m₀, hm₀i, hm₀k⟩ := hdRo7DSmNormAux_exists_ne_ne (by omega) i₀ k
    have hak : φ (dE n k.succ) ≠ 0 :=
      (hdRo7DSmNormAux_fin_triple _ _ _ _ _ _ (hzp i₀ k hi₀k) (hzp m₀ k hm₀k)
        (hzp i₀ m₀ hm₀i.symm) hk).2
    set l : ZMod 3 := φ (dE n k.succ) * h k.succ with hl
    have hl0 : l ≠ 0 := mul_ne_zero hak hk
    have hlin : ∀ i : Fin n, φ (dE n i.succ) = l * h i.succ := by
      intro i
      by_cases hik : i = k
      · rw [hik, hl]
        exact hdRo7DSmNormAux_fin_sq _ _ hk
      · obtain ⟨m, hmi, hmk⟩ := hdRo7DSmNormAux_exists_ne_ne (by omega) i k
        exact (hdRo7DSmNormAux_fin_triple _ _ _ _ _ _ (hzp i k hik) (hzp m k hmk)
          (hzp i m hmi.symm) hk).1
    have hφv : ∀ v : DV n,
        φ v = φ (dE n 0) * v 0 + l * ∑ i : Fin n, h i.succ * v i.succ := by
      intro v
      rw [hexp v, Finset.mul_sum, mul_comm (v 0)]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hlin i]; ring
    have hf0 : φ (dE n 0) ≠ 0 := by
      intro hf
      have hre : r (dE n 0) = dE n 0 := by
        rw [hrf, hf, zero_smul, sub_zero]
      have hfix : r (dStd n 0) = dStd n 0 := by
        rw [hdRo7DSmNormAux_dStd_apply]
        exact hre
      have hsp : C2SP 3 (dStd n) r :=
        hN 3 rfl n (by omega) (DV n) (dStd n) r (hD.hStab r (hD.hHA hrH) hfix) hfix
      have hB := dB_of_c2sp hsp 1 h (dE n 0)
      have hrh : r h = h - (2 : ZMod 3) • h := by rw [hrf h, hφ2]
      rw [hrh, hre, hdRo7DSmNormAux_dB_dE_zero_right, hdRo7DSmNormAux_dB_dE_zero_right] at hB
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1] at hB
      revert hB
      decide
    have hs : φ (dE n 0) + l * ∑ i : Fin n, h i.succ * h i.succ = 2 := by
      rw [← hφ2, hφv h, h1, mul_one]
    have hBh : ∀ v : DV n, dB (l * φ (dE n 0)) h v =
        l * φ (dE n 0) * v 0 + ∑ i : Fin n, h i.succ * v i.succ := by
      intro v
      rw [dB, h1, mul_one]
    refine ⟨l * φ (dE n 0), mul_ne_zero hl0 hf0, h, h1, ?_, ?_, fun v => ?_⟩
    · rw [dSupp]
      exact Finset.card_ne_zero.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩⟩
    · rw [hBh, h1, mul_one]
      exact hdRo7DSmNormAux_fin_ne _ _ _ hl0 hs
    · rw [hrf v, dRef, hBh, hBh, h1, mul_one, hφv v,
        hdRo7DSmNormAux_fin_final l (φ (dE n 0)) _ (v 0) (∑ i : Fin n, h i.succ * v i.succ) hl0 hs]

private theorem hdRo7DSmNormAux_caseB {n : ℕ} (hN : DNormalizerLeaf)
    {H A : Subgroup (DGL n)} (hD : DLinData 3 n (DV n) (dStd n) H A)
    {r : DGL n} (hrH : r ∈ H) {h : DV n}
    {φ : Module.Dual (ZMod 3) (DV n)} (hφ2 : φ h = 2)
    (hrf : ∀ v, r v = v - φ v • h) (h0 : h 0 ≠ 0) :
    (∀ ρ : ZMod 3, ρ ≠ 0 → DRefl ρ r (dE n 0)) ∨
      ∃ ρ : ZMod 3, ρ ≠ 0 ∧ ∃ h' : DV n, h' 0 = 1 ∧ dSupp h' ≠ 0 ∧ DRefl ρ r h' := by
  rcases hdRo7DSmNormAux_fin_unit (h 0) h0 with h1 | h2
  · exact hdRo7DSmNormAux_caseB1 hN hD hrH hφ2 hrf h1
  · refine hdRo7DSmNormAux_caseB1 hN hD hrH (h := -h) (φ := -φ) ?_ (fun v => ?_) ?_
    · rw [LinearMap.neg_apply, map_neg, neg_neg, hφ2]
    · rw [hrf v, LinearMap.neg_apply, neg_smul_neg]
    · rw [Pi.neg_apply, h2]
      decide

theorem dSmNorm_holds : DSmNormLeaf := by
  intro hN hF n H A hD r hrH hr
  obtain ⟨c, φ, hφc, hr_eq⟩ := (ggLinRefl_iff_isReflLin r).mp hr
  have hrf : ∀ v, r v = v - φ v • c := fun v => by
    rw [hr_eq, Module.reflection_apply]
  by_cases h0 : c 0 = 0
  · obtain ⟨h, hh0, hshape, hdref⟩ := hdRo7DSmNormAux_caseA hN hF hD hrH hr hφc hrf h0
    exact Or.inl ⟨h, hh0, hshape, hdref⟩
  · exact Or.inr (hdRo7DSmNormAux_caseB hN hD hrH hφc hrf h0)

end CFSG.StandardType.HdRo7D.Small
