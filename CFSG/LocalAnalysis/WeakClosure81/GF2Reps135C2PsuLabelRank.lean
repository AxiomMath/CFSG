module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Binary
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.FieldDegree
import CFSG.LieType.SpecialLinear.ExteriorModel.WeightDim

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Finset Module
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

private theorem w135c2_mul_pred_le_orbitSize {n : ℕ} {S : Finset (Fin n)} (hn : 2 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (h2 : 2 ≤ S.card) : n * (n - 1) ≤ orbitSize S := by
  classical
  have hn0 : 0 < n := by omega
  rw [orbitSize, card_rearr_topWt]
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  exact multinomial_lower (b := blocks S) hb hsum hl

private theorem w135c2_two_mul_of_selfDual_singleton {n : ℕ} (j : Fin n) (hj0 : (j : ℕ) ≠ 0)
    (hsd : ({j} : Finset (Fin n)).image labelStar = {j}) : n = 2 * (j : ℕ) := by
  rw [Finset.image_singleton, Finset.singleton_inj] at hsd
  have h1 := congrArg Fin.val hsd
  rw [labelStar_eq_of_ne_zero hj0] at h1
  simp only [Fin.val_mk] at h1
  have := j.isLt
  omega

private theorem w135c2_labelStar_ne_of_natural {n : ℕ} (hn : 3 ≤ n) (j : Fin n)
    (hj : (j : ℕ) = 1 ∨ (j : ℕ) + 1 = n) : labelStar j ≠ j := by
  have hj0 : (j : ℕ) ≠ 0 := by omega
  intro h
  have h1 := congrArg Fin.val h
  rw [labelStar_eq_of_ne_zero hj0] at h1
  simp only [Fin.val_mk] at h1
  omega

private theorem w135c2_two_le_card_of_selfDual_three (S : Finset (Fin 3))
    (h0 : (⟨0, by omega⟩ : Fin 3) ∉ S) (hne : S ≠ ∅)
    (hsd : S.image labelStar = S) : 2 ≤ S.card := by
  by_contra hlt
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  have hcard1 : S.card = 1 := by omega
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard1
  have hsdj : ({j} : Finset (Fin 3)).image labelStar = {j} := hsd
  have hj0 : (j : ℕ) ≠ 0 := by
    intro hh
    apply h0
    rw [Finset.mem_singleton]
    exact Fin.ext hh.symm
  have := w135c2_two_mul_of_selfDual_singleton j hj0 hsdj
  omega

theorem w135c2_psu_label_gt_six {n f s : ℕ} (hn : 3 ≤ n) (hn4 : n ≠ 4)
    (hnf : ¬ (n = 3 ∧ f = 1)) (hs : 1 ≤ s) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) (hact : ∃ r, ε r ≠ ∅)
    (hper : f ≤ s * (univ.filter fun r => ε r ≠ ∅).card)
    (hns : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 →
      (∃ r, (ε r).image labelStar ≠ ε r) → 2 * f ≤ s)
    {k : Type} [Field k] [CharP k 2] : 6 < s * finrank k (BModel k ε) := by
  classical
  have hn2 : 2 ≤ n := by omega
  set T : Finset (Fin f) := univ.filter (fun r => ε r ≠ ∅) with hT
  have hmemT : ∀ r, r ∈ T ↔ ε r ≠ ∅ := by
    intro r
    rw [hT]
    simp
  obtain ⟨r₁, hr₁⟩ := hact
  have hTpos : 0 < T.card := Finset.card_pos.mpr ⟨r₁, (hmemT r₁).mpr hr₁⟩
  have hN : ∀ r ∈ T, n ≤ orbitSize (ε r) := fun r hr =>
    n_le_orbitSize hn2 (h0 r) ((hmemT r).mp hr)
  have hP : ∏ r ∈ T, orbitSize (ε r) ≤ finrank k (BModel k ε) := by
    rw [hT]
    exact prod_orbitSize_le_finrank ε
  have hD : n ^ T.card ≤ finrank k (BModel k ε) :=
    (Finset.pow_card_le_prod T (fun r => orbitSize (ε r)) n hN).trans hP
  by_cases h2 : 2 ≤ T.card
  ·
    have hp : n ^ 2 ≤ n ^ T.card := Nat.pow_le_pow_right (by omega) h2
    have hn9 : 9 ≤ n ^ 2 := by
      have hm := Nat.mul_le_mul hn hn
      norm_num at hm
      simpa [sq] using hm
    have h9 : 9 ≤ finrank k (BModel k ε) := hn9.trans (hp.trans hD)
    calc 6 < 9 := by norm_num
      _ ≤ finrank k (BModel k ε) := h9
      _ = 1 * finrank k (BModel k ε) := (one_mul _).symm
      _ ≤ s * finrank k (BModel k ε) := Nat.mul_le_mul_right _ hs
  ·
    have hT1 : T.card = 1 := by omega
    obtain ⟨r₀, hTr₀⟩ := Finset.card_eq_one.mp hT1
    have hr₀T : r₀ ∈ T := by rw [hTr₀]; exact Finset.mem_singleton_self r₀
    have hr₀ : ε r₀ ≠ ∅ := (hmemT r₀).mp hr₀T
    have hone : ∀ r, r ≠ r₀ → ε r = ∅ := by
      intro r hr
      by_contra hne
      have hrT : r ∈ T := (hmemT r).mpr hne
      rw [hTr₀, Finset.mem_singleton] at hrT
      exact hr hrT
    have hprod : ∏ r ∈ T, orbitSize (ε r) = orbitSize (ε r₀) := by
      rw [hTr₀, Finset.prod_singleton]
    have hDn : n ≤ finrank k (BModel k ε) := (hN r₀ hr₀T).trans (hprod ▸ hP)
    have horb : orbitSize (ε r₀) ≤ finrank k (BModel k ε) := hprod ▸ hP
    have hfpos : 1 ≤ f := by have := r₀.isLt; omega
    have hsf : f ≤ s := by
      have h1 : f ≤ s * T.card := hper
      rw [hT1, mul_one] at h1
      exact h1
    by_cases hn7 : 7 ≤ n
    · have hD7 : 7 ≤ finrank k (BModel k ε) := hn7.trans hDn
      calc 6 < 7 := by norm_num
        _ ≤ finrank k (BModel k ε) := hD7
        _ = 1 * finrank k (BModel k ε) := (one_mul _).symm
        _ ≤ s * finrank k (BModel k ε) := Nat.mul_le_mul_right _ hs
    · have hn6 : n ≤ 6 := by omega
      by_cases hnsd : ∃ r, (ε r).image labelStar ≠ ε r
      ·
        have hcard2 : (univ.filter fun r => ε r ≠ ∅).card ≤ 2 := by
          rw [← hT]
          omega
        have h2f : 2 * f ≤ s := hns hcard2 hnsd
        have h6 : 6 < 2 * f * n := by
          rcases (by omega : n = 3 ∨ n = 5 ∨ n = 6) with h3 | h5 | h6n
          · subst h3
            have hf2 : 2 ≤ f := by
              by_contra hlt
              exact hnf ⟨rfl, by omega⟩
            have he : 2 * f * 3 = 6 * f := by ring
            rw [he]
            nlinarith
          · subst h5
            have h10 : 10 ≤ 2 * f * 5 := by
              have h1 : 2 * 1 * 5 ≤ 2 * f * 5 := by gcongr <;> omega
              norm_num at h1
              exact h1
            omega
          · subst h6n
            have h10 : 10 ≤ 2 * f * 6 := by
              have h1 : 2 * 1 * 5 ≤ 2 * f * 6 := by gcongr <;> omega
              norm_num at h1
              exact h1
            omega
        have h2fn : 2 * f * n ≤ s * finrank k (BModel k ε) := Nat.mul_le_mul h2f hDn
        omega
      ·
        have hsdall : ∀ r, (ε r).image labelStar = ε r := by
          intro r
          by_contra h
          exact hnsd ⟨r, h⟩
        rcases (by omega : n = 3 ∨ 5 ≤ n) with h3 | hn5
        ·
          subst h3
          have hcard2 : 2 ≤ (ε r₀).card :=
            w135c2_two_le_card_of_selfDual_three (ε r₀) (h0 r₀) hr₀ (hsdall r₀)
          have ho6 : 6 ≤ orbitSize (ε r₀) := by
            have h := w135c2_mul_pred_le_orbitSize (n := 3) (S := ε r₀)
              (by omega) (h0 r₀) hcard2
            have h' : 6 = 3 * (3 - 1) := by norm_num
            rw [h']
            exact h
          have hD6 : 6 ≤ finrank k (BModel k ε) := ho6.trans horb
          have hs2 : 2 ≤ s := by
            have hf2 : 2 ≤ f := by
              by_contra hlt
              exact hnf ⟨rfl, by omega⟩
            omega
          calc 6 < 2 * 6 := by norm_num
            _ ≤ s * finrank k (BModel k ε) := Nat.mul_le_mul hs2 hD6
        ·
          have hnon : ¬ (ε r₀ = {⟨1, by omega⟩} ∨
              ε r₀ = {⟨n - 1, by omega⟩}) := by
            rintro (h | h)
            · have hsd0 := hsdall r₀
              rw [h, Finset.image_singleton, Finset.singleton_inj] at hsd0
              exact w135c2_labelStar_ne_of_natural (by omega) _ (Or.inl rfl) hsd0
            · have hsd0 := hsdall r₀
              rw [h, Finset.image_singleton, Finset.singleton_inj] at hsd0
              exact w135c2_labelStar_ne_of_natural (by omega) _
                (Or.inr (by simp only [Fin.val_mk]; omega)) hsd0
          have hbig : n.choose 2 ≤ orbitSize (ε r₀) :=
            choose_two_le_orbitSize_of_nonnatural hn5 (h0 r₀) hr₀ hnon
          have h10choose : 10 ≤ n.choose 2 := by
            have h2c : 2 * n.choose 2 = n * (n - 1) := two_mul_choose_two n
            have hn20 : 20 ≤ n * (n - 1) := by
              have h4 : 4 ≤ n - 1 := by omega
              calc 20 = 5 * 4 := by norm_num
                _ ≤ n * (n - 1) := Nat.mul_le_mul hn5 h4
            omega
          have hD10 : 10 ≤ finrank k (BModel k ε) :=
            (h10choose.trans hbig).trans horb
          calc 6 < 10 := by norm_num
            _ ≤ finrank k (BModel k ε) := hD10
            _ = 1 * finrank k (BModel k ε) := (one_mul _).symm
            _ ≤ s * finrank k (BModel k ε) := Nat.mul_le_mul_right _ hs

end CFSG.LocalAnalysis.WeakClosure81
