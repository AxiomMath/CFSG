module

public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardSigma
public import CFSG.RankThree.GF2n.Parrott.SpinTraceData

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.RankThree.GF2n.Parrott.SpinWords
open scoped Matrix


set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s1A" => (⟨sigma1, sigma1_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

@[expose] def spinE2 : V := ![0, 0, 1, 0, 0, 0, 0, 0]

@[expose] def spinGWord : List ℕ := [1, 1, 1, 1, 0, 1, 0]

private def spinSigmaW : List ℕ := [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 2, 1, 2, 1]

private def spinS1W : List ℕ := [1, 0, 1, 2, 1, 1, 2, 1, 0, 1, 0, 1, 1]

private def spinUVW : List ℕ := [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 2, 1, 1, 1, 1]

private def spinTUVW : List ℕ := [1, 1, 0, 1, 1, 2, 1, 0, 1, 0, 1, 0, 1, 0, 1]

private def spinTW : List ℕ := [0]

private theorem spinSigmaW_eq : s1A * s2A⁻¹ = wordElem spinSigmaW := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_wordElem]
  show sigma1 * sigma2⁻¹ = wordPerm spinSigmaW
  decide +kernel

private theorem spinS1W_eq : s1A = wordElem spinS1W := by
  apply Subtype.ext
  rw [coe_wordElem]
  show sigma1 = wordPerm spinS1W
  decide +kernel

private theorem spinUVW_eq : uA * vA = wordElem spinUVW := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_wordElem]
  show u * v = wordPerm spinUVW
  decide +kernel

private theorem spinTUVW_eq : tA * (uA * vA) = wordElem spinTUVW := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_wordElem]
  show x45 * (u * v) = wordPerm spinTUVW
  decide +kernel

private theorem spinTW_eq : tA = wordElem spinTW := by
  apply Subtype.ext
  rw [coe_wordElem]
  show x45 = wordPerm spinTW
  decide +kernel

private def spinFVec : Fin 16 → V :=
  ![![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0, 0],
    ![0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0, 1, 1],
    ![1, 0, 0, 1, 1, 0, 1, 1],
    ![1, 0, 1, 0, 1, 0, 1, 1],
    ![1, 0, 1, 1, 1, 0, 1, 1],
    ![1, 1, 0, 0, 0, 0, 1, 1],
    ![1, 1, 0, 1, 0, 0, 1, 1],
    ![1, 1, 1, 0, 0, 0, 1, 1],
    ![1, 1, 1, 1, 0, 0, 1, 1]]

private theorem spin_fixed_sigma_iff (w : V) :
    ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w ↔ ∃ i : Fin 16, spinFVec i = w := by
  revert w
  rw [spinSigmaW_eq, rhoA_wordElem]
  decide +kernel

private theorem spin_triple_check (i₁ i₂ j : Fin 16)
    (hq₁ : q (spinFVec i₁) = 0) (hq₂ : q (spinFVec i₂) = 0)
    (hq : q (spinFVec j) = 0)
    (hb₁₂ : b (spinFVec i₁) (spinFVec i₂) = 0)
    (hb₁ : b (spinFVec i₁) (spinFVec j) = 0)
    (hb₂ : b (spinFVec i₂) (spinFVec j) = 0)
    (h₁ : spinFVec i₁ ≠ 0) (h₂ : spinFVec i₂ ≠ 0) (h₁₂ : spinFVec i₁ ≠ spinFVec i₂) :
    spinFVec j = 0 ∨ spinFVec j = spinFVec i₁ ∨ spinFVec j = spinFVec i₂ ∨
      spinFVec j = spinFVec i₁ + spinFVec i₂ := by
  decide +kernel +revert

private theorem spin_g_cover_check (i : Fin 16) (hq : q (spinFVec i) = 0) :
    wordMat spinTW *ᵥ spinFVec i = spinFVec i ∨
      wordMat spinTW *ᵥ (wordMat spinGWord *ᵥ spinFVec i) =
        wordMat spinGWord *ᵥ spinFVec i ∨
      wordMat spinTW *ᵥ ((wordMat spinGWord * wordMat spinGWord) *ᵥ spinFVec i) =
        (wordMat spinGWord * wordMat spinGWord) *ᵥ spinFVec i := by
  decide +kernel +revert

theorem spin_fixed_sigma_t_iff (w : V) :
    (((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w ∧ ((rhoA tA : GL8) : Mat8) *ᵥ w = w) ↔
      w = 0 ∨ w = spinE2 ∨ w = spinW0 ∨ w = spinE2 + spinW0 := by
  rw [spinSigmaW_eq, rhoA_wordElem, spinTW_eq, rhoA_wordElem]
  revert w
  decide +kernel

theorem spin_q_eq_zero_of_fixed_sigma_t {w : V}
    (hs : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w)
    (ht : ((rhoA tA : GL8) : Mat8) *ᵥ w = w) :
    q w = 0 := by
  rcases (spin_fixed_sigma_t_iff w).1 ⟨hs, ht⟩ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem spin_trace_sigma1_of_fixed_sigma_t {w : V}
    (hs : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w)
    (ht : ((rhoA tA : GL8) : Mat8) *ᵥ w = w) :
    w + ((rhoA s1A : GL8) : Mat8) *ᵥ w +
      ((rhoA s1A : GL8) : Mat8) *ᵥ (((rhoA s1A : GL8) : Mat8) *ᵥ w) = 0 := by
  rw [spinS1W_eq, rhoA_wordElem]
  rcases (spin_fixed_sigma_t_iff w).1 ⟨hs, ht⟩ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem spin_fixed_t_of_fixed_sigma_of_b {w : V}
    (hs : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w)
    (h₁ : b spinE2 w = 0) (h₂ : b spinW0 w = 0) :
    ((rhoA tA : GL8) : Mat8) *ᵥ w = w := by
  rw [spinTW_eq, rhoA_wordElem]
  revert w
  rw [spinSigmaW_eq, rhoA_wordElem]
  decide +kernel

theorem spin_eq_of_singular_fixed_sigma {v₁ v₂ w : V}
    (hv₁ : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ v₁ = v₁)
    (hv₂ : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ v₂ = v₂)
    (hw : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w)
    (hq₁ : q v₁ = 0) (hq₂ : q v₂ = 0) (hq : q w = 0)
    (hb₁₂ : b v₁ v₂ = 0) (hb₁ : b v₁ w = 0) (hb₂ : b v₂ w = 0)
    (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (h₁₂ : v₁ ≠ v₂) :
    w = 0 ∨ w = v₁ ∨ w = v₂ ∨ w = v₁ + v₂ := by
  obtain ⟨i₁, rfl⟩ := (spin_fixed_sigma_iff v₁).1 hv₁
  obtain ⟨i₂, rfl⟩ := (spin_fixed_sigma_iff v₂).1 hv₂
  obtain ⟨j, rfl⟩ := (spin_fixed_sigma_iff w).1 hw
  exact spin_triple_check i₁ i₂ j hq₁ hq₂ hq hb₁₂ hb₁ hb₂ h₁ h₂ h₁₂

theorem spin_card_fixed_sigma_uv :
    (Finset.univ.filter fun w : V =>
      ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w ∧
        ((rhoA (uA * vA) : GL8) : Mat8) *ᵥ w = w).card = 4 := by
  rw [spinSigmaW_eq, rhoA_wordElem, spinUVW_eq, rhoA_wordElem]
  decide +kernel

theorem spin_card_fixed_sigma_t_uv :
    (Finset.univ.filter fun w : V =>
      ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w ∧
        ((rhoA (tA * (uA * vA)) : GL8) : Mat8) *ᵥ w = w).card = 4 := by
  rw [spinSigmaW_eq, rhoA_wordElem, spinTUVW_eq, rhoA_wordElem]
  decide +kernel

theorem spin_card_fixed_sigma_uv_t :
    (Finset.univ.filter fun w : V =>
      ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w ∧
        ((rhoA (uA * vA) : GL8) : Mat8) *ᵥ w = w ∧
          ((rhoA tA : GL8) : Mat8) *ᵥ w = w).card = 2 := by
  rw [spinSigmaW_eq, rhoA_wordElem, spinUVW_eq, rhoA_wordElem, spinTW_eq, rhoA_wordElem]
  decide +kernel

theorem wordElem_spinGWord_comm :
    wordElem spinGWord * (s1A * s2A⁻¹) = (s1A * s2A⁻¹) * wordElem spinGWord := by
  apply Subtype.ext
  rw [spinSigmaW_eq]
  simp only [Subgroup.coe_mul, coe_wordElem]
  show wordPerm spinGWord * wordPerm spinSigmaW = wordPerm spinSigmaW * wordPerm spinGWord
  decide +kernel

theorem spin_fixed_t_or_of_singular_fixed_sigma {w : V}
    (hs : ((rhoA (s1A * s2A⁻¹) : GL8) : Mat8) *ᵥ w = w) (hq : q w = 0) :
    ((rhoA tA : GL8) : Mat8) *ᵥ w = w ∨
      ((rhoA tA : GL8) : Mat8) *ᵥ (((rhoA (wordElem spinGWord) : GL8) : Mat8) *ᵥ w) =
        ((rhoA (wordElem spinGWord) : GL8) : Mat8) *ᵥ w ∨
      ((rhoA tA : GL8) : Mat8) *ᵥ
          (((rhoA (wordElem spinGWord * wordElem spinGWord) : GL8) : Mat8) *ᵥ w) =
        ((rhoA (wordElem spinGWord * wordElem spinGWord) : GL8) : Mat8) *ᵥ w := by
  obtain ⟨i, rfl⟩ := (spin_fixed_sigma_iff w).1 hs
  rw [spinTW_eq, rhoA_wordElem]
  rw [map_mul, Units.val_mul, rhoA_wordElem]
  exact spin_g_cover_check i hq

end CFSG.RankThree.GF2n.Parrott
