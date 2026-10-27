module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.SEITZ5.UFrame

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

section Setup

variable [CharP K 2] {e w v : Fin n → K}

@[expose] noncomputable def frameOf (hσ : ∀ c, σ (σ c) = c) (he : herm σ e e = 0)
    (hw : herm σ w w = 0) (hv : herm σ v v = 0) (hew : herm σ e w = 0) (hβ : herm σ e v ≠ 0) :
    Frame σ n where
  e := e
  u := (herm σ e v)⁻¹ • v
  z := σ (herm σ w v) • e + σ (herm σ e v) • w
  he := he
  hu := by simp [herm_smul_left, herm_smul_right, hv]
  hz := by
    have hwe : herm σ w e = 0 := herm_eq_zero_comm σ hσ hew
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, he, hw, hew, hwe]
  heu := by rw [herm_smul_right, inv_mul_cancel₀ hβ]
  hez := by simp [herm_add_right, herm_smul_right, he, hew]
  huz := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have h1 : herm σ v e = σ (herm σ e v) := herm_conj σ hσ e v
    have h3 : herm σ v w = σ (herm σ w v) := herm_conj σ hσ w v
    have hσβ : σ (herm σ e v) ≠ 0 := (map_ne_zero σ).2 hβ
    simp only [herm_smul_left, herm_add_right, herm_smul_right, h1, h3, map_inv₀]
    field_simp
    linear_combination (σ (herm σ w v)) * h2

end Setup

section Generic

variable (P : Frame σ n)

theorem aff_tv_e {t : SUid σ n} {c : fixSub σ}
    (ht : IsTv σ t P.e (c : K)) : Aff P t (u2 c) 0 0 := by
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) c
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, P.hez, mul_zero, zero_smul, add_zero]
  · rw [ht, P.he, h00, h10]
    simp
  · rw [ht, P.heu, h01, h11]
    simp [add_comm]

theorem aff_tv_u (hσ : ∀ c, σ (σ c) = c) {t : SUid σ n} {c : fixSub σ}
    (ht : IsTv σ t P.u (c : K)) : Aff P t (l2 c) 0 0 := by
  obtain ⟨h00, h01, h10, h11⟩ := ent_l2 (σ := σ) c
  have hue := P.hue hσ
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, P.huz, mul_zero, zero_smul, add_zero]
  · rw [ht, hue, h00, h10]
    simp
  · rw [ht, P.hu, h01, h11]
    simp

theorem triv_tv_e {t : SUid σ n} {c : K} (ht : IsTv σ t P.e c) : Triv P t := by
  intro y h1 _ _
  rw [ht, h1, mul_zero, zero_smul, add_zero]

theorem triv_tv_u {t : SUid σ n} {c : K} (ht : IsTv σ t P.u c) : Triv P t := by
  intro y _ h2 _
  rw [ht, h2, mul_zero, zero_smul, add_zero]

theorem aff_tv_w {w : Fin n → K} {ζ ρ : K} {γ : fixSub σ} (hγ : (γ : K) = σ ρ * ρ)
    (hwe : herm σ w P.e = 0) (hwz : herm σ w P.z = 0) (hwu : herm σ w P.u = ρ)
    (hw : w = ζ • P.z + σ ρ • P.e) {t : SUid σ n} (ht : IsTv σ t w 1) :
    Aff P t (u2 γ) 0 (ρ * ζ) := by
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) γ
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, hwz, mul_zero, zero_smul, add_zero]
  · rw [ht, hwe, h00, h10]
    simp
  · rw [ht, hwu, h01, h11, hγ]
    nth_rewrite 1 [hw]
    module

theorem triv_tv_w {w : Fin n → K} {ζ ρ : K} (hw : w = ζ • P.z + σ ρ • P.e) {t : SUid σ n}
    {c : K} (ht : IsTv σ t w c) : Triv P t := by
  intro y h1 _ h3
  have : herm σ w y = 0 := by
    rw [hw, herm_add_left, herm_smul_left, herm_smul_left, h3, h1]
    simp
  rw [ht, this, mul_zero, zero_smul, add_zero]

theorem aff_siegel {w : Fin n → K} {ζ ρ μ : K} {τ : fixSub σ}
    (hτ : (τ : K) = μ * σ ρ + σ μ * ρ) (hwe : herm σ w P.e = 0) (hwz : herm σ w P.z = 0)
    (hwu : herm σ w P.u = ρ) (hw : w = ζ • P.z + σ ρ • P.e) {t : SUid σ n}
    (ht : ∀ x, t • x = x + (μ * herm σ P.e x) • w + (σ μ * herm σ w x) • P.e) :
    Aff P t (u2 τ) 0 (μ * ζ) := by
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) τ
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, P.hez, hwz]
    simp
  · rw [ht, P.he, hwe, h00, h10]
    simp
  · rw [ht, P.heu, hwu, h01, h11, hτ]
    nth_rewrite 1 [hw]
    module

theorem triv_siegel {w : Fin n → K} {ζ ρ μ : K} (hw : w = ζ • P.z + σ ρ • P.e) {t : SUid σ n}
    (ht : ∀ x, t • x = x + (μ * herm σ P.e x) • w + (σ μ * herm σ w x) • P.e) : Triv P t := by
  intro y h1 _ h3
  have : herm σ w y = 0 := by
    rw [hw, herm_add_left, herm_smul_left, herm_smul_left, h3, h1]
    simp
  rw [ht, this, h1]
  simp

end Generic

end CFSG.RankThree.PartOne.SEITZ5
