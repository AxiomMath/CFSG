module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.SzN27.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj uElt_zero_eq_one exists_ne_zero_ne)
open Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem comm_pair (α b₁ c₁ b₂ c₂ δ : K) :
    uElt α b₁ c₁ 0 * uElt 0 b₂ c₂ δ * (uElt α b₁ c₁ 0)⁻¹ * (uElt 0 b₂ c₂ δ)⁻¹ =
      uElt 0 (α * δ) (α ^ 2 * δ) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
  congr 1
  · linear_combination α * h2
  · linear_combination (α * δ + b₁ + b₂) * h2
  · linear_combination (α * b₁ + 2 * α * b₂ + c₁ + c₂) * h2
  · linear_combination δ * h2

theorem mul_center (p q p' q' : K) :
    uElt 0 p q 0 * uElt 0 p' q' 0 = uElt 0 (p + p') (q + q') 0 := by
  rw [uElt_mul]
  congr 1 <;> ring

theorem inv_mul_mem_center (a b₁ c₁ b c d : K) :
    ∃ b' c' : K, (uElt a b₁ c₁ d)⁻¹ * uElt a b c d = uElt 0 b' c' 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨b₁ + a * d + b + a * d, c₁ + c + a * b + a * a * d + (b₁ + a * d) * a, ?_⟩
  rw [uElt_inv, uElt_mul]
  congr 1
  · linear_combination a * h2
  · linear_combination d * h2

theorem U_le_of_coords (hK : 4 ≤ Nat.card K) {H : Subgroup (antiSp K)}
    (hα : ∀ α : K, ∃ B C : K, uElt α B C 0 ∈ H) (hδ : ∀ δ : K, ∃ B C : K, uElt 0 B C δ ∈ H) :
    antiUnipotent K ≤ H := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hz : ∀ α δ : K, uElt 0 (α * δ) (α ^ 2 * δ) 0 ∈ H := by
    intro α δ
    obtain ⟨B₁, C₁, h₁⟩ := hα α
    obtain ⟨B₂, C₂, h₂⟩ := hδ δ
    rw [← comm_pair α B₁ C₁ B₂ C₂ δ]
    exact H.mul_mem (H.mul_mem (H.mul_mem h₁ h₂) (H.inv_mem h₁)) (H.inv_mem h₂)
  obtain ⟨s₀, hs₀, hs₁⟩ := exists_ne_zero_ne (K := K) (by omega) 1
  have hs₀' : s₀ + 1 ≠ 0 := by
    intro h
    apply hs₁
    linear_combination -h + h2
  have hc : ∀ c : K, uElt 0 0 c 0 ∈ H := by
    intro c
    set δ : K := c / (s₀ * (s₀ + 1)) with hδdef
    have hδ' : s₀ * (s₀ + 1) * δ = c := by
      rw [hδdef]
      field_simp
    have h₁ := hz s₀ δ
    have h₂ := hz 1 (s₀ * δ)
    have := H.mul_mem h₁ h₂
    rw [mul_center] at this
    convert this using 2
    · linear_combination (-(s₀ * δ)) * h2
    · linear_combination (-1 : K) * hδ'
  have hb : ∀ p : K, uElt 0 p 0 0 ∈ H := by
    intro p
    have h₁ := hz 1 p
    have h₂ := hc p
    have := H.mul_mem h₁ h₂
    rw [mul_center] at this
    convert this using 2
    · ring
    · linear_combination (-p) * h2
  have hZ : ∀ p q : K, uElt 0 p q 0 ∈ H := by
    intro p q
    have := H.mul_mem (hb p) (hc q)
    rw [mul_center] at this
    convert this using 2 <;> ring
  rintro _ ⟨a, b, c, d, rfl⟩
  obtain ⟨B₁, C₁, h₁⟩ := hα a
  obtain ⟨B₂, C₂, h₂⟩ := hδ d
  have hw := H.mul_mem h₁ h₂
  have hwe : uElt a B₁ C₁ 0 * uElt 0 B₂ C₂ d = uElt a (B₁ + B₂ + a * d) (C₁ + C₂ + a * B₂) d := by
    rw [uElt_mul]
    congr 1 <;> ring
  rw [hwe] at hw
  obtain ⟨b', c', hbc⟩ := inv_mul_mem_center a (B₁ + B₂ + a * d) (C₁ + C₂ + a * B₂) b c d
  have : uElt a b c d = uElt a (B₁ + B₂ + a * d) (C₁ + C₂ + a * B₂) d * uElt 0 b' c' 0 := by
    rw [← hbc]
    group
  rw [this]
  exact H.mul_mem hw (hZ b' c')

end CFSG.Quasithin.SzN27.Sp4
