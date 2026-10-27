module

public import CFSG.Quasithin.H13.GoldschmidtU43CRel
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LieType.Multipliers.U43Action

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.LieType.Multipliers.U43 (X₀)

@[expose] def jwA₂ {K : Type} [Group K] (a₁ u : K) : K := u⁻¹ * a₁ * u

@[expose] def jwS₂ {K : Type} [Group K] (σ₁ u : K) : K := u⁻¹ * σ₁ * u

@[expose] def jwP₂ {K : Type} [Group K] (v φ : K) : K := v⁻¹ * φ * v

@[expose] def jwP₃ {K : Type} [Group K] (a₁ u φ : K) : K :=
  (jwA₂ a₁ u)⁻¹ * φ * jwA₂ a₁ u

@[expose] def jwP₄ {K : Type} [Group K] (a₁ u v φ : K) : K :=
  (jwA₂ a₁ u)⁻¹ * jwP₂ v φ * jwA₂ a₁ u

structure JW20 {K : Type} [Group K] (a₁ σ₁ u v φ : K) : Prop extends JW13 a₁ σ₁ u v where
  r14 : (a₁ ^ 2)⁻¹ * φ * a₁ ^ 2 = φ⁻¹
  r15 : u⁻¹ * φ * u = φ
  r16 : (jwS₂ σ₁ u)⁻¹ * jwP₃ a₁ u φ * jwS₂ σ₁ u = φ⁻¹ * jwP₃ a₁ u φ * σ₁
  r17 : (jwP₃ a₁ u φ)⁻¹ * φ * jwP₃ a₁ u φ = φ * σ₁⁻¹
  r18 : φ⁻¹ * (jwP₄ a₁ u v φ)⁻¹ * φ * jwP₄ a₁ u v φ = 1
  r19 : (u * a₁ ^ 2 * jwP₃ a₁ u φ) ^ 3 = 1
  r20 : (u * v * (jwP₃ a₁ u φ)⁻¹ * jwP₄ a₁ u v φ) ^ 3 = 1

@[expose] def U43Model : Prop :=
  ∃ a s u v φ : X₀, JW20 a s u v φ ∧ Subgroup.closure ({a, s, u, v, φ} : Set X₀) = ⊤

end CFSG.Quasithin.H13.U43
