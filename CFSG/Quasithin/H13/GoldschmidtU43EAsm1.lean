module

public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.GoldschmidtU43EMat2
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm5
public import CFSG.Quasithin.H13.GoldschmidtU43ModDef
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6
open CFSG.LieType.Multipliers.U43 (X₀)

structure JWClose {K : Type} [Group K] (a₁ σ₁ u v φ : K) : Prop where
  r16 : (jwS₂ σ₁ u)⁻¹ * jwP₃ a₁ u φ * jwS₂ σ₁ u = φ⁻¹ * jwP₃ a₁ u φ * σ₁
  r17 : (jwP₃ a₁ u φ)⁻¹ * φ * jwP₃ a₁ u φ = φ * σ₁⁻¹
  r18 : φ⁻¹ * (jwP₄ a₁ u v φ)⁻¹ * φ * jwP₄ a₁ u v φ = 1
  r19 : (u * a₁ ^ 2 * jwP₃ a₁ u φ) ^ 3 = 1
  r20 : (u * v * (jwP₃ a₁ u φ)⁻¹ * jwP₄ a₁ u v φ) ^ 3 = 1

theorem JW20.of_close {K : Type} [Group K] {a₁ σ₁ u v φ : K} (h13 : JW13 a₁ σ₁ u v)
    (h14 : (a₁ ^ 2)⁻¹ * φ * a₁ ^ 2 = φ⁻¹) (h15 : u⁻¹ * φ * u = φ) (hc : JWClose a₁ σ₁ u v φ) :
    JW20 a₁ σ₁ u v φ where
  toJW13 := h13
  r14 := h14
  r15 := h15
  r16 := hc.r16
  r17 := hc.r17
  r18 := hc.r18
  r19 := hc.r19
  r20 := hc.r20

@[expose] def U43Closing : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : JWSetup z), (S.A : G) ∈ Uz z →
    Nonempty (S.Nbar ≃* alternatingGroup (Fin 6)) → ∀ r : S.Rho,
      JWClose (S.A : G) (S.σ₁ : G) (S.u : G) (S.v : G) r.ρ

end CFSG.Quasithin.H13.U43
