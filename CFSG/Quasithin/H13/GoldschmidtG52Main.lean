module

public import CFSG.Quasithin.H13.GoldschmidtG52Sec
public import CFSG.Quasithin.H13.GoldschmidtG52Module

public section

namespace CFSG.Quasithin.H13.A6.G52

open Subgroup CFSG CFSG.ABGLocalTools
open scoped IsMulCommutative

theorem stmtG52_holds : StmtG52 := by
  intro X _ _ A B Y ρ hBA hAB hsq hcomm hYA hYB hsurj hker hlt hirr hW₁ hW₂
  obtain ⟨W₁, hBW₁, hW₁A, hW₁4, hW₁N⟩ := hW₁
  obtain ⟨W₂, hBW₂, hW₂A, hW₂4, hW₂N⟩ := hW₂
  have hch : IsChiefFactorUnder 2 Y A B := isChiefFactorUnder_two hAB hsq hcomm hYA hYB hlt hirr
  have : (B.subgroupOf A).Normal := hch.normal
  have : IsElementaryAbelian 2 (↥A ⧸ B.subgroupOf A) := hch.isElementaryAbelian
  have hτ := sRep_isIrreducible hch ρ hsurj hker
  have : Finite (Additive (↥A ⧸ B.subgroupOf A)) := inferInstance
  have : FiniteDimensional (ZMod 2) (Additive (↥A ⧸ B.subgroupOf A)) := Module.Finite.of_finite
  have h₁ : Nat.card (subm (imgSub A B W₁)) = 4 := by
    rw [natCard_subm, natCard_imgSub hW₁A, hW₁4]
  have h₂ : Nat.card (subm (imgSub A B W₂)) = 4 := by
    rw [natCard_subm, natCard_imgSub hW₂A, hW₂4]
  have hL₁ : ∀ g ∈ g5G1, ∀ v ∈ subm (imgSub A B W₁), sRep hch ρ hsurj hker g v ∈
      subm (imgSub A B W₁) := by
    intro g hg v hv
    obtain ⟨y, rfl⟩ := hsurj g
    rw [sRep_apply]
    exact yRep_mem_subm_imgSub hch y (hW₁N y hg) hv
  have hL₂ : ∀ g ∈ cA6, ∀ v ∈ subm (imgSub A B W₂), sRep hch ρ hsurj hker g v ∈
      subm (imgSub A B W₂) := by
    intro g hg v hv
    obtain ⟨y, rfl⟩ := hsurj g
    rw [sRep_apply]
    exact yRep_mem_subm_imgSub hch y (hW₂N y hg) hv
  obtain ⟨e⟩ := equiv_Mrep_three _ hτ _ _ h₁ h₂ hL₁ hL₂
  refine ⟨?_, fun y hy => ?_, fun y h3 h1 => ?_⟩
  · rw [relIndex_eq_natCard]
    exact natCard_eq_two_pow_sixteen e
  · rw [relIndex_centralizerMod hch hAB y, ← sRep_apply hch ρ hsurj hker y]
    exact natCard_range_of_isSwap e hy
  · rw [relIndex_centralizerMod hch hAB y, ← sRep_apply hch ρ hsurj hker y]
    exact natCard_range_of_order3 e h3 h1

end CFSG.Quasithin.H13.A6.G52
