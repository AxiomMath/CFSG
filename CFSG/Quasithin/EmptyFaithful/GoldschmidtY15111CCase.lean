module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CVertC
public import CFSG.Quasithin.Background.F6CatInputs
public import CFSG.Quasithin.Background.F6CatIso
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111CVertB

public section

namespace CFSG.Quasithin

namespace Y15111

open CFSG.Open F6

variable {D : Type} [Group D] [Finite D]

theorem noVc_of_oriented (hG22 : G22AmalgamShapeFact) (hM12 : M12AmalgamShapeFact)
    (hAut : AutM12AmalgamShapeFact) {X Y : Subgroup D} (hG : IsGoldschmidtTriple X Y)
    (hT : 64 ≤ Nat.card ↥(X ⊓ Y)) (ho : IsGoldCaseOrientedCat X Y) : NoVc ↥X ∧ NoVc ↥Y := by
  rcases ho with hI | hII | hIII | hIV | hV | hVI
  · exact absurd hT (by have := hI.card_inf; omega)
  · exact absurd hT (by have := hII.card_inf; omega)
  · exact absurd hT (by have := hIII.card_inf; omega)
  · exact absurd hT (by have := hIV.card_inf; omega)
  · exact absurd hT (by have := hV.card_inf; omega)
  rcases hVI with hL32 | hSp | hG22c | hG22p | hM12c | hAutc
  · exact absurd hT (by have := hL32.card_inf hG; omega)
  · exact absurd hT (by have := hSp.card_inf hG; omega)
  · obtain ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hsp, hc₂⟩ := hG22c
    obtain ⟨-, aR, a₂⟩ := hG22 W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
      (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
      (isSpecialTwoOnePlusFour_of_mulEquiv (pCoreOfCongr φ₁).symm hsp)
      (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
    have hQ : Nat.card ↥(Open.pCore 2 ↥Y) = 32 := by
      rw [Nat.card_congr (pCoreOfEquiv Y).toEquiv]; exact hc₂
    exact ⟨noVc_of_centralProduct
      (isCentralProduct₂_of_mulEquiv ((pCoreOfEquiv X).trans (pCoreOfCongr φ₁)) aR),
      noVc_of_z4z4 hQ (isExtensionOf_of_mulEquiv φ₂ a₂)⟩
  · exact absurd hT (by have := hG22p.card_inf hG; omega)
  · obtain ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hcp, hc₂⟩ := hM12c
    obtain ⟨-, a₂⟩ := hM12 W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
      (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
      (isCentralProduct₂_of_mulEquiv (pCoreOfCongr φ₁).symm hcp)
      (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
    have hQ : Nat.card ↥(Open.pCore 2 ↥Y) = 32 := by
      rw [Nat.card_congr (pCoreOfEquiv Y).toEquiv]; exact hc₂
    exact ⟨noVc_of_centralProduct (isCentralProduct₂_of_mulEquiv (pCoreOfEquiv X) hcp),
      noVc_of_z4z4 hQ (isExtensionOf_of_mulEquiv φ₂ a₂)⟩
  · obtain ⟨⟨W, _, _, K₁, K₂, hW, hTL, φ₁, φ₂, hag₁, hag₂⟩, -, hq₁, hq₂, hext, hc₁, hz₁, hc₂⟩ :=
      hAutc
    obtain ⟨-, a₂⟩ := hAut W K₁ K₂ hW hTL (quotientPCoreIsL22_of_mulEquiv φ₁ hq₁)
      (quotientPCoreIsL22_of_mulEquiv φ₂ hq₂)
      (isExtensionWith_centralProduct_of_mulEquiv φ₁.symm hext)
      (by rw [← Nat.card_congr (pCoreOfCongr φ₁).toEquiv]; exact hc₁)
      (by rw [← card_centerOf_eq (pCoreOfCongr φ₁)]; exact hz₁)
      (by rw [← Nat.card_congr (pCoreOfCongr φ₂).toEquiv]; exact hc₂)
    have hQ : Nat.card ↥(Open.pCore 2 ↥X) = 64 := by
      rw [Nat.card_congr (pCoreOfEquiv X).toEquiv, hc₁]
      norm_num
    exact ⟨noVc_of_autM12_left hQ hext, noVc_of_autM12_right (isExtensionOf₃_of_mulEquiv φ₂ a₂)⟩

end Y15111

end CFSG.Quasithin
