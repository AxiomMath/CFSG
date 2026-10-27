module

public import CFSG.Quasithin.Background.SmithB45M22HatDim
public import CFSG.Quasithin.Background.SmithB45M22HatHat
public import CFSG.Quasithin.Background.SmithB45M22HatSmall
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin

open HatM22 CFSG.CharacterTheory.SteinbergBY

theorem asB45HatM22_holds
    (hSmall : HatM22SmallModules) : AsB45HatM22 := by
  intro V _ _ hV G L hHyp hT h1 h2
  have hcard : Nat.card V < 2 ^ 30 :=
    lt_of_le_of_lt (card_le_of_hatM22 hV hHyp hT h2) (by norm_num)
  have hR := hSmall V hV L hT hHyp.2.2.2 hcard
  left
  iterate 7 right
  left
  exact ⟨⟨FieldFour, inferInstance, inferInstance, hatM22Γ₀, FieldFour.natCard_eq,
    isHat_hatM22Γ₀, ⟨hatM22Form, hatM22Form_det_ne_zero, hatM22Form_hermitian,
      hatM22Form_invariant⟩, hR⟩, lt_of_lt_of_le h1 (qhatOf_le_qOf G)⟩

end CFSG.Quasithin
