module

public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin

theorem asB42L2Even_holds :
    AsB42L2Even := by
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨hZ, f, hf, hmodel⟩ := hP
  obtain ⟨F, _, _, hF, ⟨θL⟩⟩ := B42L2.exists_sl2_of_model hZ hmodel
  have hf2 : 2 ≤ f := by omega
  have hw : ∀ B, IsFFStarOffender G B → Nat.card B * Nat.card (fixV B) = Nat.card V :=
    fun B hB => B42L2.weight_eq_sl2 hV hHyp hZ hf2 hF θL hB
  obtain ⟨Q, -, hQ, hQq, -⟩ := exists_quadratic_offender_le hV hA
  rcases (B42L2.sl2_alt hV hHyp hZ hf2 hF θL hQ hQq).2 with ⟨-, e, he⟩ | ⟨hf2', -⟩
  · exact Or.inl (B42L2.case1_of_natural hV hHyp hZ (by omega) hF θL e he hw hA)
  · omega

end CFSG.Quasithin
