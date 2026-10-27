module

public import CFSG.Quasithin.Background.SmithB42LnL5Case11
public import CFSG.Quasithin.Background.SmithB42LnNat

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.B42Ln

theorem asB42L52_holds :
    AsB42L52 := by
  intro V _ _ hV G L hHyp hL A hA
  obtain ⟨hZ, hmodel⟩ := hL
  obtain ⟨e⟩ := exists_statedSL_of_model hZ hmodel
  let : Module (ZMod 2) (Additive V) := zmod2Mod hV
  rcases l5Model_of_offender hHyp hZ e hA with htriv | ⟨κ, β, hβ⟩ | ⟨κ, β, hβ⟩
  · exact (not_trivial e htriv).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (case9 hV hHyp hZ (Or.inr rfl) (binaryNaturalSL_of_nat e hβ) hA)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (case11 hV hHyp hZ hA hβ))))))))))

end CFSG.Quasithin
