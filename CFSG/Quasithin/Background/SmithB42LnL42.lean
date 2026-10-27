module

public import CFSG.Quasithin.Background.SmithB42LnL4S8
public import CFSG.Quasithin.Background.SmithB42LnNat

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.B42Ln

theorem asB42L42_holds_core {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)} (hHyp : B4HypCore G L)
    (hL : B42TypeL42 ↥L) {A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    B42Case9 G L ∨ B42Case10 G L A := by
  obtain ⟨hZ, hmodel, hA8⟩ := hL
  obtain ⟨e⟩ := exists_statedSL_of_model hZ hmodel
  obtain ⟨ι⟩ := B42Alt7.nonempty_iso_of_center hZ hA8
  let : Module (ZMod 2) (Additive V) := zmod2Mod hV
  rcases l4Model_of_offender_core hHyp hZ e hA with htriv | ⟨κ, β, hβ⟩ | ⟨β, hβ⟩
  · exact (not_trivial4 e htriv).elim
  · exact Or.inl (case9_core hV hHyp hZ (Or.inl rfl) (binaryNaturalSL_of_nat4 e hβ) hA)
  · refine Or.inr ?_
    by_cases hGL : G = L
    · exact case10_eq_core hV hHyp hZ hA hβ hGL
    · exact case10_ne_core hV hHyp hZ ι hβ hGL

theorem asB42L42_holds : AsB42L42 := by
  intro V _ _ hV G L hHyp hL A hA
  rcases asB42L42_holds_core hV hHyp.core hL hA with h9 | h10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h10)))))))))

end CFSG.Quasithin
