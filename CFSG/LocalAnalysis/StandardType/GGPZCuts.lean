module

public import CFSG.LocalAnalysis.StandardType.GGPZReflNormal
public import CFSG.LocalAnalysis.StandardType.GGPZE6Input

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPZ_conclusion_of_cuts (hV : GGPZVertInput) (hM : GGPZMultInput)
    (hE : GGPZEndpointInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {labJ labX : LargeEvenLabel} {X : Subgroup G} {m : ℕ} {z : ↥Bs}
    (hprem : GGPZPrem p B Bs x L D J y K labJ labX X m z) :
    ∃ r n c : ℕ, GGWeylTypeData r n c ∧ labJ.rank ≤ r ∧ r ≤ m ∧
      Nat.card ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
        (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z)) ∣ n ∧
      (Nat.card ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z)) = n →
        Nat.card ↥(Subgroup.center ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z))) = c) := by
  obtain ⟨Y, hY, hJY, hBY⟩ := hV G p B Bs x L D J y K labJ labX X m z hprem
  obtain ⟨r, n, c, W, _, _, f, hW, hlo, hhi, hn, hc, hQ⟩ :=
    hE G p B Bs x L D J y K labJ labX X m z hprem Y hY hJY hBY
  have hJQ : ggAutomizer J Bs ≤ ggAutomizer Y Bs := ggAutomizer_mono Bs hJY
  have hO := ggPZ_closure_orbit_le p (ggAutomizer J Bs) (ggAutomizer L Bs ⊔ ggAutomizer K Bs)
    (ggAutomizer Y Bs) z hJQ
    (ggPZ_reflNormal hprem (hM G p B Bs x L D J y K labJ labX X m z hprem) hY hJY)
  obtain ⟨hd, he⟩ := ggPZ_card_dvd_and_center_card_eq f (hO.trans hQ)
  exact ⟨r, n, c, hW, hlo, hhi, hn ▸ hd, fun h => hc ▸ he (hn ▸ h)⟩

theorem ggPZInput_of_cuts (hV : GGPZVertInput) (hM : GGPZMultInput) (hE : GGPZEndpointInput) :
    GGPZInput := by
  intro G _ _ p B Bs x L D J y K hH hp labJ labX X m hX hJΛ hXΛ hJl hXl hrow hbr hcard hJcard
    hJrefl z hzD hzx hzy
  exact ggPZ_conclusion_of_cuts hV hM hE
    ⟨hH, hX, hJΛ, hXΛ, hJl, hXl, hrow, Or.inl hbr, hcard, hJcard, hJrefl, hzD, hzx, hzy⟩

theorem ggPZE6Input_of_cuts (hV : GGPZVertInput) (hM : GGPZMultInput) (hE : GGPZEndpointInput) :
    GGPZE6Input := by
  intro G _ _ p B Bs x L D J y K hH hp labJ labX X m hX hJΛ hXΛ hJl hXl hrow hbr hcard hJcard
    hJrefl z hzD hzx hzy
  exact ggPZ_conclusion_of_cuts hV hM hE
    ⟨hH, hX, hJΛ, hXΛ, hJl, hXl, hrow, Or.inr hbr, hcard, hJcard, hJrefl, hzD, hzx, hzy⟩

end CFSG.StandardType

end
