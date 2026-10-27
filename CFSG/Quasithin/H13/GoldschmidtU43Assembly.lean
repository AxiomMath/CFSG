module

public import CFSG.Quasithin.H13.GoldschmidtU43Main
public import CFSG.RankThree.PartTwo.Census.NineCoverU43

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.LieType.Multipliers.U43 (X₀ nonempty_mulEquiv_X₀)
open CFSG.RankThree.PartTwo.Sec4.Census.NineCoverU43 (lieModel_U43)
open CFSG.Quasithin.H13.A6 (StmtU43Type)

@[expose] def U43Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Hyp z →
    ∃ X : Subgroup G, Hz z ≤ X ∧ Nonempty (↥X ≃* X₀)

@[expose] def U43Endgame : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G), Hyp z →
    ∀ X : Subgroup G, Hz z ≤ X → Nonempty (↥X ≃* X₀) → X = ⊤

theorem main_of_core_endgame (h1 : U43Core) (h2 : U43Endgame) : U43Main := by
  intro G _ _ z hz
  obtain ⟨X, hHX, ⟨e⟩⟩ := h1 G z hz
  have hX : X = ⊤ := h2 G z hz X hHX ⟨e⟩
  have e' : G ≃* X₀ :=
    ((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr hX.symm)).trans e
  obtain ⟨e0⟩ := nonempty_mulEquiv_X₀ lieModel_U43
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (e0.trans e'.symm) lieModel_U43

theorem stmtU43Type_of_core_endgame (h1 : U43Core) (h2 : U43Endgame) : StmtU43Type :=
  stmtU43Type_of_main (main_of_core_endgame h1 h2)

end CFSG.Quasithin.H13.U43
