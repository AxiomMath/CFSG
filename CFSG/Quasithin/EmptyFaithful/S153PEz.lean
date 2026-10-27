module

public import CFSG.Quasithin.EmptyFaithful.S153PE2
public import CFSG.Quasithin.EmptyFaithful.S153PE3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

namespace S153P

theorem jStruct56_of_main (hmain : Abs56Main) {G : Type} [Group G] [Finite G]
    {T Mc M V₁ V₂ : Subgroup G} {t : G} {cx : Ctx15350 T Mc M V₁ V₂ t}
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y : G}
    (H : PE.HypsA cx N₁ N₂ g s y) : JStruct56 T Mc M V₁ N₁ y := by
  obtain ⟨z, hz⟩ := S153E56e.exists_ZGen cx
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    hmain G (UH153 T M V₁ Mc) (quasithinOmegaOneCenter T) Mc z y (PE.abs56_of_hypsA H hz)
  exact ⟨PE.V0_eq_of_hypsA H hz, h1, h2, h3, h4, h5, h6⟩

theorem input15356J_of_main (hmain : Abs56Main) (h113 : StageLemma14113) : Input15356J := by
  intro G _ _ T Mc M V₁ V₂ t cx N₁ N₂ g s hc y hy
  exact jStruct56_of_main hmain ⟨h113, hc, hy⟩

end S153P

end CFSG.Quasithin
