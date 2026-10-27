module

public import CFSG.Quasithin.Background.G117CanonL28
public import CFSG.Quasithin.Background.G117CanonSetup
public import CFSG.Quasithin.Background.G117Layer
public import CFSG.Quasithin.Background.G117StepsA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace Canon

open CFSG.Quasithin.G11.G117 CFSG.Assembly.LowTwoRank

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Q : ConclPred}
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {m : ℕ}

theorem step16 (hQ : QContains Q) (c : QCtx Q B Γ v₁ W X X₀ L ⊤ m)
    (h16 : G93Case16 (topH Γ L) m) : False := by
  obtain ⟨⟨-, hd, hL28⟩, hend, -⟩ := h16
  have hF := fstar_map_eq_normalClosure c.h108.component (centralizer_trivial hend)
  have hd8 : Module.finrank (ZMod 2) V = 8 := by
    rwa [finrank_top] at hd
  refine c.setup.notConcl (hQ.c11 B Γ X ⟨hd8, ?_⟩)
  rw [hF]
  exact isL28TwistedTensorModule_of_restrictRange_top hL28

end Canon

end G11

end CFSG.Quasithin
