module

public import CFSG.Quasithin.Background.RonanH49S4
public import CFSG.Quasithin.Background.RonanH49Cx

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr

theorem nonempty_stabE_perm4 :
    Nonempty (↥stabE ≃* (Equiv.Perm (Fin 4) ≀ᵣ Multiplicative (ZMod 2))) := by
  obtain ⟨e⟩ := nonempty_P1_mulEquiv_perm
  exact ⟨thetaEquiv.symm.trans (wreathCongr e)⟩

end CFSG.Quasithin.RonanH49
