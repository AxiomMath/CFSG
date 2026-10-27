module

public import CFSG.Quasithin.Background.SmithB42LnL5Par

public section

namespace CFSG.Quasithin.G11.Harris.Ln2

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42Ln Matrix

@[expose] def fixSet (A : Fin 4 → Matrix (Fin 10) (Fin 10) (ZMod 2)) : Finset (Fin 10 → ZMod 2) :=
  Finset.univ.filter fun w => ∀ j, A j *ᵥ w = w

theorem mem_fixSet {A : Fin 4 → Matrix (Fin 10) (Fin 10) (ZMod 2)} {w : Fin 10 → ZMod 2} :
    w ∈ fixSet A ↔ ∀ j, A j *ᵥ w = w := by
  simp [fixSet]

theorem card_fixSet_center :
    (fixSet fun j => wedgeMat (eTM 0 j.succ)).card = 16 := by decide +kernel

theorem card_fixSet_axis :
    (fixSet fun j => wedgeMat (eTM j.succ 0)).card = 64 := by decide +kernel

end CFSG.Quasithin.G11.Harris.Ln2
