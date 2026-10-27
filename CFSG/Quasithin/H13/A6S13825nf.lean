module

public import CFSG.Quasithin.H13.A6S13825ne

public section

namespace CFSG.Quasithin.H13.A6.L4Tw

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open L4Ind

abbrev InL (A : M4) (v : V4) : Prop :=
  v = 0 ∨ v = A *ᵥ e0 ∨ v = A *ᵥ e1 ∨ v = A *ᵥ e0 + A *ᵥ e1

@[expose] def repM : Fin 35 → M4 := ![
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 0, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0],
  !![0, 0, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 1, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 1, 0, 0; 0, 1, 0, 0],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 1, 1, 0, 1; 1, 1, 0, 0]]

@[expose] def repI : Fin 35 → M4 := ![
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0],
  !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0; 0, 1, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0],
  !![0, 0, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 1, 0],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 1],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0],
  !![0, 0, 1, 0; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 1],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 0, 0; 0, 1, 1, 1],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 1],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 0, 0],
  !![0, 0, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 1, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 0, 1, 0],
  !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 1, 0; 0, 0, 0, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 0, 1, 1],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0],
  !![0, 1, 0, 0; 0, 1, 0, 1; 1, 1, 0, 1; 0, 0, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 1],
  !![0, 0, 1, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 1, 1],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 0, 0, 0, 1],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 0],
  !![0, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 0; 0, 0, 0, 1],
  !![0, 0, 1, 1; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 1],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 0, 1],
  !![0, 1, 0, 0; 0, 1, 0, 1; 1, 1, 0, 1; 0, 0, 1, 1]]

@[expose] def plc : Fin 35 → Fin 6 → ZMod 2 := ![
  ![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 1],
  ![0, 0, 1, 0, 1, 0], ![0, 0, 1, 0, 1, 1], ![0, 0, 0, 1, 0, 1], ![0, 1, 0, 0, 0, 1],
  ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1], ![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1],
  ![0, 1, 1, 0, 0, 0], ![0, 1, 1, 0, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1],
  ![1, 0, 0, 0, 1, 0], ![1, 0, 0, 1, 0, 0], ![1, 0, 0, 1, 1, 0], ![1, 0, 1, 0, 0, 0],
  ![1, 0, 1, 0, 1, 0], ![1, 0, 1, 1, 0, 1], ![1, 0, 1, 1, 1, 1], ![1, 1, 0, 0, 0, 0],
  ![1, 1, 0, 0, 1, 1], ![1, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 1, 1], ![1, 1, 1, 0, 0, 0],
  ![1, 1, 1, 0, 1, 1], ![1, 1, 1, 1, 0, 1], ![1, 1, 1, 1, 1, 0]]

@[expose] def relG : Fin 35 → M4 := ![
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 0, 0, 1; 0, 1, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 0, 0],
  !![0, 0, 0, 1; 0, 1, 1, 0; 1, 0, 0, 0; 1, 1, 0, 0],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 1, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 0; 1, 0, 0, 1; 1, 0, 0, 0],
  !![0, 1, 1, 0; 0, 1, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 1, 0, 1; 0, 1, 0, 0],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 1, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 0, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 1, 0, 0; 0, 1, 0, 0],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 0, 1; 0, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 0, 0, 0; 1, 1, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 1; 1, 1, 0, 0; 1, 0, 0, 0],
  !![0, 1, 1, 0; 1, 0, 0, 0; 1, 1, 0, 1; 1, 1, 0, 0]]

@[expose] def relGi : Fin 35 → M4 := ![
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 1, 0; 1, 0, 0, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 0],
  !![0, 0, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 1, 0],
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 1, 0, 1; 1, 0, 0, 0],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 0],
  !![0, 0, 1, 0; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1; 1, 0, 0, 0],
  !![0, 0, 1, 0; 0, 0, 1, 1; 0, 1, 1, 1; 1, 0, 0, 0],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1; 0, 1, 0, 0],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 0, 0],
  !![0, 0, 0, 1; 0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 1, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 0, 1, 0],
  !![0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 1, 0; 0, 0, 0, 1],
  !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 0, 1, 1],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 0],
  !![0, 1, 0, 0; 0, 1, 0, 1; 1, 1, 0, 1; 0, 0, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 0, 1],
  !![0, 0, 1, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 1, 1, 1],
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 0, 0, 0, 1],
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 0],
  !![0, 1, 0, 0; 0, 1, 1, 0; 1, 1, 1, 0; 0, 0, 0, 1],
  !![0, 0, 1, 1; 0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 1, 1],
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1],
  !![0, 0, 1, 0; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 1, 0],
  !![0, 0, 0, 1; 0, 0, 1, 1; 1, 0, 1, 1; 0, 1, 0, 1],
  !![0, 1, 0, 0; 0, 1, 0, 1; 1, 1, 0, 1; 0, 0, 1, 1]]

@[expose] def relA : Fin 35 → Fin 35 := ![
  0, 0, 0, 0, 0, 0, 4, 2, 2, 2, 3, 1, 1, 1, 3, 14, 1, 16,
  16, 16, 0, 0, 0, 0, 23, 23, 23, 0, 27, 27, 27, 0, 31, 31, 31]

@[expose] def relB : Fin 35 → Fin 35 := ![
  0, 0, 0, 0, 0, 0, 5, 5, 4, 6, 5, 5, 3, 10, 4, 5, 2, 5,
  14, 15, 4, 3, 14, 2, 4, 10, 15, 1, 6, 3, 15, 16, 6, 10, 14]

@[expose] def piL : Fin 35 → Fin 35 := ![
  0, 1, 3, 2, 4, 5, 6, 10, 14, 15, 7, 11, 16, 17, 8, 9, 12, 13,
  18, 19, 20, 23, 24, 21, 22, 25, 26, 27, 28, 31, 32, 29, 30, 33, 34]

abbrev wv : Fin 6 → ZMod 2 := ![0, 0, 1, 1, 0, 0]

theorem rep_ok : ∀ ℓ : Fin 35, repM ℓ * repI ℓ = 1 := by
  decide +kernel

theorem plc_basis : ∀ k : Fin 6, plc (Fin.castLE (by norm_num) k) = Pi.single k 1 := by
  decide +kernel

theorem rel_ok : ∀ ℓ : Fin 35, 6 ≤ (ℓ : ℕ) →
    relG ℓ * relGi ℓ = 1 ∧ InL (repM ℓ) (relG ℓ *ᵥ e0) ∧ InL (repM ℓ) (relG ℓ *ᵥ e1) ∧
      InL (repM (relA ℓ)) (relG ℓ *ᵥ e0) ∧ InL (repM (relA ℓ)) (relG ℓ *ᵥ e2) ∧
      InL (repM (relB ℓ)) (relG ℓ *ᵥ e0) ∧ InL (repM (relB ℓ)) (relG ℓ *ᵥ (e1 + e2)) ∧
      relA ℓ < ℓ ∧ relB ℓ < ℓ ∧ plc ℓ = plc (relA ℓ) + plc (relB ℓ) := by
  decide +kernel

theorem tau_ok : ∀ ℓ : Fin 35,
    InL (repM (piL ℓ)) ((w0M * (repI ℓ)ᵀ * w0M) *ᵥ e0) ∧
      InL (repM (piL ℓ)) ((w0M * (repI ℓ)ᵀ * w0M) *ᵥ e1) ∧
      (plc ℓ + plc (piL ℓ) = 0 ∨ plc ℓ + plc (piL ℓ) = wv) := by
  decide +kernel

@[expose] def allV4 : List V4 :=
  [0, 1].flatMap fun a => [0, 1].flatMap fun b => [0, 1].flatMap fun c =>
    [0, 1].map fun d => ![a, b, c, d]

theorem mem_allV4 : ∀ v : V4, v ∈ allV4 := by
  decide

theorem gen_ok : ∀ v ∈ allV4, ∀ w ∈ allV4, v ≠ 0 → w ≠ 0 → v ≠ w →
    ∃ ℓ : Fin 35, InL (repM ℓ) v ∧ InL (repM ℓ) w := by
  decide +kernel

theorem inQ2_of_inL {γ g : SL4} (h0 : InL (γ : M4) ((g : M4) *ᵥ e0))
    (h1 : InL (γ : M4) ((g : M4) *ᵥ e1)) : InQ2 ((γ⁻¹ * g : SL4) : M4) := by
  rw [inQ2_iff, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec]
  have key : ∀ v, InL (γ : M4) v → InL0 (((γ⁻¹ : SL4) : M4) *ᵥ v) := by
    rintro v (rfl | rfl | rfl | rfl)
    · rw [mulVec_zero]
      decide
    · rw [inv_mulVec_mulVec]
      decide
    · rw [inv_mulVec_mulVec]
      decide
    · rw [mulVec_add, inv_mulVec_mulVec, inv_mulVec_mulVec]
      decide
  exact ⟨key _ h0, key _ h1⟩

theorem mulVec_ne_zero (g : SL4) {v : V4} (hv : v ≠ 0) : (g : M4) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← inv_mulVec_mulVec g v, h, mulVec_zero]

section Lines

variable {M : Type*} [CommGroup M] {Φ : MulAut SL4 →* MulAut M} {m₀ : M}

theorem exists_transv_of_lines (hsq : ∀ x : M, x * x = 1)
    (hQ2 : ∀ g : SL4, InQ2 (g : M4) → Φ (MulAut.conj g) m₀ = m₀) (hτ : Φ tauW m₀ = m₀)
    (hrel : m₀ * Φ (MulAut.conj q1) m₀ * Φ (MulAut.conj q2) m₀ = 1)
    (hgen : Subgroup.closure (Set.range fun g : SL4 => Φ (MulAut.conj g) m₀) = ⊤) :
    ∃ r : M, ∀ v : M, Φ tauW v * v⁻¹ = 1 ∨ Φ tauW v * v⁻¹ = r := by
  have hinv : ∀ x : M, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hcos : ∀ γ g : SL4, InL (γ : M4) ((g : M4) *ᵥ e0) → InL (γ : M4) ((g : M4) *ᵥ e1) →
      Φ (MulAut.conj g) m₀ = Φ (MulAut.conj γ) m₀ := by
    intro γ g h0 h1
    rw [show g = γ * (γ⁻¹ * g) by group, map_mul, map_mul, MulAut.mul_apply,
      hQ2 _ (inQ2_of_inL h0 h1)]
  set γ : Fin 35 → SL4 := fun ℓ => L4Ind.mkSL (repM ℓ) (repI ℓ) (rep_ok ℓ) with hγ
  set μ : Fin 35 → M := fun ℓ => Φ (MulAut.conj (γ ℓ)) m₀ with hμ
  set Ψ : (Fin 6 → ZMod 2) → M := fun v =>
    ∏ j : Fin 6, if v j = 1 then μ (Fin.castLE (by norm_num) j) else 1 with hΨ
  have hΨadd : ∀ v w, Ψ (v + w) = Ψ v * Ψ w := by
    intro v w
    simp only [hΨ, Pi.add_apply, L4Ind.ite_add_one hsq, Finset.prod_mul_distrib]
  have hΨ0 : Ψ 0 = 1 := by
    simp [hΨ]
  have hΨe : ∀ k : Fin 6, Ψ (Pi.single k 1) = μ (Fin.castLE (by norm_num) k) := by
    intro k
    simp only [hΨ]
    rw [Finset.prod_eq_single k]
    · simp
    · intro j _ hjk
      simp [hjk]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have hrelg : ∀ g : SL4, Φ (MulAut.conj g) m₀ * Φ (MulAut.conj (g * q1)) m₀ *
      Φ (MulAut.conj (g * q2)) m₀ = 1 := by
    intro g
    have := congrArg (Φ (MulAut.conj g)) hrel
    simpa only [map_mul, MulAut.mul_apply, map_one] using this
  have hq1e0 : ((q1 : SL4) : M4) *ᵥ e0 = e0 := by decide
  have hq1e1 : ((q1 : SL4) : M4) *ᵥ e1 = e2 := by decide
  have hq2e0 : ((q2 : SL4) : M4) *ᵥ e0 = e0 := by decide
  have hq2e1 : ((q2 : SL4) : M4) *ᵥ e1 = e1 + e2 := by decide
  have hmain : ∀ n (hn : n < 35), μ ⟨n, hn⟩ = Ψ (plc ⟨n, hn⟩) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases h6 : n < 6
      · have hb := plc_basis ⟨n, h6⟩
        have e : (⟨n, hn⟩ : Fin 35) = Fin.castLE (by norm_num) (⟨n, h6⟩ : Fin 6) := rfl
        rw [e, hb, hΨe]
      · obtain ⟨hgg, h0, h1, ha0, ha2, hb0, hb12, hal, hbl, hpl⟩ :=
          rel_ok ⟨n, hn⟩ (not_lt.mp h6)
        set g := L4Ind.mkSL (relG ⟨n, hn⟩) (relGi ⟨n, hn⟩) hgg with hg
        have e1 : Φ (MulAut.conj g) m₀ = μ ⟨n, hn⟩ := hcos _ _ h0 h1
        have e2 : Φ (MulAut.conj (g * q1)) m₀ = μ (relA ⟨n, hn⟩) := by
          refine hcos _ _ ?_ ?_
          · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hq1e0]
            exact ha0
          · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hq1e1]
            exact ha2
        have e3 : Φ (MulAut.conj (g * q2)) m₀ = μ (relB ⟨n, hn⟩) := by
          refine hcos _ _ ?_ ?_
          · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hq2e0]
            exact hb0
          · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hq2e1]
            exact hb12
        have hr := hrelg g
        rw [e1, e2, e3] at hr
        have ha := ih _ (Fin.lt_def.mp hal) (relA ⟨n, hn⟩).isLt
        have hb := ih _ (Fin.lt_def.mp hbl) (relB ⟨n, hn⟩).isLt
        simp only [Fin.eta] at ha hb
        rw [hpl, hΨadd, ← ha, ← hb, ← hinv (μ (relA ⟨n, hn⟩) * μ (relB ⟨n, hn⟩))]
        rw [mul_assoc] at hr
        exact eq_inv_of_mul_eq_one_left hr
  have hmain' : ∀ ℓ : Fin 35, μ ℓ = Ψ (plc ℓ) := fun ℓ => hmain ℓ ℓ.isLt
  have hτμ : ∀ ℓ, Φ tauW (μ ℓ) = μ (piL ℓ) := by
    intro ℓ
    obtain ⟨h0, h1, -⟩ := tau_ok ℓ
    have e : Φ tauW (μ ℓ) = Φ (MulAut.conj (tauW (γ ℓ))) m₀ := by
      simp only [hμ]
      rw [← MulAut.mul_apply, ← map_mul, tauW_mul_conj, map_mul, MulAut.mul_apply, hτ]
    have hm : ((tauW (γ ℓ) : SL4) : M4) = w0M * (repI ℓ)ᵀ * w0M := by
      rw [tauW_matrix, hγ, L4Ind.coe_mkSL_inv]
    rw [e]
    refine hcos _ _ ?_ ?_
    · rw [hm]
      exact h0
    · rw [hm]
      exact h1
  have hcomm : ∀ ℓ, Φ tauW (μ ℓ) * (μ ℓ)⁻¹ = 1 ∨ Φ tauW (μ ℓ) * (μ ℓ)⁻¹ = Ψ wv := by
    intro ℓ
    rw [hτμ, hinv, hmain' (piL ℓ), hmain' ℓ, ← hΨadd, add_comm]
    rcases (tau_ok ℓ).2.2 with h | h
    · left
      rw [h, hΨ0]
    · right
      rw [h]
  have hgen' : Subgroup.closure (Set.range μ) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    have hg0 := mulVec_ne_zero g (v := e0) (by decide)
    have hg1 := mulVec_ne_zero g (v := e1) (by decide)
    have hg01 : (g : M4) *ᵥ e0 ≠ (g : M4) *ᵥ e1 := by
      intro h
      have := congrArg (((g⁻¹ : SL4) : M4) *ᵥ ·) h
      simp only [inv_mulVec_mulVec] at this
      exact absurd this (by decide)
    obtain ⟨ℓ, h0, h1⟩ := gen_ok _ (mem_allV4 _) _ (mem_allV4 _) hg0 hg1 hg01
    exact Subgroup.subset_closure ⟨ℓ, (hcos (γ ℓ) g h0 h1).symm⟩
  set r := Ψ wv with hr
  let R : Subgroup M :=
    { carrier := {1, r}
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (one_mul 1)
        · exact Or.inr (one_mul _)
        · exact Or.inr (mul_one _)
        · exact Or.inl (hsq _)
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro a ha
        rw [hinv]
        exact ha }
  refine ⟨r, fun v => ?_⟩
  have := IndQuad.comm_mem_of_closure hgen' (Φ tauW) (R := R) (by
    rintro _ ⟨ℓ, rfl⟩
    rcases hcomm ℓ with h | h
    · exact Or.inl h
    · exact Or.inr h) v
  exact this

end Lines

section Main

variable {M : Type*} [CommGroup M] {Φ : MulAut SL4 →* MulAut M} {m₀ : M}

theorem exists_transv (hsq : ∀ x : M, x * x = 1)
    (hU : ∀ u ∈ unitriangular 4 (ZMod 2), Φ (MulAut.conj u) m₀ = m₀) (hτ : Φ tauW m₀ = m₀)
    (hgen : Subgroup.closure (Set.range fun g : SL4 => Φ (MulAut.conj g) m₀) = ⊤)
    {c : SL4} (hc : c ∈ Q13) (h1 : Φ (MulAut.conj c) m₀ ≠ m₀)
    (h2 : Φ (MulAut.conj (c * c)) m₀ ≠ m₀)
    (h12 : Φ (MulAut.conj c) m₀ ≠ Φ (MulAut.conj (c * c)) m₀)
    (hcc : m₀ * Φ (MulAut.conj c) m₀ = Φ (MulAut.conj (c * c)) m₀)
    {E : Subgroup (MulAut SL4)} (hE : ∀ x ∈ E, ∃ o, x = enc o)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (h4 : 4 ≤ Nat.card E) (hq : IndQuad.QuadOn Φ (E : Set (MulAut SL4))) :
    ∃ r : M, ∀ v : M, Φ tauW v * v⁻¹ = 1 ∨ Φ tauW v * v⁻¹ = r := by
  obtain ⟨hrel, hq1⟩ := rel_of hsq hU hc h1 h2 h12 hcc
  obtain ⟨A, hA, hAf⟩ := exists_fix_of_quad hsq hU hτ hrel hE hab hE2 h4 hq
  exact exists_transv_of_lines hsq (fun g hg => Q2_fix hU hτ hA hAf hq1 hg) hτ hrel hgen

end Main

end CFSG.Quasithin.H13.A6.L4Tw
