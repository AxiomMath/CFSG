
module


public import CFSG.Sporadic.Th.KernelInputs

public section

namespace CFSG.Sporadic.Th.Kernel

structure ThKernelFacts : Prop where
  facts : KernelFacts
  y_cube : yJ ^ 3 = 1
  cent_a : Subgroup.centralizer ({a} : Set J) = Max3.M
  cent7 : ∃ z : J, orderOf z = 7 ∧ Nat.card (Subgroup.centralizer ({z} : Set J)) ≤ 1176
  cent5 : ∃ x : J, orderOf x = 5 ∧ Nat.card (Subgroup.centralizer ({x} : Set J)) ≤ 3000

end CFSG.Sporadic.Th.Kernel
