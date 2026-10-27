module

public import CFSG.Monster.CodeAut.Perm
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.Monster.Code

open CFSG.Sporadic.Mathieu (m24gA m24gB)

@[expose] def bridgeList : List ℕ :=
  [0, 1, 2, 3, 6, 7, 8, 9, 21, 20, 19, 18, 15, 14, 13, 12, 11, 17, 5, 22, 16, 10, 4, 23]

@[expose] def bridgeQ : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 6, 7, 8, 9, 21, 20, 19, 18, 15, 14, 13, 12, 11, 17, 5, 22, 16, 10, 4, 23]
  invFun := ![0, 1, 2, 3, 22, 18, 4, 5, 6, 7, 21, 16, 15, 14, 13, 12, 20, 17, 11, 10, 9, 8, 19, 23]
  left_inv := by decide
  right_inv := by decide

theorem bridgeQ_apply : ∀ i : Fin 24, (bridgeQ i : ℕ) = bridgeList.getD i 0 := by decide

@[expose] def bridgePA : Equiv.Perm (Fin 24) := bridgeQ⁻¹ * m24gA * bridgeQ

@[expose] def bridgePB : Equiv.Perm (Fin 24) := bridgeQ⁻¹ * m24gB * bridgeQ

theorem bridgePA_apply (i : Fin 24) : bridgePA i = bridgeQ⁻¹ (m24gA (bridgeQ i)) := by
  rw [bridgePA, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem bridgePB_apply (i : Fin 24) : bridgePB i = bridgeQ⁻¹ (m24gB (bridgeQ i)) := by
  rw [bridgePB, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

@[expose] def bridgePAImage : List ℕ :=
  [3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def bridgePBImage : List ℕ :=
  [3, 9, 6, 18, 4, 5, 13, 22, 8, 14, 10, 23, 15, 2, 1, 20, 16, 7, 0, 11, 12, 21, 17, 19]

theorem bridgePA_image : ∀ i : Fin 24, (bridgePA i : ℕ) = bridgePAImage.getD i 0 := by
  decide +kernel

theorem bridgePB_image : ∀ i : Fin 24, (bridgePB i : ℕ) = bridgePBImage.getD i 0 := by
  decide +kernel

@[expose] def coeffWord (n : ℕ) : Fin 24 → ZMod 2 :=
  ∑ j : Fin 12, (if n.testBit j then 1 else 0) • B j

@[expose] def bridgePACoeff : List ℕ :=
  [1244, 2112, 1839, 1335, 571, 3200, 2582, 824, 3084, 1792, 2316, 2580]

@[expose] def bridgePBCoeff : List ℕ :=
  [1566, 483, 2277, 1, 4047, 233, 353, 2209, 3935, 673, 1121, 3999]

@[expose] def bridgeDiffGen : Fin 11 → Fin 2 := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1]

@[expose] def bridgeDiffIdx : Fin 11 → Fin 12 := ![0, 1, 2, 3, 7, 0, 1, 2, 3, 4, 8]

@[expose] def bridgeDiffCoeff : List ℕ :=
  [1245, 2114, 1835, 1343, 952, 1567, 481, 2273, 9, 4063, 3679]

@[expose] def bridgeGen : Fin 2 → Equiv.Perm (Fin 24) := ![bridgePA, bridgePB]

@[expose] def bridgeDiffWord (t : Fin 11) : Fin 24 → ZMod 2 :=
  B (bridgeDiffIdx t) + permWord (bridgeGen (bridgeDiffGen t)) (B (bridgeDiffIdx t))

end CFSG.Monster.Code
