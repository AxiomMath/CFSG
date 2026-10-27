module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel

public section

namespace CFSG.ASVolI.ChH

open scoped Matrix
open CFSG.Quasithin CFSG.Open

@[expose] def invGL4 (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) (h : A * A = 1) : GL (Fin 4) (ZMod 2) :=
  ⟨A, A, h, h⟩

@[expose] def mP01_23 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def mP02_13 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

@[expose] def mP01 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mP23 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def mZJ : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 0, 1; 1, 1, 1, 0]

@[expose] def mT02 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mT03 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mT12 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mT13 : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

theorem mP01_23_sq : mP01_23 * mP01_23 = 1 := by decide
theorem mP02_13_sq : mP02_13 * mP02_13 = 1 := by decide
theorem mP01_sq : mP01 * mP01 = 1 := by decide
theorem mP23_sq : mP23 * mP23 = 1 := by decide
theorem mZJ_sq : mZJ * mZJ = 1 := by decide
theorem mT02_sq : mT02 * mT02 = 1 := by decide
theorem mT03_sq : mT03 * mT03 = 1 := by decide
theorem mT12_sq : mT12 * mT12 = 1 := by decide
theorem mT13_sq : mT13 * mT13 = 1 := by decide

@[expose] def gP01_23 : GL (Fin 4) (ZMod 2) := invGL4 mP01_23 mP01_23_sq
@[expose] def gP02_13 : GL (Fin 4) (ZMod 2) := invGL4 mP02_13 mP02_13_sq
@[expose] def gP01 : GL (Fin 4) (ZMod 2) := invGL4 mP01 mP01_sq
@[expose] def gP23 : GL (Fin 4) (ZMod 2) := invGL4 mP23 mP23_sq
@[expose] def gZJ : GL (Fin 4) (ZMod 2) := invGL4 mZJ mZJ_sq
@[expose] def gT02 : GL (Fin 4) (ZMod 2) := invGL4 mT02 mT02_sq
@[expose] def gT03 : GL (Fin 4) (ZMod 2) := invGL4 mT03 mT03_sq
@[expose] def gT12 : GL (Fin 4) (ZMod 2) := invGL4 mT12 mT12_sq
@[expose] def gT13 : GL (Fin 4) (ZMod 2) := invGL4 mT13 mT13_sq

@[expose] noncomputable def Rg4 : Subgroup (MulAut (PairN 4)) :=
  Subgroup.closure {pairActN 4 gT02, pairActN 4 gT03, pairActN 4 gT12, pairActN 4 gT13}

@[expose] noncomputable def A1g : Subgroup (MulAut (PairN 4)) :=
  Subgroup.closure {pairActN 4 gP01_23, pairActN 4 gP02_13, pairActN 4 gZJ, swapN 4}

@[expose] noncomputable def A2g : Subgroup (MulAut (PairN 4)) :=
  Subgroup.closure {pairActN 4 gP01, pairActN 4 gP23, pairActN 4 gZJ, swapN 4}

@[expose] def vP01_23 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 1, a 0, a 3, a 2]
@[expose] def vP02_13 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 2, a 3, a 0, a 1]
@[expose] def vP01 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 1, a 0, a 2, a 3]
@[expose] def vP23 (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 := ![a 0, a 1, a 3, a 2]
@[expose] def vZJ (a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![a 0 + (a 0 + a 1 + a 2 + a 3), a 1 + (a 0 + a 1 + a 2 + a 3),
    a 2 + (a 0 + a 1 + a 2 + a 3), a 3 + (a 0 + a 1 + a 2 + a 3)]

@[expose] def A1vec (ε a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  (if ε 0 = 1 then vP01_23 else id) ((if ε 1 = 1 then vP02_13 else id)
    ((if ε 2 = 1 then vZJ else id) a))

@[expose] def A2vec (ε a : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  (if ε 0 = 1 then vP01 else id) ((if ε 1 = 1 then vP23 else id)
    ((if ε 2 = 1 then vZJ else id) a))

@[expose] def A1fst (ε a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  if ε 3 = 0 then A1vec ε a else A1vec ε b
@[expose] def A1snd (ε a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  if ε 3 = 0 then A1vec ε b else A1vec ε a

@[expose] def A2fst (ε a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  if ε 3 = 0 then A2vec ε a else A2vec ε b
@[expose] def A2snd (ε a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  if ε 3 = 0 then A2vec ε b else A2vec ε a

@[expose] def Rfst (ε a _b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![a 0 + ε 0 * a 2 + ε 1 * a 3, a 1 + ε 2 * a 2 + ε 3 * a 3, a 2, a 3]
@[expose] def Rsnd (ε _a b : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  ![b 0, b 1, b 2 + ε 0 * b 0 + ε 2 * b 1, b 3 + ε 1 * b 0 + ε 3 * b 1]

end CFSG.ASVolI.ChH
