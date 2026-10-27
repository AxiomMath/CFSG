module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UAction
public import CFSG.LieType.Multipliers.U43Data
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.Open.Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.U43.Cover

open CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1.U43

@[expose] def matK (k : ℕ) : Matrix (Fin 4) (Fin 4) F9 :=
  Matrix.of fun i j => uncode (k / 9 ^ (4 * i.val + j.val) % 9)

@[expose] def mvK (A : Matrix (Fin 4) (Fin 4) F9) (v : Fin 4 → F9) : Fin 4 → F9 :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 + A i 3 * v 3

@[expose] def imgK (k : ℕ) (ε : Bool) (i : ℕ) : ℕ :=
  ptIndex (mvK (matK k) (if ε then barV (decode i) else decode i))

@[expose] def tuL (k : ℕ) (ε : Bool) : Array ℕ := (Array.range 820).map (imgK k ε)

@[expose] def diagL (k : ℕ) (y : List ℕ) : Array ℕ := tuL k false ++ (y.map (· + 820)).toArray

@[expose] def cI : ℕ := 3 + 3 * 9 ^ 5 + 3 * 9 ^ 10 + 3 * 9 ^ 15

@[expose] def cM1 : ℕ := 6 + 3 * 9 ^ 5 + 3 * 9 ^ 10 + 3 * 9 ^ 15

@[expose] def cDi : ℕ := 1 + 3 * 9 ^ 5 + 3 * 9 ^ 10 + 3 * 9 ^ 15

@[expose] def cDmi : ℕ := 2 + 3 * 9 ^ 5 + 3 * 9 ^ 10 + 3 * 9 ^ 15

@[expose] def genL : Array (Array ℕ) := #[tabA, tabB]

@[expose] def baseL : List ℕ := [0, 1, 9]

@[expose] def baseL4 : List ℕ := [0, 1, 9, 2]

@[expose] def baseD : List ℕ := [0, 1, 9]

@[expose] def repIn : ℕ × Bool := (1352421315757428, false)

@[expose] def repM1a : ℕ × Bool := (988661333672684, false)

@[expose] def repM1b : ℕ × Bool := (617675637233571, false)

@[expose] def repFa : ℕ × Bool := (1574439281455640, true)

@[expose] def repFb : ℕ × Bool := (121383151902288, true)

@[expose] def repIa : ℕ × Bool := (559409894806529, true)

@[expose] def rIn : Array ℕ := tuL repIn.1 repIn.2

@[expose] def rM1a : Array ℕ := tuL repM1a.1 repM1a.2

@[expose] def rM1b : Array ℕ := tuL repM1b.1 repM1b.2

@[expose] def rFa : Array ℕ := tuL repFa.1 repFa.2

@[expose] def rFb : Array ℕ := tuL repFb.1 repFb.2

@[expose] def rIa : Array ℕ := tuL repIa.1 repIa.2

end CFSG.ComponentClassification.HarrisLit.P1.U43.Cover
