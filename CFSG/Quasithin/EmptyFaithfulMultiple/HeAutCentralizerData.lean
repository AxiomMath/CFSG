module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

@[expose] def heSylAl : Array (Array ℕ) :=
  sylBuild 8330 2048 heSylGens (parseNats heSylParStr) (parseNats heSylLabStr)

@[expose] def heCentIdx : List ℕ := [3, 20]

@[expose] def heSiftAll (Al : Array (Array ℕ)) (js : List ℕ) : Bool :=
  js.all fun j => siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 Al[j]!

@[expose] def sylCommAll (n : ℕ) (Al : Array (Array ℕ)) (js : List ℕ) (i : ℕ) : Bool :=
  js.all fun j => eqA n (compA n Al[i]! Al[j]!) (compA n Al[j]! Al[i]!)

@[expose] def sylCentCheck (n N : ℕ) (Al : Array (Array ℕ)) (js : List ℕ) (z : ℕ) : Bool :=
  allLt N fun i => !sylCommAll n Al js i || i == 0 || i == z

end CFSG.Quasithin.EmptyFaithfulMultiple
