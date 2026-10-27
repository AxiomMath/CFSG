module

public import CFSG.Sporadic.ThSchreier.PlaneSepData
public import CFSG.Sporadic.Th.FormBase
public meta import CFSG.Sporadic.ThSchreier.PlaneSepData
public meta import CFSG.Sporadic.Th.FormBase
public import Certificates.Certificate1022

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.FormBase
  Pointwise Matrix

@[expose] def sepGramRows : Array V4 :=
  mulRows (mulRows sepCRows sepFRows) (transposeRows sepCRows)

@[expose] def gramBit (p q : ℕ) : ZMod 2 := if (sepGramRows[p]!).testBit q then 1 else 0

@[expose] def sepCode (i j : ℕ) : ℕ := gramCode fun a b => gramBit (2 * i + a) (2 * j + b)

@[expose] def sepTInvRows (i : ℕ) : Array V4 := abRows (invWord (sepWords.getD i []))

@[expose] def sepKey (i : ℕ) : Key := ⟨sepCRows[2 * i]!, sepCRows[2 * i + 1]!⟩

@[expose] def sepTree : List ℕ := natsOf (include_str "Data/SepTree.txt")

@[expose] def sepTreeV (k : ℕ) : ℕ := sepTree.getD (2 * k) 0

@[expose] def sepTreeP (k : ℕ) : ℕ := sepTree.getD (2 * k + 1) 0

end CFSG.Sporadic.ThSchreier
