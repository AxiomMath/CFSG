module

public import Certificates.Data.GrSLitL34FactsCF23U52Data

public section

namespace CFSG.ComponentClassification.GSThmB.U52.Cover

open CFSG.ComponentClassification.GSThmB.U52

@[expose] def codeRA : ℕ := 281543700398081

@[expose] def codeRB : ℕ := 70643626295297

@[expose] def sylCodes : List ℕ :=
  [338775203954025, 89353621990077, 804734416917121, 783822959349761]

@[expose] def genL : Array (Array ℕ) := #[tabN codeA, tabN codeB]

@[expose] def repAL : Array ℕ := tabN codeRA

@[expose] def repBL : Array ℕ := tabN codeRB

@[expose] def sylL : Array (Array ℕ) := (sylCodes.map tabN).toArray

@[expose] def baseL : List ℕ := [0, 1, 16, 4, 64]

end CFSG.ComponentClassification.GSThmB.U52.Cover
