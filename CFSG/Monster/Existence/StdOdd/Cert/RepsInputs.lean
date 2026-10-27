module

public import CFSG.LieType.Chevalley.C2E6StandardFixedData

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std

@[expose] def wordOfString (s : String) : List (ℕ × Bool) :=
  s.toList.map fun c => if c = 'A' then (0, true) else if c = 'B' then (1, true) else (1, false)

@[expose] def wordPow (v : List (ℕ × Bool)) (k : ℕ) : List (ℕ × Bool) :=
  (List.replicate k v).flatten

@[expose] def repWord5 : List (ℕ × Bool) := wordPow (wordOfString "AbABAbAbABAbABAb") 6

@[expose] def repWord7A : List (ℕ × Bool) := wordPow (wordOfString "ABABAbAbABAbABAbAB") 5

@[expose] def repWord7B : List (ℕ × Bool) := wordPow (wordOfString "AbABAbABABAbABABAB") 4

@[expose] def repWord11 : List (ℕ × Bool) := wordPow (wordOfString "AbAbAbAbAbABAbAB") 3

@[expose] def repWord13 : List (ℕ × Bool) := wordOfString "AbAbAbAbABABAbAb"

@[expose] def repWord17 : List (ℕ × Bool) := wordOfString "AbAbAbAbABAbABAbAb"

@[expose] def repWord19 : List (ℕ × Bool) := wordOfString "ABAbAbAbAbAbAbAb"

end CFSG.Monster.Existence.StdOdd.Cert
