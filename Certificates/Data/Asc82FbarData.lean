module

public import Certificates.Data.CatFactsL4U4P1L43Data
public import Certificates.Data.Asc82FbarCheck

public section

namespace Certificates.Asc82Fbar

open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.HarrisLit.P1.L43

@[expose] def fbarInner (_ : Unit := ()) : InnerData where
  b := tm 37301281
  c := tm 38099616
  r₁ := tm 23098396
  r₂ := tm 11712909

@[expose] def rhoPairs : List (ℕ × ℕ) :=
  [(28, 14408200), (37, 39333700), (31, 28712323), (46, 25102647), (67, 33613399),
    (41, 39453247), (34, 28765467), (22, 38337301), (59, 20261358), (16, 29290348),
    (48, 34071850), (65, 33606756), (42, 39393460), (23, 19191916), (79, 15006151),
    (75, 14946364), (56, 38855539), (15, 15420069), (21, 38270898), (17, 15484285),
    (53, 25109290), (69, 23975605), (74, 14888791), (62, 20208214)]

@[expose] def fbarRho (_ : Unit := ()) : List Table :=
  (List.range 81).map fun c => match rhoPairs.lookup c with
    | some k => tm k
    | none => idT 80

@[expose] def fbarOuter (_ : Unit := ()) : OuterData where
  b := tm 19250485
  c := tm 31901178
  run := 0
  row := 2
  rho := fbarRho ()

end Certificates.Asc82Fbar
