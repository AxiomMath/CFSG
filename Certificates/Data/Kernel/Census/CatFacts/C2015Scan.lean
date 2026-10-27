
module

public import Certificates.Data.Kernel.Census.CatFacts.C2015Defs

public section

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum

local notation "V45" => VP 45

@[expose] def powW {n : Nat} (u : List (VP n)) : Nat → List (VP n)
  | 0 => []
  | k + 1 => u ++ powW u k

@[expose] def pow405 {n : Nat} (u : VP n) : VP n := cubeV (cubeV (pow45 u))

@[expose] def pairW {n : Nat} (C : List (List (VP n))) : Bool :=
  C.any fun x₁ => C.any fun x₂ => !isOneW [pow405 (codeV (pkpW (x₁ ++ x₂)))]

@[expose] def odd3W (tP : List (List V45)) : List (List V45) :=
  (productsW tP).filter fun w => isOneW (powW w 3) && !isOneW w

@[expose] def fpf2015 : Bool :=
  forceLL c15.tP fun tP => (productsW tP).all fun w =>
    !(isOneW (powW w 5) && !isOneW w) || (List.range 45).all fun j => imgW w j != j

@[expose] def force15 {β : Sort _} (k : C15 → List (List V45) → β) : β :=
  forceLL c15.tA fun tA => forceLL c15.tP fun tP => forceLv c15.lP fun lP =>
  forceV c15.s0 fun s0 => forceLL c15.cj fun cj => k ⟨tA, tP, lP, s0, cj⟩ (odd3W tP)

@[expose] def t15 (C : C15) (o3 : List (List V45)) (s : List V45) : Bool :=
  (!isOneW (s ++ s) || pairW (o3.filter fun x => eqW (x ++ s) (s ++ x))) &&
    (!isOneW (s ++ s) || siftW C.lP s || (C.cj.any fun c => eqW c s) ||
      (Finset.univ.filter fun j : Fin 45 => pkpW s j = j).card % 5 != 0)

@[expose] def grp2015 (g : Nat) : Bool :=
  force15 fun C o3 => (List.range 9).all fun i => (blockW C.tA (9 * g + i)).all (t15 C o3)

end CFSG.Certificates.Kernel.CatFacts

end
