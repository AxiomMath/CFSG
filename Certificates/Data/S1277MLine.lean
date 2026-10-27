module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace Certificates.Data.S1277MLine

open CFSG.Quasithin.H13.S127.Mod

@[expose] def fixList (B : B6) : List ℕ := (List.range 64).filter fun c => B.app c == c

@[expose] def isInv (B : B6) : Bool := B.comp B == B6.id && B != B6.id

@[expose] def dedupAux : List ℕ → List ℕ → List ℕ
  | acc, [] => acc
  | acc, x :: xs => if acc.contains x then dedupAux acc xs else dedupAux (x :: acc) xs

@[expose] def dedupN (l : List ℕ) : List ℕ := dedupAux [] l

@[expose] def orbitSize (G : List B6) (c : ℕ) : ℕ := (dedupN (G.map fun B => B.app c)).length

@[expose] def invsD (Γ : List B6) (D : List ℕ) : List B6 :=
  Γ.filter fun B => isInv B && D.all fun d => B.app d == d

@[expose] def stabD (Γ : List B6) (D : List ℕ) : List B6 :=
  Γ.filter fun B => D.all fun d => D.contains (B.app d)

@[expose] def orbD (D : List ℕ) (n : ℕ) : List ℕ := D.filter fun c => orbitSize gm6 c == n

@[expose] def perD (Γ : List B6) (D : List ℕ) : Bool :=
  decide ((invsD Γ D).length ≤ 3) &&
    (decide ((invsD Γ D).length < 3) ||
      (decide (4 ≤ (orbD D 18).length) &&
        (orbD D 18).all (fun t => (orbD D 18).all fun s => (stabD Γ D).any fun B => B.app t == s) &&
        (orbD D 45).any fun c => decide (9 ≤ (dedupN ((stabD Γ D).map fun B => B.app c)).length)))

@[expose] def mCheck (Γ : List B6) (_ : Unit := ()) : Bool :=
  Γ.all (fun B => !isInv B || decide ((fixList B).length ≤ 16)) &&
    Γ.all fun B₀ => !(isInv B₀ && (fixList B₀).length == 16) || perD Γ (fixList B₀)

end Certificates.Data.S1277MLine

end
