module

public import CFSG.Sporadic.SuzRecog.LevelTwoHomotopy
public import Mathlib

public section

namespace CFSG.KC.RankElim

open CFSG.Sporadic.SuzRecog.ElimCert

@[expose] def listOK (n : ℕ) (nb : Array (Array ℕ)) (par : ℕ → ℕ) (rk ap bp : ℕ → ℕ → ℕ)
    (tri : ℕ → ℕ → ℕ → Bool) (x k : ℕ) : Bool :=
  let y := (nb[x]!)[k]!
  let z := (nb[x]!)[ap x k]!
  x == y || n ≤ y ||
    (rk x k == 0 && ((0 < y && par y == x) || (0 < x && par x == y))) ||
    (0 < rk x k && ap x k < (nb[x]!).size && z < n && x != z && z != y && rk x (ap x k) < rk x k &&
      ((bp x k < (nb[z]!).size && (nb[z]!)[bp x k]! == y && rk z (bp x k) < rk x k) ||
        (bp x k < (nb[y]!).size && (nb[y]!)[bp x k]! == z && rk y (bp x k) < rk x k)) &&
      tri x z y)

@[expose] def ok (n : ℕ) (nb : Array (Array ℕ)) (par dep : ℕ → ℕ) (rk ap bp : ℕ → ℕ → ℕ)
    (tri : ℕ → ℕ → ℕ → Bool) : Bool :=
  0 < n &&
    (List.range n).all (fun x => x == 0 || (par x < n && dep (par x) < dep x && adjB nb (par x) x)) &&
    (List.range n).all fun x => (List.range (nb[x]!).size).all fun k =>
      listOK n nb par rk ap bp tri x k

end CFSG.KC.RankElim
