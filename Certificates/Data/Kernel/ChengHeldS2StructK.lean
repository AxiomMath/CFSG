module

public import Certificates.Data.Kernel.ChengHeldAutK

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeldS2

variable (n : ℕ) (m : ℕ → ℕ → ℕ) (inv g : ℕ → ℕ)

@[expose] def ordW (a : ℕ) : ℕ :=
  ((List.range (n + 1)).find? fun k => k > 0 && pwK m a k == 0).getD 0

@[expose] def centralW (a : ℕ) : Bool :=
  decide (a < n) && (List.range n).all fun b => m a b == m b a

@[expose] def cmW (a b : ℕ) : ℕ := m (m (inv a) (inv b)) (m a b)

@[expose] def genCmW : List ℕ :=
  (List.range 7).flatMap fun i => (List.range 7).map fun j => cmW m inv (g i) (g j)

@[expose] def elemAbW (B : ℕ → Bool) : Bool :=
  ((elemsK n B).all fun a => (elemsK n B).all fun b => m a b == m b a) &&
    (elemsK n B).all fun a => m a a == 0

@[expose] def involsW (B : ℕ → Bool) : List ℕ := (elemsK n B).filter fun a => a != 0 && m a a == 0

@[expose] def rootW (x : ℕ) : Bool := (List.range n).any fun s => pwK m s 2 == x

@[expose] def s2CmW (K : ℕ) : Bool :=
  clW n m (genCmW m inv g) K &&
    Nat.beq (clIterK n m (genCmW m inv g) K) (clIterK n m [g 0, g 1, g 2] K) &&
    (List.range 7).all (fun j => Nat.blt (g j) n) &&
    (List.range n).all fun x => centralW n m x == bitW n (clIterK n m [g 0, g 1, g 2] K) x

@[expose] def s2RestW (K : ℕ) : Bool :=
  let q := g 0
  let pi := g 1
  let tau := g 2
  let mu := g 3
  let lam := g 4
  let ze := g 5
  let xi := g 6
  let D := bitW n (clIterK n m [q, pi, tau] K)
  let R1 := bitW n (clIterK n m [q, pi, tau, mu, lam] K)
  let R2 := bitW n (clIterK n m [q, pi, tau, ze, xi] K)
  ordW n m q == 2 && cardW n D == 8 && cardW n R1 == 32 && cardW n R2 == 32 &&
    elemAbW n m R1 && elemAbW n m R2 &&
    ((List.range n).all fun x => (decide (x < n) && (R1 x && R2 x)) == D x) &&
    (involsW n m fun x => decide (x < n)).length == 55 &&
    (involsW n m fun x => decide (x < n) && (R1 x || R2 x)).length == 55 &&
    !rootW n m q && rootW n m pi && rootW n m (m q pi) && rootW n m tau && rootW n m (m q tau) &&
    pwK m (m (m mu lam) xi) 2 == pi && pwK m (m mu ze) 2 == m q pi

end CFSG.KC.ChengHeldP

end
