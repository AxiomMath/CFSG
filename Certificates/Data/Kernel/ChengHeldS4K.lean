module

public import Certificates.Data.Kernel.ChengHeldAutK

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeldS2

variable (n : ℕ) (m : ℕ → ℕ → ℕ) (inv g : ℕ → ℕ)

@[expose] def cgK (gs : List ℕ) (a : ℕ) : Bool := gs.all fun y => m a y == m y a

@[expose] def cmM (a b : ℕ) : ℕ := m (m (m a b) (inv a)) (inv b)

@[expose] def o2K (a k : ℕ) : Bool := pwK m a (2 ^ (k + 1)) == 0 && !(pwK m a (2 ^ k) == 0)

@[expose] def derW (gs ds : List ℕ) (A : ℕ → Bool) (ps : List (ℕ × ℕ)) (K : ℕ) : Bool :=
  (List.range n).all (fun h => ds.all fun d => bitW n (clIterK n m ds K) (m (m h d) (inv h))) &&
    gs.all (fun x => gs.all fun y => bitW n (clIterK n m ds K) (cmM m inv x y)) &&
    ps.all (fun p => A p.1 && A p.2) && ps.map (fun p => cmM m inv p.1 p.2) == ds

@[expose] def s4RestW (α K : ℕ) (ws : List ℕ) : Bool :=
  let t := g 0
  let pi := g 1
  let tau := g 2
  let mu := g 3
  let lam := g 4
  let ze := g 5
  let xi := g 6
  let gs7 := [g 0, g 1, g 2, g 3, g 4, g 5, g 6]
  let Zt := bitW n (clIterK n m [t] K)
  let D := bitW n (clIterK n m [t, pi, tau] K)
  let R1 := bitW n (clIterK n m [t, pi, tau, mu, lam] K)
  let R2 := bitW n (clIterK n m [t, pi, tau, ze, xi] K)
  let V := bitW n (clIterK n m [pwK m t 2, pi, m t tau] K)
  let W := bitW n (clIterK n m ws K)
  let mlx := m (m mu lam) xi
  let inv2 := fun a => a != 0 && m a a == 0
  n == 256 && o2K m t 1 &&
    (List.range n).all (fun x => (decide (x < n) && cgK m gs7 x) == Zt x) && cardW n Zt == 4 &&
    cardW n D == 16 && cardW n R1 == 64 && cardW n R2 == 64 &&
    (List.range n).all (fun x => (R1 x && R2 x) == D x) &&
    (List.range n).all (fun x => (R1 x && (decide (x < n) && cgK m [t, pi, tau, mu, lam] x)) ==
      Zt x) &&
    (List.range n).all (fun x => (R2 x && (decide (x < n) && cgK m [t, pi, tau, ze, xi] x)) ==
      Zt x) &&
    ((elemsK n fun x => decide (x < n)).filter inv2).length == 55 &&
    ((elemsK n fun x => R1 x || R2 x).filter inv2).length == 55 &&
    (((elemsK n R1).filter inv2).filter fun a => !Zt a).length == 30 &&
    (((elemsK n R1).filter fun a => o2K m a 1).filter fun a => !Zt a).length == 30 &&
    (((elemsK n R2).filter inv2).filter fun a => !Zt a).length == 30 &&
    (((elemsK n R2).filter fun a => o2K m a 1).filter fun a => !Zt a).length == 30 &&
    ((List.range n).filter fun s => pwK m s 2 == t || pwK m s 2 == inv t).length == 0 &&
    ([pwK m t 2, pi, m t tau].all (fun a => [pwK m t 2, pi, m t tau].all fun b => m a b == m b a) &&
      (elemsK n V).all fun a => m a a == 0) &&
    cardW n V == 8 && cardW n W == 64 &&
    (ws.all fun x => ws.all fun y => m x y == m y x) == (α == 0) &&
    ((elemsK n W).filter inv2).all V &&
    (elemsK n W).all (fun a => !o2K m a 2) &&
    (α == 0 || (List.range n).all (fun x => (W x && (decide (x < n) && cgK m ws x)) ==
      bitW n (clIterK n m [t, pi, m t tau] K) x)) &&
    (m (m (inv mlx) (inv (m (m mu ze) xi))) (m mlx (m (m mu ze) xi)) == 0) == (α == 0) &&
    pwK m (m mlx tau) 2 == pi

end CFSG.KC.ChengHeldP

end
