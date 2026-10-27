module

public import CFSG.Quasithin.Background.B3Tab

public section

namespace CFSG.Quasithin.B3

@[expose] def Tgens : (n : ℕ) → List (Gp n)
  | 5 => [Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3]
  | 6 => [Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 4 5]
  | 7 => [Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3, Equiv.swap 4 5]
  | 8 => [Equiv.swap 0 1, Equiv.swap 0 2 * Equiv.swap 1 3,
          Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 6 * Equiv.swap 3 7]
  | _ => []

@[expose] def bfsStep (gens : List Tab) (st : List Tab × List Tab) (x : Tab) :
    List Tab × List Tab :=
  gens.foldl (fun (acc : List Tab × List Tab) g =>
    let y := mulT g x
    if acc.1.contains y then acc else (y :: acc.1, y :: acc.2)) st

@[expose] def bfs (gens : List Tab) : ℕ → List Tab → List Tab → List Tab
  | 0, seen, _ => seen
  | fuel + 1, seen, frontier =>
      if frontier.isEmpty then seen
      else
        let st := frontier.foldl (bfsStep gens) (seen, [])
        bfs gens fuel st.1 st.2

@[expose] def closeT (n : ℕ) (gens : List Tab) : List Tab :=
  (bfs gens 300 [idT n] [idT n]).reverse

@[expose] def Tl (n : ℕ) : List Tab := closeT n ((Tgens n).map tab)

@[expose] def invsOf (n : ℕ) (T : List Tab) : List Tab :=
  T.filter (fun s => !(s == idT n) && mulT s s == idT n)

@[expose] def seteqT (A B : List Tab) : Bool :=
  A.all (fun x => B.contains x) && B.all (fun x => A.contains x)

@[expose] def extT (A : List Tab) (s : Tab) : List Tab :=
  A ++ A.map (fun a => mulT a s)

@[expose] def nextLevel (invs : List Tab) (prev : List (List Tab)) : List (List Tab) :=
  prev.foldl (fun (seen : List (List Tab)) A =>
    invs.foldl (fun (seen2 : List (List Tab)) s =>
      if !(A.contains s) && A.all (fun a => mulT a s == mulT s a) then
        let B := extT A s
        if seen2.any (fun C => seteqT B C) then seen2 else B :: seen2
      else seen2) seen) []

@[expose] def eaLevels (n : ℕ) (T : List Tab) : ℕ → List (List Tab) → List (List (List Tab))
  | 0, _ => []
  | fuel + 1, lv =>
      let nxt := nextLevel (invsOf n T) lv
      if nxt.isEmpty then [] else nxt :: eaLevels n T fuel nxt

@[expose] def Dl (n : ℕ) : List (List Tab) :=
  [idT n] :: ((eaLevels n (Tl n) 7 [[idT n]]).flatten)

end CFSG.Quasithin.B3
