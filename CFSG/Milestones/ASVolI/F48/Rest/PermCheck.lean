module

public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.OrbitCert

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native

section Words

variable {n : ℕ}

@[expose] def burnsideF48t_letA (L Li : Array (Array ℕ)) (l : Fin n × Bool) : Array ℕ :=
  if l.2 then L[(l.1 : ℕ)]! else Li[(l.1 : ℕ)]!

@[expose] def burnsideF48t_evA (N : ℕ) (L Li : Array (Array ℕ)) : List (Fin n × Bool) → Array ℕ
  | [] => pid N
  | l :: w => pcomp N (burnsideF48t_letA L Li l) (burnsideF48t_evA N L Li w)

end Words

@[expose] def burnsideF48t_closeSet (N : ℕ) (gs : Array (Array ℕ)) (fuel : ℕ) :
    Std.HashSet (Array ℕ) := Id.run do
  let mut seen : Std.HashSet (Array ℕ) := (∅ : Std.HashSet (Array ℕ)).insert (pid N)
  let mut queue : Array (Array ℕ) := #[pid N]
  let mut i := 0
  for _ in [0:fuel] do
    if i < queue.size then
      let e := queue[i]!
      i := i + 1
      for g in gs do
        let f := pcomp N e g
        if !seen.contains f then
          seen := seen.insert f
          queue := queue.push f
    else
      break
  return seen

@[expose] def burnsideF48t_closedOK (N : ℕ) (gs : Array (Array ℕ)) (E : Std.HashSet (Array ℕ)) :
    Bool :=
  E.contains (pid N) && E.toList.all fun e => gs.all fun g => E.contains (pcomp N e g)

section Checks

open CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def burnsideF48t_baseArr {N : ℕ} (b : List (Fin N)) : Array ℕ := (b.map Fin.val).toArray

@[expose] def burnsideF48t_levels (N : ℕ) (O : Array (Array ℕ)) (W : Array (List ℤ))
    (b : List (Fin N)) : Array Level :=
  rawLevels N (strongArrs N O W) (burnsideF48t_baseArr b)

@[expose] def burnsideF48t_sift (N : ℕ) (lv : Array Level) (b : List (Fin N)) (t : Array ℕ) : Bool :=
  siftA N lv (burnsideF48t_baseArr b) 0 t

@[expose] def burnsideF48t_bfs (m : ℕ) (gens : Array (Array ℕ)) (root : ℕ) : Array ℕ := Id.run do
  let mut L : Array ℕ := #[root]
  let mut seen : Array Bool := (Array.replicate m false).set! root true
  for i in [0:m] do
    if i < L.size then
      for g in gens do
        let y := g[L[i]!]!
        if y < m && !seen[y]! then
          seen := seen.set! y true
          L := L.push y
  return L

@[expose] def burnsideF48t_orbCert (m : ℕ) (gens : Array (Array ℕ)) (L : Array ℕ) : Bool :=
  orbitCertOK m gens L (CFSG.ONSchreier.Native.posArr m L)
    (orbitRecs gens L (CFSG.ONSchreier.Native.posArr m L)).1
    (orbitRecs gens L (CFSG.ONSchreier.Native.posArr m L)).2

@[expose] def burnsideF48t_orbOK (m : ℕ) (gens : Array (Array ℕ)) (root size : ℕ) : Bool :=
  let L := burnsideF48t_bfs m gens root
  L.size == size && L[0]! == root && burnsideF48t_orbCert m gens L

@[expose] def burnsideF48t_inOrb (m : ℕ) (gens : Array (Array ℕ)) (root p : ℕ) : Bool :=
  (burnsideF48t_bfs m gens root).contains p

@[expose] def burnsideF48t_coverOK (m : ℕ) (gens : Array (Array ℕ)) (roots : List ℕ) (lo len : ℕ) :
    Bool :=
  let Ls := roots.map fun r => burnsideF48t_bfs m gens r
  allBelowN len fun p => Ls.any fun L => L.contains (p + lo)

@[expose] def burnsideF48t_closedL (N : ℕ) (gs : Array (Array ℕ)) (E : List (Array ℕ)) : Bool :=
  E.contains (pid N) && E.all fun e => gs.all fun g => E.contains (pcomp N e g)

end Checks

end CFSG.ASVolI
