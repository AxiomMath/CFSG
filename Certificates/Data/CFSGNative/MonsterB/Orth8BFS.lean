module

public section

namespace CFSG.Monster.B.Sp8.Native

@[inline, expose] def pairImg (tab : Array (Array Nat)) (k p : Nat) : Nat :=
  256 * tab[k]![p / 256]! + tab[k]![p % 256]!

@[expose] def pairBFS (tab : Array (Array Nat)) (root : Nat) : Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate 65536 0
  let mut dep : Array Nat := Array.replicate 65536 100000
  dep := dep.set! root 0
  let mut queue : Array Nat := #[root]
  let mut i := 0
  for _ in [0:65536] do
    if i < queue.size then
      let p := queue[i]!
      i := i + 1
      for k in [0:tab.size] do
        let q := pairImg tab k p
        if q < 65536 && dep[q]! == 100000 then
          dep := dep.set! q (dep[p]! + 1)
          par := par.set! q (65536 * k + p)
          queue := queue.push q
  return (par, dep)

@[expose] def pairCheck (tab : Array (Array Nat)) (zero : Array Bool) (root : Nat) : Bool :=
  let r := pairBFS tab root
  r.2[root]! == 0 &&
  (List.range 65536).all fun p =>
    if zero[p / 256]! && zero[p % 256]! && p / 256 != p % 256 && p != root then
      let k := r.1[p]! / 65536
      let q := r.1[p]! % 65536
      decide (k < tab.size) && decide (r.2[q]! < r.2[p]!) && pairImg tab k q == p &&
        zero[q / 256]! && zero[q % 256]! && q / 256 != q % 256
    else true

end CFSG.Monster.B.Sp8.Native
