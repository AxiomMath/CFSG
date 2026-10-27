
module

public import CFSG.Sporadic.Schreier.J4SFrattiniBase

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.SmallF2.Native

@[expose] def stepNF (p : ℕ × ℕ) : ℕ × ℕ := (p.1 ^^^ app11 elementColumns[p.2]! p.1, squares[p.2]!)

@[expose] def kfun (n e : ℕ) : ℕ :=
  ((List.range 5).find? fun m => stepNF^[m] (n, e) == (0, 0)).getD 5

@[expose] def profCount (b j : ℕ) : ℕ :=
  ∑ e : Fin 1024, if cTable[e.val]! = b / 2 then
    ((Finset.univ : Finset (Fin 2048)).filter fun n =>
      ell n.val = b % 2 ∧ kfun n.val e.val = j).card
    else 0

@[expose] def profTable : Array (Array ℕ) := #[
    #[1, 5119, 56320, 4096, 0],
    #[0, 1536, 47616, 16384, 0],
    #[0, 0, 32768, 32768, 0],
    #[0, 0, 0, 65536, 0],
    #[0, 0, 0, 65536, 0],
    #[0, 0, 0, 0, 65536],
    #[0, 2560, 54784, 8192, 0],
    #[0, 1024, 31744, 32768, 0],
    #[0, 1024, 39936, 24576, 0],
    #[0, 1024, 23552, 40960, 0],
    #[0, 1536, 55808, 8192, 0],
    #[0, 0, 16384, 49152, 0],
    #[0, 1024, 48128, 16384, 0],
    #[0, 0, 16384, 49152, 0],
    #[0, 0, 16384, 49152, 0],
    #[0, 0, 16384, 49152, 0],
    #[0, 1536, 47616, 16384, 0],
    #[0, 0, 24576, 40960, 0],
    #[0, 0, 49152, 16384, 0],
    #[0, 0, 0, 65536, 0],
    #[0, 0, 32768, 32768, 0],
    #[0, 0, 0, 65536, 0],
    #[0, 0, 32768, 32768, 0],
    #[0, 0, 0, 65536, 0],
    #[0, 2560, 46592, 16384, 0],
    #[0, 0, 40960, 24576, 0],
    #[0, 1024, 48128, 16384, 0],
    #[0, 0, 16384, 49152, 0],
    #[0, 0, 32768, 32768, 0],
    #[0, 0, 16384, 49152, 0],
    #[0, 0, 32768, 32768, 0],
    #[0, 0, 16384, 49152, 0]]

end CFSG.Sporadic.J4Schreier
