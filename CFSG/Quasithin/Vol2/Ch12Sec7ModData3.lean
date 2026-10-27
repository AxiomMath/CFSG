module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace CFSG.Quasithin.H13.S127.Mod

@[expose] def ptOf (p : ℕ) : List ℕ := [0, p, wV p, wV (wV p)]

@[expose] def pt1 : List ℕ := [0, 1, 2, 3]

@[expose] def stab1 : List B6 := gm6.filter fun g => g.app 1 == 1

@[expose] def blkC (B : B6) : List ℕ :=
  [(B.c2 >>> 2) % 4, (B.c4 >>> 2) % 4, (B.c2 >>> 4) % 4, (B.c4 >>> 4) % 4]

@[expose] def det2 (B : B6) : ℕ :=
  sV ((B.c2 >>> 2) % 4) ((B.c4 >>> 4) % 4) ^^^ sV ((B.c4 >>> 2) % 4) ((B.c2 >>> 4) % 4)

@[expose] def l1s0p : List B6 := l1.flatMap fun a => s0p.map fun s => a.comp s

@[expose] def l2s0p : List B6 := l2.flatMap fun a => s0p.map fun s => a.comp s

end CFSG.Quasithin.H13.S127.Mod

end
