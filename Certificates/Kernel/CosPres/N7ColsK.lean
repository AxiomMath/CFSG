module

public import Certificates.Data.Kernel.N7ModClass
public import Certificates.Kernel.Census.N6.ColsK

public section

namespace CFSG.KernelN7

open CFSG.CGT.T75JM CFSG.CGT.T75M23 CFSG.KernelN6

@[expose] noncomputable def relCB7K (X Y : Cols) : Bool :=
  eqC (compK X X) idC && !eqC X idC && eqC (powK Y 5) idC &&
    eqC (powK (compK X (compK Y (compK X (powK Y 4)))) 3) idC &&
    eqC (powK (compK (powK Y 4) X) 7) idC &&
    eqC (compK X (compK Y (compK X (compK (powK (compK Y (compK X (compK (powK Y 4)
      (compK X Y)))) 2) (compK Y (compK X (powK Y 4))))))) idC

@[expose] noncomputable def equivB7K (X Y Q Qi : Cols) : Bool :=
  smallB Q && smallB Qi && eqC (compK Qi Q) idC && eqC (compK Q Qi) idC &&
    eqC (compK X Q) (compK Q modelX7) && eqC (compK Y Q) (compK Q modelY7)

@[expose] noncomputable def relB7K (r n : ℕ) : Bool := relCB7K (repC7 r) (unpackK n)

@[expose] noncomputable def invRecOK7K (e : ℕ) : Bool :=
  eqC (compK (unpackK (e / 65536 ^ 2 % 65536)) (unpackK (e / 65536 % 65536))) idC &&
    eqC (compK (unpackK (e / 65536 % 65536)) (unpackK (e / 65536 ^ 2 % 65536))) idC &&
    eqC (cjK (unpackK (e / 65536 % 65536)) (unpackK (e / 65536 ^ 2 % 65536)) (unpackK (e % 65536)))
      (repC7 (e / 65536 ^ 3))

@[expose] noncomputable def relRecOK7K (e : ℕ) : Bool :=
  equivB7K modelX7
    (if e / 65536 ^ 3 = 0 then unpackK (e % 65536)
      else evalK modelX7 (unpackK (e % 65536)) twistWord7)
    (unpackK (e / 65536 % 65536)) (unpackK (e / 65536 ^ 2 % 65536))

@[expose] noncomputable def invAll7K (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter isInvK) (L.map (· % 65536)) && L.all invRecOK7K

@[expose] noncomputable def relAll7K (r : ℕ) (L : List ℕ) : Bool :=
  eqNL ((List.range' 0 65536).filter (relB7K r)) (L.map (· % 65536)) && L.all relRecOK7K

theorem relB7_eq (r : ℕ) : relB7 r = relB7K r := funext fun n => by
  simp only [relB7, relB7K, relCB7, relCB7K, compC_eq, powC_eq, unpackC_eq]

theorem invRecOK7_eq : invRecOK7 = invRecOK7K := funext fun e => by
  simp only [invRecOK7, invRecOK7K, cjC_eq, compC_eq, unpackC_eq]

theorem relRecOK7_eq : relRecOK7 = relRecOK7K := funext fun e => by
  simp only [relRecOK7, relRecOK7K, equivB7, equivB7K, compC_eq, unpackC_eq, evalC_eq]

theorem invAll7_eqK (L : List ℕ) : invAll7 L = invAll7K L := by
  rw [invAll7, invAll7K, isInvB_eq, invRecOK7_eq]

theorem relAll7_eqK (r : ℕ) (L : List ℕ) : relAll7 r L = relAll7K r L := by
  rw [relAll7, relAll7K, relB7_eq, relRecOK7_eq]

end CFSG.KernelN7
