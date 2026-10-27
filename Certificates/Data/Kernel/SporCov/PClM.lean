module

public import Certificates.Data.Kernel.SporCov.PCl

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def pgHm (E : List Nat → List Nat → Bool) (L : Nat → Bool)
    (gs : List (List Nat)) (m : Nat) (M : List (List Nat)) (nL : Nat) (Y : List (List Nat))
    (nE : Nat) : Bool :=
  lenLe M (2 * nL) && lenLe Y nE && chA L M && chA L Y &&
    allLt m fun j => E (nthW M (2 * j)) (nthW gs j)

@[expose] noncomputable def pgEm (E : List Nat → List Nat → Bool) (L : Nat → Bool) (t : List Nat)
    (H Y Yc M : List (List Nat)) (m e : Nat) : Bool :=
  chW L (nthW H e) && cjOK E t (nthW H e) (nthW Y e) &&
    chW (fun c => Nat.blt c (2 * m)) (nthW Yc e) && E (nthW Y e) (expC M (nthW Yc e))

@[expose] noncomputable def pgLm (E : List Nat → List Nat → Bool) (M Y : List (List Nat))
    (K : List Nat) (m nE j : Nat) : Bool :=
  E (nthW M (2 * j) ++ nthW M (2 * j + 1)) [] &&
    (Nat.blt j m || (Nat.blt (nthN K j) nE && cm E (nthW M (2 * j)) (nthW Y (nthN K j))))

@[expose] noncomputable def pclMOK (E : List Nat → List Nat → Bool) (L : Nat → Bool)
    (gs : List (List Nat)) (m nL nE nR : Nat) (t : List Nat) (M Y H Yc C R : List (List Nat))
    (K : List Nat) : Bool :=
  pgHm E L gs m M nL Y nE && allLt nE (pgEm E L t H Y Yc M m) && allLt nL (pgLm E M Y K m nE) &&
    stH L R nR && allLt nR (stOK E M C R) && chW L t

end CFSG.KC.SporCov

end
