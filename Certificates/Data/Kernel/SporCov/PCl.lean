module

public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.Census

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def pgH (E : List Nat → List Nat → Bool) (L : Nat → Bool) (g₁ g₂ : List Nat)
    (M : List (List Nat)) (nL : Nat) (Y : List (List Nat)) (nE : Nat) : Bool :=
  lenLe M (2 * nL) && lenLe Y nE && chA L M && chA L Y && E (nthW M 0) g₁ && E (nthW M 2) g₂

@[expose] noncomputable def pgE (E : List Nat → List Nat → Bool) (L : Nat → Bool) (t : List Nat)
    (H Y Yc M : List (List Nat)) (e : Nat) : Bool :=
  chW L (nthW H e) && cjOK E t (nthW H e) (nthW Y e) &&
    chW (fun c => Nat.blt c (nat_lit 4)) (nthW Yc e) && E (nthW Y e) (expC M (nthW Yc e))

@[expose] noncomputable def pgL (E : List Nat → List Nat → Bool) (M Y : List (List Nat))
    (K : List Nat) (nE j : Nat) : Bool :=
  E (nthW M (2 * j) ++ nthW M (2 * j + 1)) [] &&
    (Nat.blt j (nat_lit 2) || (Nat.blt (nthN K j) nE && cm E (nthW M (2 * j)) (nthW Y (nthN K j))))

@[expose] noncomputable def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && f k) n

@[expose] noncomputable def lnW (g₁ g₂ : List Nat) (p i : Nat) : List Nat :=
  cond (Nat.blt i p) (repW g₂ i ++ g₁) g₂

@[expose] noncomputable def pclOK (E : List Nat → List Nat → Bool) (L : Nat → Bool)
    (nL nE nR : Nat) (g₁ g₂ t : List Nat) (M Y H Yc C R : List (List Nat)) (K : List Nat) : Bool :=
  pgH E L g₁ g₂ M nL Y nE && allLt nE (pgE E L t H Y Yc M) && allLt nL (pgL E M Y K nE) &&
    stH L R nR && allLt nR (stOK E M C R) && chW L t

@[expose] noncomputable def p3cOK (E : List Nat → List Nat → Bool) (L : Nat → Bool)
    (p e₁ e₂ nL nE nR : Nat) (g₁ g₂ z t gz : List Nat) (M Y H Yc C R : List (List Nat))
    (K : List Nat) : Bool :=
  p3OK E L p g₁ g₂ z e₁ e₂ && pclOK E L nL nE nR g₁ g₂ t M Y H Yc C R K && chW L gz &&
    cjOK E t gz z

@[expose] noncomputable def p3lOK (E : List Nat → List Nat → Bool) (L : Nat → Bool)
    (p e₁ e₂ nL nE nR : Nat) (g₁ g₂ z t : List Nat) (M Y H Yc C R : List (List Nat))
    (K A : List Nat) (W : List (List Nat)) : Bool :=
  p3OK E L p g₁ g₂ z e₁ e₂ && pclOK E L nL nE nR g₁ g₂ t M Y H Yc C R K &&
    allLt (Nat.succ p) fun i =>
      chW L (nthW W i) && cjOK E (repW t (nthN A i)) (nthW W i) (lnW g₁ g₂ p i)

end CFSG.KC.SporCov

end
