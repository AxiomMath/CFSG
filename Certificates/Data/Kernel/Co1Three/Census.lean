module

public import Certificates.Data.Kernel.Co1Three.Moore

public section

namespace CFSG.KC.Co1Census

open CFSG.KC.Co1B

@[expose] noncomputable def getK (M : Nat → Nat) (N k : Nat) : Nat := if k < N then M k else oneK

@[expose] noncomputable def a0K (d₀ d₁ d₂ k : Nat) : Nat :=
  mulWK (powWK d₀ (k % 5)) (mulWK (powWK d₁ ((k / 5) % 5)) (powWK d₂ (k / 25)))

@[expose] noncomputable def stepK (n nI a : Nat → Nat) (cov : List Nat) (s : Nat × Nat × Nat) :
    Bool :=
  cov.contains s.2.1 && decide (s.1 < 125) && decide (s.2.2 < 3) &&
    eqK (mulWK (mulWK (n (88 + s.2.2)) (a s.2.1)) (nI (88 + s.2.2))) (a s.1)

@[expose] noncomputable def chainK (n nI a : Nat → Nat) (cov : List Nat)
    (steps : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun s _ ih cov => stepK n nI a cov s && ih (s.1 :: cov)) steps cov

@[expose] noncomputable def censusK (n nI a : Nat → Nat) (P₀ P₁ PZ : Nat)
    (steps : List (Nat × Nat × Nat)) : Bool :=
  eqK (a 1) P₀ && eqK (a 5) P₁ && eqK (a 6) PZ && chainK n nI a [1, 5, 6] steps &&
    (List.range 125).all fun k =>
      k == 0 || k == 1 || k == 5 || k == 6 || steps.any fun s => s.1 == k

end CFSG.KC.Co1Census

end
