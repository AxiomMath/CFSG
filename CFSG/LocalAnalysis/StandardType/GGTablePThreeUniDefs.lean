module

public import Mathlib

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix

@[expose] def IsHermIsometry {K : Type} [Field K] {n : ℕ} (q : ℕ) (g : Matrix (Fin n) (Fin n) K) :
    Prop :=
  ∀ v w : Fin n → K, ∑ i, (g *ᵥ v) i ^ q * (g *ᵥ w) i = ∑ i, v i ^ q * w i

end CFSG.StandardType.TablePThreeKG

end
