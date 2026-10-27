module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSys
public import Mathlib.Data.Finset.Sort

public section

namespace CFSG.Quasithin.Fan86.Tutte

variable {H : Type*} [Group H]

@[expose] def nfw (r l : H) (e : ℤ) : List ℤ → H
  | [] => 1
  | t :: L => tx r l t ^ e * nfw r l (-e) L

@[expose] def Abel (Hs : ℕ → Subgroup H) (k : ℕ) : Prop :=
  ∀ a ∈ Hs k, ∀ b ∈ Hs k, a * b = b * a

@[expose] def pset (r l : H) (T : Finset ℕ) : H :=
  ((T.sort (· ≤ ·)).map fun t => tx r l t).prod

end CFSG.Quasithin.Fan86.Tutte
