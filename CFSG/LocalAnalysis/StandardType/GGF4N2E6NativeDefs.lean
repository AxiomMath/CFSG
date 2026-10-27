module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.StandardType.N2E6Native

open CFSG.Blueprint.Chevalley
open scoped Matrix

@[expose] def e6NativePair (l m : Fin Tag.E6.rank → ℤ) : ℤ :=
  ∑ k, ∑ j, l k * Tag.E6.cartan k j * m j

@[expose] def e6NativeGamma : Fin 4 → Fin Tag.E6.rank → ℤ :=
  ![![1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 1], ![1, 2, 2, 3, 2, 1]]

@[expose] def e6NativeW (l : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  l - ∑ i, e6NativePair l (e6NativeGamma i) • e6NativeGamma i

@[expose] def e6NativeChar (a : Fin 4 → ℤ) (k : Fin Tag.E6.rank) : ℤ :=
  ∑ i, a i * ∑ j, Tag.E6.cartan k j * e6NativeGamma i j

theorem e6NativePair_gamma (i j : Fin 4) :
    e6NativePair (e6NativeGamma i) (e6NativeGamma j) = if i = j then 2 else 0 := by
  revert i j
  decide

@[expose] def e6NativeWMat : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![-1, -1, 1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, -2, 1, 0, 0, 0; 0, -2, 1, -1, 1, 0;
    0, -2, 0, 0, 1, 0; 0, -1, 0, 0, 1, -1]

theorem e6NativeW_single (k : Fin Tag.E6.rank) :
    e6NativeW (Pi.single k 1) = fun t => e6NativeWMat t k := by
  revert k
  decide

end CFSG.StandardType.N2E6Native

end
