module

public import CFSG.LocalAnalysis.StandardType.GGOmegaPlusRootGenDefs

public section

namespace CFSG.StandardType

namespace OrthTorus

@[expose] def omSigned (p r : ℕ) : Subgroup (MulAut (Fin r → Multiplicative (ZMod p))) :=
  Subgroup.closure (Set.range (SpCoord.permAut (p := p) (k := r)) ∪
    Set.range (SpCoord.sgnAut (p := p) (k := r)))

@[expose] def omStd (r : ℕ) (hr : 2 ≤ r) (k : Fin r) : OmPlusIdx r :=
  if h : k.val + 1 < r then
    (⟨(k, ⟨k.val + 1, h⟩), by rw [Fin.lt_def]; exact Nat.lt_succ_self _⟩, false)
  else
    (⟨(⟨r - 2, by omega⟩, ⟨r - 1, by omega⟩), by rw [Fin.lt_def]; simp only; omega⟩, true)

end OrthTorus

end CFSG.StandardType

end
