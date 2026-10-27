module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBDatum

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord

namespace TypeDDatum

@[expose] def evenSignedSupportedAut (m p : ℕ) (S : Finset (Fin m)) :
    Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
  Subgroup.closure ({σ | ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ σ = permAut (p := p) (Equiv.swap a b)} ∪
    {σ | ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ σ = sgnAut (p := p) a * sgnAut (p := p) b})

@[expose] def evenSignedAut (m p : ℕ) : Subgroup (MulAut (Fin m → Multiplicative (ZMod p))) :=
  evenSignedSupportedAut m p Finset.univ

@[expose] def typeDSimple (m p : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    MulAut (Fin m → Multiplicative (ZMod p)) :=
  if hi : i.val + 1 < m then permAut (p := p) (Equiv.swap i ⟨i.val + 1, hi⟩)
  else permAut (p := p) (Equiv.swap ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩) *
    (sgnAut (p := p) ⟨m - 2, by omega⟩ * sgnAut (p := p) ⟨m - 1, by omega⟩)

end TypeDDatum

end CFSG.StandardType

end
