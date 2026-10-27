module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

namespace CFSG.StandardType

@[expose] def bSignedFull (n p : ℕ) : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | (∃ i : Fin n, r = SpCoord.sgnAut i) ∨
    (∃ a b : Fin n, a ≠ b ∧ r = SpCoord.permAut (Equiv.swap a b))}

@[expose] def bCoordinateBlock (n p : ℕ) (i0 : Fin n) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | (∃ i : Fin n, i ≠ i0 ∧ r = SpCoord.sgnAut i) ∨
    (∃ a b : Fin n, a ≠ b ∧ a ≠ i0 ∧ b ≠ i0 ∧ r = SpCoord.permAut (Equiv.swap a b))}

@[expose] def dCoordinateBlock (n p : ℕ) (i0 : Fin n) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | (∃ a b : Fin n, a ≠ b ∧ a ≠ i0 ∧ b ≠ i0 ∧
      r = SpCoord.permAut (Equiv.swap a b)) ∨
    (∃ a b : Fin n, a ≠ b ∧ a ≠ i0 ∧ b ≠ i0 ∧
      r = SpCoord.sgnAut a * SpCoord.permAut (Equiv.swap a b) * (SpCoord.sgnAut a)⁻¹)}

@[expose] def aPermutationFull (n p : ℕ) : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | ∃ a b : Fin n, a ≠ b ∧ r = SpCoord.permAut (Equiv.swap a b)}

@[expose] def bBlockOn (n p : ℕ) (I : Finset (Fin n)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | (∃ i ∈ I, r = SpCoord.sgnAut i) ∨
    (∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ r = SpCoord.permAut (Equiv.swap a b))}

@[expose] def dBlockOn (n p : ℕ) (I : Finset (Fin n)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | (∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ r = SpCoord.permAut (Equiv.swap a b)) ∨
    (∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧
      r = SpCoord.sgnAut a * SpCoord.permAut (Equiv.swap a b) * (SpCoord.sgnAut a)⁻¹)}

@[expose] def aPermutationOn (n p : ℕ) (I : Finset (Fin n)) :
    Subgroup (MulAut (Fin n → Multiplicative (ZMod p))) :=
  Subgroup.closure {r | ∃ a ∈ I, ∃ b ∈ I, a ≠ b ∧ r = SpCoord.permAut (Equiv.swap a b)}

@[expose] def IsSignedBlockOn (n p : ℕ) (I : Finset (Fin n))
    (Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) : Prop :=
  Γ = bBlockOn n p I ∨ (2 ≤ I.card ∧ Γ = dBlockOn n p I) ∨
    ∃ (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1),
      Γ = (aPermutationOn n p I).map (MulAut.conj (SpCoord.diagAut d hd)).toMonoidHom

end CFSG.StandardType

end
