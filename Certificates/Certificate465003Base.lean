module

public import CFSG.LocalAnalysis.StandardType.L34SylowTabs

@[expose] public section

open CFSG.StandardType.L34Sylow CFSG.PSL3Four.Native

namespace Certificates

structure Facts465003 : Prop where
  card_P : Nat.card ↥(closureTabs pGens) = 9
  P_le_S : closureTabs pGens ≤ closureTabs gensS
  aSix : ∀ j < 6, commutator ↥(closureTabs (pGensWith mRs[j]!)) = ⊤ ∧
    Nonempty (↥(closureTabs (pGensWith mRs[j]!)) ≃* alternatingGroup (Fin 6))
  trichotomy : ∀ Z : Subgroup (Equiv.Perm (Fin 42)), closureTabs pGens ≤ Z →
    Z ≤ closureTabs gensS → Z = closureTabs gensS ∨
      (∃ j < 6, Z = closureTabs (pGensWith mRs[j]!)) ∨ Group.IsSolvable ↥Z
  seven : ∀ Z : Subgroup (Equiv.Perm (Fin 42)), closureTabs pGens ≤ Z →
    Z ≤ closureTabs gensS → (∃ x ∈ Z, x ≠ 1 ∧ x ^ 7 = 1) → Z = closureTabs gensS

end Certificates
