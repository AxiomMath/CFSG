module

public import CFSG.LocalAnalysis.StandardType.GGQTwoRowDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveQ2PrimeLDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

@[expose] def GGCartanRankLe : Prop :=
  ∀ {G : Type} [Group G] {p N : ℕ} {Bs : Subgroup G},
    p.Prime → p ≠ 2 → IsElemAbelian p Bs → [Finite Bs] →
    ∀ (ρ : Equiv.Perm (Fin N) →* MulAut ↥Bs),
      Function.Injective ρ →
      (∀ a b : Fin N, a ≠ b → GGIsReflection p (ρ (Equiv.swap a b))) →
      (∀ g, ¬ GGIsTransvection p (ρ g)) →
      p ^ (N - 1 - (if p ∣ N then 1 else 0)) ≤ Nat.card Bs

end CFSG.StandardType.QTwo

end
