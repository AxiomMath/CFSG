module

public import CFSG.Monster.GMS.Facts.Co1OddPairs

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

@[expose] def FourPattern (a b ω : Fin 24 → ZMod 2) : Prop :=
  a ∈ co1Orbit 0 ∧ b ∈ co1Orbit 0 ∧ a + b ∈ co1Orbit 0 ∧ ω ∈ co1Orbit 2 ∧ ω + a ∈ co1Orbit 2 ∧
    ω + b ∈ co1Orbit 2 ∧ ω + a + b ∈ co1Orbit 2

@[expose] def Co1FourU : Prop :=
  ∀ r s : Co1, IsCo1TwoA r → IsCo1TwoA s → r * s = s * r → IsCo1TwoA (r * s) →
    ∃ v ∈ co1Orbit 2, (∃ p, v = p + co1Act r p) ∧ (∃ p, v = p + co1Act s p) ∧
      ∃ p, v = p + co1Act (r * s) p

@[expose] def Co1FourT : Prop :=
  ∀ a b ω a' b' ω' : Fin 24 → ZMod 2, FourPattern a b ω → FourPattern a' b' ω' →
    ∃ g : Co1, co1Act g a = a' ∧ co1Act g b = b' ∧
      (co1Act g ω = ω' ∨ co1Act g ω = ω' + a' ∨ co1Act g ω = ω' + b' ∨
        co1Act g ω = ω' + a' + b')

end S365

end CFSG.Monster.GMS
