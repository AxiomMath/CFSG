module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

structure Facts134Five : Prop where
  alt : NoE25Config fun (X : Type) [Group X] =>
    ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (X ≃* alternatingGroup (Fin n))
  psl2Odd : ∀ p f : ℕ, p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 p f
  psl2Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n
  psl3Odd : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1
  psu3Odd : ∀ p : ℕ, p.Prime → p ≠ 2 →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1
  psl3Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n
  psu3Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n
  psp4Even : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A),
    StatedClassicalModel ↥L .PSp 2 2 n → E25Config L P T → EmptyFaithfulMultiple.AutCyclic T P
  g2Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n
  d4Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n
  f4Even : ∀ n : ℕ,
    NoE25Config fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n
  sz : ∀ n : ℕ, NoE25Config fun (X : Type) [Group X] => SuzukiModel X 2 n
  tits : NoE25Config fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1
  psl45 : ∀ n : ℕ, (n = 4 ∨ n = 5) →
    NoE25Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1
  m11 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M11)
  m12 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12)
  m22 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22)
  m23 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23)
  m24 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24)
  j1 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1)
  j2 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2)
  j4 : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)
  hs : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS)
  he : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He)
  ru : NoE25Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru)

end CFSG.Quasithin.S146zY
