module

public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def AutSylowSelfNorm (Q : Type) [Group Q] : Prop :=
  ∀ A S : Subgroup (MulAut Q), (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A →
    Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A ≤ S

@[expose] def AutOddNormCent (Q : Type) [Group Q] : Prop :=
  ∀ A S : Subgroup (MulAut Q), (MulAut.conj : Q →* MulAut Q).range ≤ A → IsSylowTwoOf S A →
    ∀ d ∈ Subgroup.normalizer (S : Set (MulAut Q)) ⊓ A, Odd (orderOf d) →
      ∀ s ∈ S, d * s = s * d

theorem AutSylowSelfNorm.autOddNormCent {Q : Type} [Group Q] (h : AutSylowSelfNorm Q) :
    AutOddNormCent Q := by
  intro A S hA hS d hd hodd s _
  have hdS : d ∈ S := h A S hA hS hd
  have hd1 : d = 1 := by
    obtain ⟨k, hk⟩ := hS.2.1 ⟨d, hdS⟩
    have h1 : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    rcases i with _ | i
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · exfalso
      obtain ⟨m, hm⟩ := hodd
      rw [hi, pow_succ] at hm
      omega
  rw [hd1, one_mul, mul_one]

@[expose] def FactAutSylowL42 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 4 2 1 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowL52 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 5 2 1 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowA7 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsAlt 7 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowM11 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .M11 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowM22 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .M22 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowM23 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .M23 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowM24 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .M24 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowJ4 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .J4 Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowHS : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .HS Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowRu : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsSporadic .Ru Q → AutSylowSelfNorm Q

@[expose] def FactAutSylowL2Sq : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 2 p 2 Q →
    AutSylowSelfNorm Q

@[expose] def FactAutU35 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsPSU 3 5 1 Q → AutOddNormCent Q

end CFSG.Quasithin.H13
