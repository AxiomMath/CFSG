module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdx
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrameLemmas

public section

namespace CFSG.HardMathSupport.C14Idx

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.C14Exc
  CFSG.LieType.Ree

@[expose] def IsReeConj
    {L : Type} [Field L] [CharP L ReeTag.F4.prime] (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ)
    (h : adjointGroup ReeTag.F4.tag L)
    (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L) : Prop :=
  ∀ g, F' g = h * ReeTag.F4.reeEndo L hf a₀ (h⁻¹ * g * h) * h⁻¹

@[expose] def ExcF4PowSixInput :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] {ι : Type} (a : ι → Fin Tag.F4.rank → Lˣ)
    (g : adjointGroup Tag.F4 L), (g : ModGL Tag.F4 L) ∈ famZ a → g ∈ famS a → g ^ 6 = 1

@[expose] def ExcIdxReeInput :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime] {ι : Type} (p : ℕ), p.Prime →
    p ≠ 2 → ∀ (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ)
      (h : adjointGroup ReeTag.F4.tag L)
      (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L),
      IsReeConj hf a₀ h F' → (∀ g ∈ famM a, F' g ∈ famM a) →
      Finite ↥(F'.eqLocus (MonoidHom.id _)) → CorootPSaturated p (familyKernel a) →
        IdxConclusion p a F'

@[expose] def ExcReeCentralStab
     : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime] {ι : Type}
    (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ)
    (h : adjointGroup ReeTag.F4.tag L)
    (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L),
    IsReeConj hf a₀ h F' → (∀ g ∈ famM a, F' g ∈ famM a) →
      (∀ g : adjointGroup ReeTag.F4.tag L, (g : ModGL ReeTag.F4.tag L) ∈ famZ a →
        (F' g : ModGL ReeTag.F4.tag L) ∈ famZ a) ∧
      ∀ g : adjointGroup ReeTag.F4.tag L,
        (g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) →
          (F' g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a)

theorem exc_not_dvd_card_of_exponent
    {τ : Tag} {L : Type} [Field L]
    {ι : Type} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (a : ι → Fin τ.rank → Lˣ)
    (hfin : Finite {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a})
    (hexp : ∀ g : adjointGroup τ L, (g : ModGL τ L) ∈ famZ a → g ∈ famS a → g ^ 6 = 1) :
    ¬ p ∣ Nat.card {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a} := by
  set H : Subgroup (adjointGroup τ L) := (famZ a).comap (adjointGroup τ L).subtype ⊓ famS a
  have hH : Nat.card {g : adjointGroup τ L // (g : ModGL τ L) ∈ famZ a ∧ g ∈ famS a} =
      Nat.card H := rfl
  rw [hH]
  haveI : Finite H := hfin
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h6 : x ^ 6 = 1 := Subtype.ext (hexp x.1 x.2.1 x.2.2)
  have hp6 : p ∣ 2 * 3 := hx ▸ orderOf_dvd_of_pow_eq_one h6
  rcases (Nat.Prime.dvd_mul hp).1 hp6 with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

theorem exc_not_dvd_card_F4_of_input
    (hBor : ExcBorelInput)
    (hF4 : ExcF4PowSixInput) {L : Type} [Field L] [IsAlgClosed L] {ι : Type} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (a : ι → Fin Tag.F4.rank → Lˣ) :
    ¬ p ∣ Nat.card {g : adjointGroup Tag.F4 L // (g : ModGL Tag.F4 L) ∈ famZ a ∧ g ∈ famS a} :=
  exc_not_dvd_card_of_exponent hp hp2 hp3 a (hBor Tag.F4 L a).2.2.1 (hF4 L a)

end CFSG.HardMathSupport.C14Idx
