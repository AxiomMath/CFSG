module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylAdjDerived

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

section Main


theorem not_eleven_dvd_two_pow (n : ℕ) : ¬ 11 ∣ 2 ^ n := by
  intro h
  have h2 := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h
  norm_num at h2

theorem sylowAutBoundAll_of_untwisted {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {S : Type} [Group S] [Finite S] {K : Type} [Field K]
    [Finite K] (e : S ≃* AdjointQuotient τ K) (hK : ¬ 11 ∣ Nat.card K) :
    SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) S := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  have h0 : SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) (adjointGroup τ K) :=
    sylowAutBoundAll_adjointGroup hτ hK
  have h1 : SylowAutBoundAll 11 (if τ = .G2 then 6 else 24) (AdjointQuotient τ K) :=
    SylowAutBoundAll.of_surjective (QuotientGroup.mk' (Subgroup.center ↥(adjointGroup τ K)))
      (QuotientGroup.mk'_surjective _) h0
  exact SylowAutBoundAll.of_injective e.toMonoidHom e.injective h1

theorem sylowAutBoundAll_of_derived {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {S : Type} [Group S] [Finite S] {K : Type} [Field K]
    [Finite K] {H : Subgroup (ModGL τ K)} (hH : H ≤ adjointGroup τ K)
    (e : S ≃* DerivedCentralQuotient H) (hK : ¬ 11 ∣ Nat.card K) :
    SylowAutBoundAll 11 24 S := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h1 : SylowAutBoundAll 11 24 (DerivedCentralQuotient H) :=
    sylowAutBoundAll_derivedCentralQuotient hτ hK hH
  exact SylowAutBoundAll.of_injective e.toMonoidHom e.injective h1

theorem lieSylow11Exc_holds : LieSylow11Exc := by
  intro S _ _ f h
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have key : SylowAutBoundAll 11 1152 S := by
    rcases h with h | h | h
    ·
      have h' : UntwistedChevalleyModel S .G2 (2 ^ f) := h.2
      obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := h'
      letI := hKf
      haveI := hKfin
      have hK : ¬ 11 ∣ Nat.card K := by
        rw [hcard]
        exact not_eleven_dvd_two_pow f
      exact (sylowAutBoundAll_of_untwisted (τ := .G2) (Or.inl rfl) e hK).mono (by
        split_ifs <;> norm_num)
    ·
      have h' : TwistedChevalleyModel S TwistTag.D4 (2 ^ f) := h.2
      obtain ⟨K, hKf, hKfin, hcard, σ, -, ⟨e⟩⟩ := h'
      letI := hKf
      haveI := hKfin
      have hK : ¬ 11 ∣ Nat.card K := by
        rw [hcard, ← pow_mul]
        exact not_eleven_dvd_two_pow _
      exact (sylowAutBoundAll_of_derived (τ := TwistTag.D4.tag) (Or.inr (Or.inl rfl))
        (H := twistedFixedGroup TwistTag.D4 K σ) inf_le_left e hK).mono (by norm_num)
    ·
      obtain ⟨a, -, hR⟩ := h.2
      obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := hR
      letI := hKf
      haveI := hKfin
      have hK : ¬ 11 ∣ Nat.card K := by
        rw [hcard]
        exact not_eleven_dvd_two_pow f
      exact (sylowAutBoundAll_of_derived (τ := .F4) (Or.inr (Or.inr rfl))
        (H := reeFixedGroup .F4 K reeF4Perm fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))
        inf_le_left e hK).mono (by norm_num)
  exact (sylowAutBound_iff_all).2 key

theorem ltqtk_conj2_G2 (S : Type) [Group S] [Finite S] (p : ℕ)
    (hp11 : p ≠ 11) (h : ChevalleyExceptionalModel S .G2 p 1) : SylowAutBound 11 24 S := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hp : p.Prime := h.1.1
  have h' : UntwistedChevalleyModel S .G2 (p ^ 1) := h.2
  obtain ⟨K, hKf, hKfin, hcard, ⟨e⟩⟩ := h'
  letI := hKf
  haveI := hKfin
  have hK : ¬ 11 ∣ Nat.card K := by
    rw [hcard, pow_one]
    intro hd
    have h11p : 11 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).1 hd
    exact hp11 h11p.symm
  have h24 : SylowAutBoundAll 11 24 S :=
    (sylowAutBoundAll_of_untwisted (τ := .G2) (Or.inl rfl) e hK).mono (by split_ifs <;> norm_num)
  exact sylowAutBound_iff_all.2 h24

end Main

end CFSG.Quasithin.KGC31
