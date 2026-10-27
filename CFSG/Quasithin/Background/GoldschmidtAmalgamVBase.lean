module

public import CFSG.Quasithin.Background.F6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

structure IsGoldschmidtVTriple {D : Type*} [Group D] (G₁ G₂ : Subgroup D) : Prop where
  gen : G₁ ⊔ G₂ = ⊤
  quotient₁ : Nonempty (↥G₁ ⧸ Open.pCore 2 ↥G₁ ≃* Equiv.Perm (Fin 3))
  quotient₂ : Nonempty (↥G₂ ⧸ Open.pCore 2 ↥G₂ ≃* Equiv.Perm (Fin 3))
  sylow₁ : IsSylowTwoOf (G₁ ⊓ G₂) G₁
  sylow₂ : IsSylowTwoOf (G₁ ⊓ G₂) G₂

structure IsGoldschmidtVAmalgam {D : Type*} [Group D] (G₁ G₂ : Subgroup D) : Prop
    extends IsGoldschmidtVTriple G₁ G₂ where
  pCore_eq_bot : Open.pCore 2 D = ⊥

namespace GoldPair

variable {D : Type*} [Group D]

theorem relIndex_eq_three [Finite D] {X S : Subgroup D}
    (e : Nonempty (↥X ⧸ Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3))) (hS : IsSylowTwoOf S X) :
    S.relIndex X = 3 := by
  obtain ⟨e⟩ := e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).exists_card_eq
  have hcardQ : Nat.card (↥X ⧸ Open.pCore 2 ↥X) = 6 := by
    rw [Nat.card_congr e.toEquiv, gold_card_perm_fin_three]
  have hX : Nat.card ↥X = 3 * 2 ^ (k + 1) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥X)
    rw [this, hcardQ, hk]
    ring
  obtain ⟨m, hm⟩ := hS.2.1.exists_card_eq
  have hmul : S.relIndex X * Nat.card ↥S = Nat.card ↥X := by
    have := Subgroup.relIndex_mul_card S X
    rwa [inf_of_le_left hS.1] at this
  have hcop : Nat.Coprime (S.relIndex X) (2 ^ (k + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hS.2.2).symm
  have hdvd : S.relIndex X ∣ 3 * 2 ^ (k + 1) := ⟨Nat.card ↥S, by rw [← hX, ← hmul]⟩
  have h3 : S.relIndex X ∣ 3 := hcop.dvd_of_dvd_mul_right hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
  · exfalso
    rw [h1, hX, hm, one_mul] at hmul
    have : 3 ∣ 2 ^ m := ⟨2 ^ (k + 1), by rw [hmul]⟩
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
    omega
  · exact h1

theorem card_eq_three_mul [Finite D] {X S : Subgroup D}
    (e : Nonempty (↥X ⧸ Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3))) (hS : IsSylowTwoOf S X) :
    Nat.card ↥X = 3 * Nat.card ↥S := by
  have := Subgroup.relIndex_mul_card S X
  rw [relIndex_eq_three e hS, inf_of_le_left hS.1] at this
  exact this.symm

omit [Group D] in
theorem card_eq_six_mul_pCoreOf {D : Type*} [Group D] {X : Subgroup D}
    (e : Nonempty (↥X ⧸ Open.pCore 2 ↥X ≃* Equiv.Perm (Fin 3))) :
    Nat.card ↥X = 6 * Nat.card ↥(pCoreOf 2 X) := by
  obtain ⟨e⟩ := e
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 ↥X)
  rw [Nat.card_congr e.toEquiv, gold_card_perm_fin_three] at h1
  have h2 : Nat.card ↥(pCoreOf 2 X) = Nat.card ↥(Open.pCore 2 ↥X) :=
    Nat.card_congr ((Open.pCore 2 ↥X).equivMapOfInjective X.subtype
      X.subtype_injective).toEquiv.symm
  rw [h2]
  exact h1

end GoldPair

namespace IsGoldschmidtVTriple

variable {D : Type*} [Group D] {G₁ G₂ : Subgroup D}

theorem isPGroup_inf (h : IsGoldschmidtVTriple G₁ G₂) : IsPGroup 2 ↥(G₁ ⊓ G₂) :=
  h.sylow₁.2.1

theorem symm (h : IsGoldschmidtVTriple G₁ G₂) : IsGoldschmidtVTriple G₂ G₁ where
  gen := by rw [sup_comm]; exact h.gen
  quotient₁ := h.quotient₂
  quotient₂ := h.quotient₁
  sylow₁ := by rw [inf_comm]; exact h.sylow₂
  sylow₂ := by rw [inf_comm]; exact h.sylow₁

theorem relIndex_inf_left [Finite D] (h : IsGoldschmidtVTriple G₁ G₂) :
    (G₁ ⊓ G₂).relIndex G₁ = 3 :=
  GoldPair.relIndex_eq_three h.quotient₁ h.sylow₁

theorem relIndex_inf_right [Finite D] (h : IsGoldschmidtVTriple G₁ G₂) :
    (G₁ ⊓ G₂).relIndex G₂ = 3 :=
  GoldPair.relIndex_eq_three h.quotient₂ h.sylow₂

theorem le_pCore_of_normal_le_inf (h : IsGoldschmidtVTriple G₁ G₂) {N : Subgroup D}
    [N.Normal] (hN : N ≤ G₁ ⊓ G₂) : N ≤ Open.pCore 2 D :=
  le_pCore 2 inferInstance (h.isPGroup_inf.to_le hN)

end IsGoldschmidtVTriple

namespace IsGoldschmidtVAmalgam

variable {D : Type*} [Group D] {G₁ G₂ : Subgroup D}

theorem symm (h : IsGoldschmidtVAmalgam G₁ G₂) : IsGoldschmidtVAmalgam G₂ G₁ :=
  ⟨h.toIsGoldschmidtVTriple.symm, h.pCore_eq_bot⟩

end IsGoldschmidtVAmalgam

theorem _root_.CFSG.Quasithin.IsGoldschmidtTriple.toVTriple {D : Type*} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) : IsGoldschmidtVTriple G₁ G₂ :=
  ⟨h.gen, h.quotient₁, h.quotient₂, isSylowTwoOf_inf_left h, isSylowTwoOf_inf_right h⟩

theorem _root_.CFSG.Quasithin.IsGoldschmidtAmalgam.toVAmalgam {D : Type*} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtAmalgam G₁ G₂) : IsGoldschmidtVAmalgam G₁ G₂ :=
  ⟨h.toIsGoldschmidtTriple.toVTriple, h.pCore_eq_bot⟩

end F6

end CFSG.Quasithin
