module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.SzN31

namespace SmD6Heis

open CFSG.Open

section SylowContaining

variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_two_containing {N S₀ : Subgroup G} (hS₀N : S₀ ≤ N) (hS₀c : Nat.card S₀ = 16)
    (hS₀iso : Nonempty (↥S₀ ≃* SemidihedralGroup 4))
    (hUB : ∀ T : Subgroup G, IsPGroup 2 T → T ≤ N → Nat.card T ∣ 16)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTN : T ≤ N) :
    ∃ S : Subgroup G, T ≤ S ∧ CFSG.QuasithinUnique.IsSylowTwoOf S N ∧
      Nonempty (↥S ≃* SemidihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁ : IsPGroup 2 (T.subgroupOf N) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTN).symm
  have hS₁ : IsPGroup 2 (S₀.subgroupOf N) :=
    IsPGroup.of_card (n := 4) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀N).toEquiv, hS₀c]
      norm_num)
  obtain ⟨R, hR⟩ := hT₁.exists_le_sylow
  obtain ⟨Q₀, hQ₀⟩ := hS₁.exists_le_sylow
  have hQ₀card : Nat.card (Q₀ : Subgroup ↥N) ≤ Nat.card (S₀.subgroupOf N) := by
    have hdvd := hUB ((Q₀ : Subgroup ↥N).map N.subtype) (Q₀.isPGroup'.map N.subtype)
      (Subgroup.map_subtype_le _)
    rw [Subgroup.card_map_of_injective N.subtype_injective] at hdvd
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₀N).toEquiv, hS₀c]
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hQ₀eq : S₀.subgroupOf N = (Q₀ : Subgroup ↥N) := Subgroup.eq_of_le_of_card_ge hQ₀ hQ₀card
  refine ⟨(R : Subgroup ↥N).map N.subtype, ?_,
    ⟨Subgroup.map_subtype_le _, R.isPGroup'.map N.subtype, ?_⟩, ?_⟩
  · intro t ht
    have : (⟨t, hTN ht⟩ : ↥N) ∈ (R : Subgroup ↥N) := hR (Subgroup.mem_subgroupOf.2 ht)
    exact ⟨_, this, rfl⟩
  · show ¬ 2 ∣ (((R : Subgroup ↥N).map N.subtype).comap N.subtype).index
    rw [Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    exact R.not_dvd_index
  · obtain ⟨e⟩ := hS₀iso
    have e1 : ↥((R : Subgroup ↥N).map N.subtype) ≃* ↥(R : Subgroup ↥N) :=
      (Subgroup.equivMapOfInjective (R : Subgroup ↥N) N.subtype N.subtype_injective).symm
    have e2 : ↥(R : Subgroup ↥N) ≃* ↥(Q₀ : Subgroup ↥N) := Sylow.equiv R Q₀
    have e3 : ↥(Q₀ : Subgroup ↥N) ≃* ↥(S₀.subgroupOf N) := MulEquiv.subgroupCongr hQ₀eq.symm
    have e4 : ↥(S₀.subgroupOf N) ≃* ↥S₀ := Subgroup.subgroupOfEquivOfLe hS₀N
    exact ⟨((e1.trans e2).trans e3).trans (e4.trans e)⟩

end SylowContaining

section Complement

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_sylow_complement (P : Subgroup Γ) (hP : Nat.card P = 27) (hi : P.index ∣ 16)
    {B : Subgroup Γ} (hB : IsPGroup 2 B) :
    ∃ T : Subgroup Γ, B ≤ T ∧ IsPGroup 2 T ∧ ∀ g : Γ, ∃ p ∈ P, ∃ t ∈ T, g = p * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := hB.exists_le_sylow
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show P.index ∣ 2 ^ 4 by simpa using hi)
  have hΓ : Nat.card Γ = 27 * 2 ^ b := by
    rw [← hP, ← hb]
    exact (Subgroup.card_mul_index P).symm
  have hTcard : Nat.card (T : Subgroup Γ) = 2 ^ b := by
    rw [T.card_eq_multiplicity, hΓ]
    have : (27 * 2 ^ b).factorization 2 = b := by
      rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num), zero_add,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    rw [this]
  have hcomp : P.IsComplement' (T : Subgroup Γ) := by
    refine Subgroup.isComplement'_of_coprime ?_ ?_
    · rw [hP, hTcard, hΓ]
    · rw [hP, hTcard]
      exact Nat.Coprime.pow_right b (by norm_num)
  refine ⟨T, hT, T.isPGroup', fun g => ?_⟩
  obtain ⟨⟨p, t⟩, hpt⟩ := hcomp.2 g
  exact ⟨p, p.2, t, t.2, hpt.symm⟩

end Complement

end SmD6Heis

end CFSG.Quasithin.SzN31
