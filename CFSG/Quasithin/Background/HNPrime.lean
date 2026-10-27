module

public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open
open scoped Pointwise

section Map

variable {M M' : Type*} [Group M] [Group M']

theorem nPrime_set_map_of_injective {f : M →* M'} (hf : Function.Injective f) (X : Subgroup M) :
    {c : ℕ | ∃ Y B S : Subgroup M', Y ≤ B ∧ B ≤ X.map f ∧ IsCyclic Y ∧ Nat.card Y = 2 ^ c - 1 ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧ IsSylowIn 2 S (X.map f) ∧
      (B : Set M') * (S : Set M') = (S : Set M') * (B : Set M')} =
    {c : ℕ | ∃ Y B S : Subgroup M, Y ≤ B ∧ B ≤ X ∧ IsCyclic Y ∧ Nat.card Y = 2 ^ c - 1 ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Odd (Nat.card B) ∧ IsSylowIn 2 S X ∧
      (B : Set M) * (S : Set M) = (S : Set M) * (B : Set M)} := by
  have hcard : ∀ K : Subgroup M, Nat.card (K.map f) = Nat.card K := fun K =>
    Subgroup.card_map_of_injective hf
  have hset : ∀ K : Subgroup M, ((K.map f : Subgroup M') : Set M') = f '' (K : Set M) :=
    fun K => Subgroup.coe_map f K
  ext c
  constructor
  · rintro ⟨Y', B', S', hYB, hBX, hYc, hYcard, hBab, hBodd, hS, hBS⟩
    have hrange : ∀ {K : Subgroup M'}, K ≤ X.map f → (K.comap f).map f = K := fun hK =>
      Subgroup.map_comap_eq_self (hK.trans (Subgroup.map_le_range f X))
    have hB' := hrange hBX
    have hY' := hrange (hYB.trans hBX)
    have hS' := hrange hS.1
    refine ⟨Y'.comap f, B'.comap f, S'.comap f, Subgroup.comap_mono hYB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, hyx⟩ := hBX hx
      rwa [hf hyx] at hy
    · have e : ↥(Y'.comap f) ≃* ↥Y' :=
        (Subgroup.equivMapOfInjective (Y'.comap f) f hf).trans (MulEquiv.subgroupCongr hY')
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    · rw [← hcard, hY', hYcard]
    · intro a ha b hb
      exact hf (by rw [map_mul, map_mul, hBab _ ha _ hb])
    · rw [← hcard, hB']
      exact hBodd
    · rw [← E1.isSylowIn_map_of_injective hf, hS']
      exact hS
    · apply Set.image_injective.mpr hf
      rw [Set.image_mul, Set.image_mul, ← hset, ← hset, hB', hS', hBS]
  · rintro ⟨Y, B, S, hYB, hBX, hYc, hYcard, hBab, hBodd, hS, hBS⟩
    refine ⟨Y.map f, B.map f, S.map f, Subgroup.map_mono hYB, Subgroup.map_mono hBX, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · have e : ↥Y ≃* ↥(Y.map f) := Subgroup.equivMapOfInjective Y f hf
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    · rw [hcard, hYcard]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBab a ha b hb]
    · rw [hcard]
      exact hBodd
    · exact (E1.isSylowIn_map_of_injective hf).mpr hS
    · rw [hset, hset, ← Set.image_mul, ← Set.image_mul, hBS]

theorem nPrime_map_of_injective {f : M →* M'} (hf : Function.Injective f) (X : Subgroup M) :
    E3.nPrime (X.map f) = E3.nPrime X := by
  unfold E3.nPrime
  rw [nPrime_set_map_of_injective hf X]

end Map

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem nPrime_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    E3.nPrime (X.map (congrHom e)) = E3.nPrime X :=
  nPrime_map_of_injective (congrHom_injective e) X

end H

end CFSG.Quasithin
