module

public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem card_rootsOfUnity_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (rootsOfUnity p L) = p := by
  have hp0 : (p : L) ≠ 0 := fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ((CharP.cast_eq_zero_iff L 2 p).1 h)).symm
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hp0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  exact hζ.card_rootsOfUnity

theorem card_rootsOfUnity_of_odd {m : ℕ} (hm : Odd m) : Nat.card (rootsOfUnity m L) = m := by
  have hm0 : (m : L) ≠ 0 := fun h => by
    have := (CharP.cast_eq_zero_iff L 2 m).1 h
    exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)
  have : NeZero m := ⟨hm.pos.ne'⟩
  have : NeZero (m : L) := ⟨hm0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L m
  exact hζ.card_rootsOfUnity

theorem card_range_of_odd {m : ℕ} (hm : Odd m) {M : Type*} [Group M]
    (Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* M) (hΦ : Function.Injective Φ) :
    Nat.card Φ.range = m ^ 2 := by
  rw [Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv.symm, Nat.card_prod,
    card_rootsOfUnity_of_odd hm, sq]

theorem exists_pTors_elt {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m) :
    ∃ ζ : rootsOfUnity m L, (ζ : Lˣ) ^ p = 1 ∧ ∀ N : ℤ, (ζ : Lˣ) ^ N = 1 → (p : ℤ) ∣ N := by
  have hp0 : (p : L) ≠ 0 := fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 ((CharP.cast_eq_zero_iff L 2 p).1 h)).symm
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (p : L) := ⟨hp0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  lift ζ₀ to Lˣ using hζ₀.isUnit hp.ne_zero
  rw [IsPrimitiveRoot.coe_units_iff] at hζ₀
  have hmem : ζ₀ ∈ rootsOfUnity m L := by
    rw [mem_rootsOfUnity]
    obtain ⟨k, rfl⟩ := hpm
    rw [pow_mul, hζ₀.pow_eq_one, one_pow]
  exact ⟨⟨ζ₀, hmem⟩, hζ₀.pow_eq_one, fun N hN => (hζ₀.zpow_eq_one_iff_dvd N).1 hN⟩

@[expose] def pTors (m p : ℕ) : Subgroup ((rootsOfUnity m L) × (rootsOfUnity m L)) :=
  ((rootsOfUnity p L).subgroupOf (rootsOfUnity m L)).prod
    ((rootsOfUnity p L).subgroupOf (rootsOfUnity m L))

omit [CharP L 2] [IsAlgClosed L] in
theorem mem_pTors {m p : ℕ} (z : (rootsOfUnity m L) × (rootsOfUnity m L)) :
    z ∈ pTors m p ↔ (z.1 : Lˣ) ^ p = 1 ∧ (z.2 : Lˣ) ^ p = 1 := by
  simp [pTors, Subgroup.mem_prod, Subgroup.mem_subgroupOf, mem_rootsOfUnity]

theorem card_pTors {m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ m) :
    Nat.card (pTors m p : Subgroup ((rootsOfUnity m L) × (rootsOfUnity m L))) = p ^ 2 := by
  have h1 : Nat.card ((rootsOfUnity p L).subgroupOf (rootsOfUnity m L)) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootsOfUnity_le_of_dvd hpm)).toEquiv]
    exact card_rootsOfUnity_eq hp hp2
  unfold pTors
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, h1, sq]

theorem exists_elemAbelian_of_injective {M : Type*} [Group M] {m p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpm : p ∣ m)
    (Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* M) (hΦ : Function.Injective Φ) :
    ∃ E : Subgroup M, E ≤ Φ.range ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ 2 := by
  refine ⟨(pTors m p).map Φ, ?_, ?_, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rw [CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian]
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, z, -, rfl⟩ ⟨_, z', -, rfl⟩
      apply Subtype.ext
      show Φ z * Φ z' = Φ z' * Φ z
      rw [← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨z, hz, rfl⟩
      rw [← map_pow]
      have h := (mem_pTors z).1 hz
      have : z ^ p = 1 := Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
      rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hΦ]
    exact card_pTors hp hp2 hpm

end CFSG.RankThree.PartOne.KEXC
