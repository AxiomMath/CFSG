module

public import CFSG.LocalAnalysis.SignalizerFunctor.HyperplaneGeneration
public import CFSG.SignalizerFunctorTheorem.Coprime.CommutatorGeneration

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem mem_hyperplanes_iff_index {A B : Subgroup G} (hB : B ≤ A) :
    B ∈ Coprime.hyperplanes p A ↔ (B.subgroupOf A).index = p := by
  have h1 := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv] at h1
  constructor
  · rintro ⟨-, hcard⟩
    have hpos : 0 < Nat.card B := Nat.card_pos
    rw [hcard, mul_comm p] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  · intro hidx
    refine ⟨hB, ?_⟩
    rw [hidx] at h1
    rw [← h1, mul_comm]

theorem generation_hyperplanes (hp : p.Prime) {A X : Subgroup G} (hA : IsElemAbelian p A)
    (hA2 : p ^ 2 ≤ Nat.card A) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hcop : Nat.Coprime p (Nat.card X)) :
    ⨆ B ∈ Coprime.hyperplanes p A, X ⊓ Subgroup.centralizer (B : Set G) = X := by
  have hA0 : A ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hA2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hgen := elementary_abelian_hyperplane_generation p hp A X hA hA0 hAX hcop
  apply le_antisymm
  · exact iSup₂_le fun B _ => inf_le_left
  · refine le_trans (le_of_eq hgen.symm) ?_
    refine iSup_le fun B => iSup_le fun hBA => iSup_le fun hidx => ?_
    exact le_iSup₂_of_le B ((mem_hyperplanes_iff_index hBA).mpr hidx) le_rfl

omit [Finite G] in
theorem exists_Ek_le_of_card (hp : p.Prime) {A C : Subgroup G} (hA : IsElemAbelian p A)
    (hCA : C ≤ A) (hC : p ≤ Nat.card C) : ∃ S ∈ signalizerFunctorEk p 1 A, S ≤ C := by
  have hCe : IsElemAbelian p C := elementary_abelian_of_le p hA hCA
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp
    (elementary_abelian_isPGroup p C hCe) (n := 1) (by simpa using hC)
  have hKC : K.map C.subtype ≤ C := Subgroup.map_subtype_le K
  refine ⟨K.map C.subtype, ⟨hKC.trans hCA, ?_⟩, hKC⟩
  rw [Subgroup.card_map_of_injective C.subtype_injective]
  exact hK

omit [Finite G] in
theorem exists_Ek_le_hyperplane (hp : p.Prime) {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hA2 : p ^ 2 ≤ Nat.card A) (hB : B ∈ Coprime.hyperplanes p A) :
    ∃ S ∈ signalizerFunctorEk p 1 A, S ≤ B := by
  refine exists_Ek_le_of_card hp hA hB.1 ?_
  have h1 : p * p ≤ p * Nat.card B := by
    calc p * p = p ^ 2 := (sq p).symm
      _ ≤ Nat.card A := hA2
      _ = p * Nat.card B := hB.2
  exact Nat.le_of_mul_le_mul_left h1 hp.pos

theorem exists_Ek_le_inf_hyperplanes (hp : p.Prime) {A B B' : Subgroup G}
    (hA : IsElemAbelian p A) (hA3 : p ^ 3 ≤ Nat.card A) (hB : B ∈ Coprime.hyperplanes p A)
    (hB' : B' ∈ Coprime.hyperplanes p A) :
    ∃ S ∈ signalizerFunctorEk p 1 A, S ≤ B ∧ S ≤ B' := by
  have hCA : B ⊓ B' ≤ A := inf_le_left.trans hB.1
  have hidx : ((B ⊓ B').subgroupOf A).index ≤ p * p := by
    have hsub : (B ⊓ B').subgroupOf A = B.subgroupOf A ⊓ B'.subgroupOf A :=
      Subgroup.comap_inf B B' A.subtype
    have h1 : (B.subgroupOf A).index = p := (mem_hyperplanes_iff_index hB.1).mp hB
    have h2 : (B'.subgroupOf A).index = p := (mem_hyperplanes_iff_index hB'.1).mp hB'
    calc ((B ⊓ B').subgroupOf A).index = (B.subgroupOf A ⊓ B'.subgroupOf A).index := by rw [hsub]
      _ ≤ (B.subgroupOf A).index * (B'.subgroupOf A).index := Subgroup.index_inf_le
      _ = p * p := by rw [h1, h2]
  have hmul := ((B ⊓ B').subgroupOf A).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv] at hmul
  have hcard : p ≤ Nat.card (B ⊓ B' : Subgroup G) := by
    by_contra hlt
    have hlt' : Nat.card (B ⊓ B' : Subgroup G) < p := not_le.mp hlt
    have h1 : Nat.card (B ⊓ B' : Subgroup G) * ((B ⊓ B').subgroupOf A).index ≤
        Nat.card (B ⊓ B' : Subgroup G) * (p * p) := Nat.mul_le_mul_left _ hidx
    have h2 : Nat.card (B ⊓ B' : Subgroup G) * (p * p) < p * (p * p) :=
      Nat.mul_lt_mul_of_pos_right hlt' (Nat.mul_pos hp.pos hp.pos)
    have h3 : p ^ 3 = p * (p * p) := by ring
    omega
  obtain ⟨S, hS, hSC⟩ := exists_Ek_le_of_card hp hA hCA hcard
  exact ⟨S, hS, hSC.trans inf_le_left, hSC.trans inf_le_right⟩

theorem exists_mem_hyperplanes (hp : p.Prime) {A : Subgroup G} (hA : IsElemAbelian p A)
    (hA2 : p ^ 2 ≤ Nat.card A) : ∃ B, B ∈ Coprime.hyperplanes p A := by
  have : Fact p.Prime := ⟨hp⟩
  have hAp := elementary_abelian_isPGroup p A hA
  obtain ⟨n, hn⟩ := hAp.exists_card_eq
  have hn1 : 1 ≤ n := by
    by_contra hlt
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hn
    rw [hn] at hA2
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hAp
    (n := n - 1) (by rw [hn]; exact Nat.pow_le_pow_right hp.pos (Nat.sub_le n 1))
  refine ⟨K.map A.subtype, Subgroup.map_subtype_le K, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK, hn, ← pow_succ']
  congr 1
  omega

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
