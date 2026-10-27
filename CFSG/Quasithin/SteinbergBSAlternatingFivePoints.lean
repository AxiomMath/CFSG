module

public import CFSG.Quasithin.SteinbergCBAlternatingFive
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SteinbergBS

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem index_stabilizer_perm_five (α : Fin 5) :
    (MulAction.stabilizer (Perm (Fin 5)) α).index = 5 := by
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem map_stabilizer_alternating (α : Fin 5) :
    (MulAction.stabilizer (alternatingGroup (Fin 5)) α).map (alternatingGroup (Fin 5)).subtype =
      alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxα⟩
    exact ⟨⟨x, hx⟩, hxα, rfl⟩

theorem card_alternating_inf_stabilizer (α : Fin 5) :
    Nat.card ↥(alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α) = 12 := by
  have : MulAction.IsPretransitive (alternatingGroup (Fin 5)) (Fin 5) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 5) (by simp)
  have h1 := MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin 5)) α
  have h2 := card_mul_index (MulAction.stabilizer (alternatingGroup (Fin 5)) α)
  rw [h1, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin,
    CFSG.Quasithin.SteinbergCB.nat_card_alternating_five] at h2
  rw [← map_stabilizer_alternating,
    card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective]
  omega

theorem le_of_isPGroup_of_card {G : Type*} [Group G] [Finite G] {W P L : Subgroup G}
    (hW : IsPGroup 2 W) (hP : IsPGroup 2 P) (hWP : W ≤ normalizer (P : Set G)) (hWL : W ≤ L)
    (hPL : P ≤ L) {m : ℕ} (hm : Odd m) (hL : Nat.card L = Nat.card P * m) : W ≤ P := by
  have hWP2 : IsPGroup 2 ↥(W ⊔ P) := hW.to_sup_of_normal_right' hP hWP
  obtain ⟨k, hk⟩ := hWP2.exists_card_eq
  obtain ⟨l, hl⟩ := hP.exists_card_eq
  have h1 : Nat.card ↥(W ⊔ P) ∣ Nat.card L := card_dvd_of_le (sup_le hWL hPL)
  rw [hL, hk, hl] at h1
  have h2 : 2 ^ k ∣ 2 ^ l :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)).dvd_of_dvd_mul_right h1
  have h3 : P = W ⊔ P := eq_of_le_of_card_ge le_sup_right (by
    rw [hk, hl]
    exact Nat.le_of_dvd (by positivity) h2)
  exact le_sup_left.trans h3.ge

theorem sylow_alternating_five_fixed {P : Subgroup (Perm (Fin 5))}
    (hP : IsSylowOf 2 P (alternatingGroup (Fin 5))) :
    ∃ α : Fin 5, (∀ β : Fin 5, (∀ p ∈ P, p β = β) ↔ β = α) ∧
      (∀ p ∈ P, p ≠ 1 → ∀ β : Fin 5, p β = β → β = α) ∧ Nat.card P = 4 ∧
      P ≤ alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α ∧
      alternatingGroup (Fin 5) ⊓ normalizer (P : Set (Perm (Fin 5))) =
        alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α ∧
      ∀ W : Subgroup (Perm (Fin 5)), IsPGroup 2 W →
        W ≤ alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α → W ≤ P := by
  classical
  obtain ⟨-, hS, -⟩ :=
    CFSG.Quasithin.SteinbergCB.alternating_five_unique_Sylow_two_containment_and_solvable_normalizer
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨-, hcard, α, hfix, hmem, hnorm, -, -, -⟩ := hS Q
  have hfix' : ∀ β : Fin 5,
      (∀ p ∈ (Q : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype,
        p β = β) ↔ β = α := by
    intro β
    rw [← hfix β]
    constructor
    · intro h p hp
      exact h _ ⟨p, hp, rfl⟩
    · rintro h _ ⟨p, hp, rfl⟩
      exact h p hp
  have hle : (Q : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype ≤
      alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.2, ((hfix α).2 rfl) p hp⟩
  have hN : alternatingGroup (Fin 5) ⊓ normalizer
      (((Q : Subgroup (alternatingGroup (Fin 5))).map (alternatingGroup (Fin 5)).subtype :
        Subgroup (Perm (Fin 5))) : Set (Perm (Fin 5))) =
      alternatingGroup (Fin 5) ⊓ MulAction.stabilizer (Perm (Fin 5)) α := by
    have hQ : ((Q : Subgroup (alternatingGroup (Fin 5))).map
        (alternatingGroup (Fin 5)).subtype).subgroupOf (alternatingGroup (Fin 5)) = Q :=
      comap_map_eq_self_of_injective (alternatingGroup (Fin 5)).subtype_injective _
    rw [← CFSG.QuasithinUnique.map_subtype_normalizer (map_subtype_le _), hQ, hnorm,
      map_stabilizer_alternating]
  refine ⟨α, hfix', ?_, by rw [card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective,
    hcard], hle, hN, fun W hW hWL => ?_⟩
  ·
    rintro _ ⟨p, hp, rfl⟩ hp1 β hβ
    rcases (hmem p).1 hp with h | ⟨htype, hpα⟩
    · exact absurd (by rw [h]; rfl) hp1
    · by_contra hβα
      have hsupp : ((p : Perm (Fin 5)).support).card = 4 := by
        rw [← Equiv.Perm.sum_cycleType, htype]
        rfl
      have hsub : (p : Perm (Fin 5)).support ⊆ (Finset.univ.erase α).erase β := by
        intro x hx
        rw [Equiv.Perm.mem_support] at hx
        refine Finset.mem_erase.2 ⟨fun h => hx (h ▸ hβ), Finset.mem_erase.2
          ⟨fun h => hx (h ▸ hpα), Finset.mem_univ x⟩⟩
      have hc := Finset.card_le_card hsub
      rw [hsupp, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hβα, Finset.mem_univ β⟩),
        Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ, Fintype.card_fin] at hc
      omega
  ·
    refine le_of_isPGroup_of_card hW ((Q.isPGroup').map _) ?_ hWL hle (m := 3) (by decide) ?_
    · exact hWL.trans (hN ▸ inf_le_right)
    · rw [card_alternating_inf_stabilizer, card_map_of_injective
        (alternatingGroup (Fin 5)).subtype_injective, hcard]

theorem sylow_eq_of_fixed {P P' : Subgroup (Perm (Fin 5))}
    (hP : IsSylowOf 2 P (alternatingGroup (Fin 5)))
    (hP' : IsSylowOf 2 P' (alternatingGroup (Fin 5))) {α : Fin 5}
    (hPα : P ≤ MulAction.stabilizer (Perm (Fin 5)) α)
    (hP'α : P' ≤ MulAction.stabilizer (Perm (Fin 5)) α) : P = P' := by
  obtain ⟨β, hfix, -, hcard, -, -, hall⟩ := sylow_alternating_five_fixed hP
  obtain ⟨β', hfix', -, hcard', -, -, -⟩ := sylow_alternating_five_fixed hP'
  have hβ : α = β := (hfix α).1 fun p hp => hPα hp
  subst hβ
  have hle : P' ≤ P := hall P' hP'.isPGroup (le_inf hP'.le hP'α)
  exact (eq_of_le_of_card_ge hle (by rw [hcard, hcard'])).symm

theorem sup_sylow_eq_alternating {P P' : Subgroup (Perm (Fin 5))}
    (hP : IsSylowOf 2 P (alternatingGroup (Fin 5)))
    (hP' : IsSylowOf 2 P' (alternatingGroup (Fin 5))) (hne : P ≠ P') :
    P ⊔ P' = alternatingGroup (Fin 5) := by
  classical
  obtain ⟨α, hfix, hfix1, hcard, hPle, -, -⟩ := sylow_alternating_five_fixed hP
  obtain ⟨β, hfix', -, -, hP'le, -, -⟩ := sylow_alternating_five_fixed hP'
  have hαβ : α ≠ β := fun h => hne (sylow_eq_of_fixed hP hP' (hPle.trans inf_le_right)
    (h ▸ hP'le.trans inf_le_right))
  have hLA : P ⊔ P' ≤ alternatingGroup (Fin 5) := sup_le hP.le hP'.le
  have hpα : ∀ p ∈ P, p α = α := (hfix α).2 rfl
  have htrans : ∀ γ δ : Fin 5, γ ≠ α → δ ≠ α → ∃ p ∈ P, p γ = δ := by
    intro γ δ hγ hδ
    let f : ↥P → Fin 5 := fun p => (p : Perm (Fin 5)) γ
    have hf : Function.Injective f := fun p q hpq => by
      by_contra hne'
      have h1 : (q : Perm (Fin 5))⁻¹ * p ≠ 1 := fun h => hne' (Subtype.ext
        (inv_mul_eq_one.1 h).symm)
      have h2 : ((q : Perm (Fin 5))⁻¹ * p) γ = γ := by
        rw [Perm.mul_apply, show (p : Perm (Fin 5)) γ = (q : Perm (Fin 5)) γ from hpq]
        exact Equiv.Perm.inv_eq_iff_eq.2 rfl
      exact hγ (hfix1 _ (mul_mem (inv_mem q.2) p.2) h1 γ h2)
    have himg : Finset.univ.image f = Finset.univ.erase α := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
        refine Finset.mem_erase.2 ⟨fun h => hγ ?_, Finset.mem_univ _⟩
        have h1 : (p : Perm (Fin 5)) γ = (p : Perm (Fin 5)) α := by rw [hpα p p.2]; exact h
        exact (p : Perm (Fin 5)).injective h1
      · rw [Finset.card_image_of_injective _ hf, Finset.card_univ,
          Finset.card_erase_of_mem (Finset.mem_univ α), Finset.card_univ, Fintype.card_fin,
          ← Nat.card_eq_fintype_card, hcard]
    have hδ' : δ ∈ Finset.univ.image f := himg ▸ Finset.mem_erase.2 ⟨hδ, Finset.mem_univ δ⟩
    obtain ⟨p, -, hp⟩ := Finset.mem_image.1 hδ'
    exact ⟨p, p.2, hp⟩
  obtain ⟨p', hp'P, hp'α⟩ : ∃ p' ∈ P', p' α ≠ α := by
    by_contra h
    push Not at h
    exact hαβ ((hfix' α).1 h)
  have h5 : 5 ∣ Nat.card ↥(P ⊔ P') := by
    have horb : MulAction.orbit ↥(P ⊔ P') α = Set.univ := by
      refine Set.eq_univ_of_forall fun γ => ?_
      by_cases hγ : γ = α
      · rw [hγ]
        exact MulAction.mem_orbit_self α
      · obtain ⟨p, hp, hpγ⟩ := htrans (p' α) γ hp'α hγ
        exact ⟨⟨p * p', mul_mem (mem_sup_left hp) (mem_sup_right hp'P)⟩, by
          show (p * p') α = γ
          rw [Perm.mul_apply, hpγ]⟩
    have h1 := MulAction.index_stabilizer ↥(P ⊔ P') α
    rw [horb, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 := card_mul_index (MulAction.stabilizer ↥(P ⊔ P') α)
    rw [h1] at h2
    exact Dvd.intro_left _ h2
  have h4 : 4 ∣ Nat.card ↥(P ⊔ P') := hcard ▸ card_dvd_of_le le_sup_left
  have h60 : Nat.card ↥(P ⊔ P') ∣ 60 :=
    CFSG.Quasithin.SteinbergCB.nat_card_alternating_five ▸ card_dvd_of_le hLA
  have h20 : 20 ∣ Nat.card ↥(P ⊔ P') := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
  have hpos : 0 < Nat.card ↥(P ⊔ P') := Nat.card_pos
  have hcases : Nat.card ↥(P ⊔ P') = 20 ∨ Nat.card ↥(P ⊔ P') = 60 := by
    obtain ⟨k, hk⟩ := h20
    obtain ⟨m, hm⟩ := h60
    rw [hk] at hm hpos
    have hk3 : k ∣ 3 := ⟨m, by linarith⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h
    · left; rw [hk, h]
    · right; rw [hk, h]
  rcases hcases with h | h
  ·
    exfalso
    have hidx : ((P ⊔ P').subgroupOf (alternatingGroup (Fin 5))).index = 3 := by
      have h1 := relIndex_mul_card (P ⊔ P') (alternatingGroup (Fin 5))
      rw [inf_eq_left.2 hLA, h, CFSG.Quasithin.SteinbergCB.nat_card_alternating_five] at h1
      show (P ⊔ P').relIndex (alternatingGroup (Fin 5)) = 3
      omega
    have hcore : ((P ⊔ P').subgroupOf (alternatingGroup (Fin 5))).normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          ((P ⊔ P').subgroupOf (alternatingGroup (Fin 5))).normalCore with h1 | h1
      · exact h1
      · exfalso
        have h2 := normalCore_le ((P ⊔ P').subgroupOf (alternatingGroup (Fin 5)))
        rw [h1, top_le_iff] at h2
        rw [h2, index_top] at hidx
        omega
    have h1 := ((P ⊔ P').subgroupOf (alternatingGroup (Fin 5))).index_normalCore_dvd_factorial_index
    rw [hcore, index_bot, hidx, CFSG.Quasithin.SteinbergCB.nat_card_alternating_five] at h1
    norm_num [Nat.factorial] at h1
  · exact eq_of_le_of_card_ge hLA (by
      rw [h, CFSG.Quasithin.SteinbergCB.nat_card_alternating_five])

end CFSG.Quasithin.SteinbergBS
