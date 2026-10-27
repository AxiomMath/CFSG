module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.OrderReductions.PrimePart

universe u

variable {G : Type u} [Group G] [Finite G]

theorem sylow_in_characteristic_normalizer_of_prime_part_bound
    (p : ℕ) (hp : p.Prime) (J X Q : Subgroup G)
    (hQJ : Q ≤ J) (hXQ : X ≤ Q) (hXchar : (X.subgroupOf Q).Characteristic)
    (hQp : IsPGroup p Q)
    (hbound : primePart p
      (Nat.card (Subgroup.normalizer (X : Set G) ⊓ J : Subgroup G)) ≤ Nat.card Q) :
    ∃ S : Sylow p (Subgroup.normalizer (X : Set G) ⊓ J : Subgroup G),
      (S : Subgroup _).map (Subgroup.normalizer (X : Set G) ⊓ J).subtype = Q := by
  let : Fact p.Prime := ⟨hp⟩
  let : (X.subgroupOf Q).Characteristic := hXchar
  let T := Subgroup.normalizer (X : Set G) ⊓ J
  have hQN : Q ≤ Subgroup.normalizer (X : Set G) := by
    have hh := primeComplementGrowth_normalizer_le_characteristic_image_normalizer
      Q (X.subgroupOf Q)
    rw [Subgroup.map_subgroupOf_eq_of_le hXQ] at hh
    exact Subgroup.le_normalizer.trans hh
  have hQT : Q ≤ T := le_inf hQN hQJ
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hcard : Nat.card Q = primePart p (Nat.card T) := by
    apply le_antisymm
    · rw [hn]
      exact Nat.pow_le_pow_right hp.pos
        ((hp.pow_dvd_iff_le_factorization (ne_of_gt (Nat.card_pos (α := T)))).mp
          (hn ▸ Subgroup.card_dvd_of_le hQT))
    · exact hbound
  exact exists_sylow_image_of_card p Q T hQT hcard

theorem sylow_of_characteristic_normalizer
    (p : ℕ) (hp : p.Prime) (J X Q : Subgroup G)
    (hQJ : Q ≤ J) (hXQ : X ≤ Q) (hXchar : (X.subgroupOf Q).Characteristic)
    (S : Sylow p (Subgroup.normalizer (X : Set G) ⊓ J : Subgroup G))
    (hS : (S : Subgroup _).map (Subgroup.normalizer (X : Set G) ⊓ J).subtype = Q) :
    ∃ P : Sylow p J, (P : Subgroup J).map J.subtype = Q := by
  let : Fact p.Prime := ⟨hp⟩
  let : (X.subgroupOf Q).Characteristic := hXchar
  let T := Subgroup.normalizer (X : Set G) ⊓ J
  have hQp : IsPGroup p Q := hS ▸ S.isPGroup'.map T.subtype
  have hinternalp : IsPGroup p (Q.subgroupOf J) :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQJ).symm
  have hNQNX : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (X : Set G) := by
    have hh := primeComplementGrowth_normalizer_le_characteristic_image_normalizer
      Q (X.subgroupOf Q)
    rwa [Subgroup.map_subgroupOf_eq_of_le hXQ] at hh
  obtain ⟨P, hP⟩ := CFSG.OrderReductions.FixedPairSylow.sylow_of_normalizer_control
    p (Q.subgroupOf J) hinternalp (by
      intro A hAp hQA
      rw [← Subgroup.subgroupOf_normalizer_eq hQJ]
      let B := A.map J.subtype
      have hBp : IsPGroup p B := hAp.map J.subtype
      have hQB : Q ≤ B := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hQJ]
        exact Subgroup.map_mono hQA
      have hBT : Subgroup.normalizer (Q : Set G) ⊓ B ≤ T :=
        le_inf (inf_le_left.trans hNQNX)
          (inf_le_right.trans (Subgroup.map_subtype_le _))
      have hcontrol := CFSG.OrderReductions.FixedPairSylow.internal_sylow_controls_normalizer
        p T S B hBp (hS.symm ▸ hQB) (hS.symm ▸ hBT)
      rw [hS] at hcontrol
      intro a ha
      exact hcontrol ⟨ha.1, Subgroup.mem_map_of_mem J.subtype ha.2⟩)
  refine ⟨P, ?_⟩
  rw [hP]
  exact Subgroup.map_subgroupOf_eq_of_le hQJ

theorem full_sylow_of_characteristic_prime_part_bound
    (p : ℕ) (hp : p.Prime) (J X Q : Subgroup G)
    (hQJ : Q ≤ J) (hXQ : X ≤ Q) (hXchar : (X.subgroupOf Q).Characteristic)
    (hQp : IsPGroup p Q)
    (hbound : primePart p
      (Nat.card (Subgroup.normalizer (X : Set G) ⊓ J : Subgroup G)) ≤ Nat.card Q) :
    ∃ P : Sylow p J, (P : Subgroup J).map J.subtype = Q := by
  obtain ⟨S, hS⟩ := sylow_in_characteristic_normalizer_of_prime_part_bound
    p hp J X Q hQJ hXQ hXchar hQp hbound
  exact sylow_of_characteristic_normalizer p hp J X Q hQJ hXQ hXchar S hS

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
