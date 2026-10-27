module

public import CFSG.RankThree.PartTwo.Sec4.Item423ResProofCensusL29

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res423Alt

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem false_of_isExtOf_three {Q : Type*} [Group Q] (hq : IsQuasisimple X)
    (hZ : Subgroup.center X = ⊥) (h : IsExtOf X Q (Multiplicative (ZMod 3))) : False := by
  obtain ⟨K, hKn, ⟨eK⟩, -⟩ := h
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKn with hK | hK
  ·
    obtain ⟨-, -, ⟨u, v, huv⟩⟩ := hq
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
    apply huv
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    have hcomm : ∀ a b : K, a * b = b * a := fun a b => eK.injective (by
      rw [map_mul, map_mul, mul_comm])
    have hu : u' ∈ K := hK ▸ Subgroup.mem_top u'
    have hv : v' ∈ K := hK ▸ Subgroup.mem_top v'
    exact congrArg Subtype.val (hcomm ⟨u', hu⟩ ⟨v', hv⟩)
  ·
    rw [hZ, le_bot_iff] at hK
    rw [hK, Subgroup.card_bot] at hK3
    norm_num at hK3

omit [Finite X] in
theorem not_nine_dvd_card_alternating {n : ℕ} (hn : n ≤ 5)
    (e : X ≃* alternatingGroup (Fin n)) : ¬ 9 ∣ Nat.card X := by
  intro h9
  have hdvd : Nat.card X ∣ n.factorial := by
    rw [Nat.card_congr e.toEquiv]
    have := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
    rwa [Nat.card_perm, Nat.card_fin] at this
  have h := h9.trans hdvd
  interval_cases n <;> simp [Nat.factorial] at h

end Res423Alt

open Res423Alt

@[expose] def K423Inner46FourAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (∃ n : ℕ, 6 ≤ n ∧ n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) → IsQuasisimple X →
      Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

theorem k423Inner46Four_of (h : K423Inner46FourAlt) : K423Inner46Four := by
  rintro X _ _ hX hq hZ hSL
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | hX | hX
  · by_cases h6 : 6 ≤ n
    · exact h X ⟨n, h6, hn, ⟨e⟩⟩ hq hZ hSL
    · exact Res423Census.census423_of_not_nine_dvd (not_nine_dvd_card_alternating (by omega) e)
  · exact (false_of_isExtOf_three hq hZ hX).elim
  · exact (false_of_isExtOf_three hq hZ hX).elim

@[expose] def K423Inner46FiveSimple : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (∃ s ∈ sporadics46, Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) →
    ¬ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census423 X

theorem k423Inner46FiveRest_of (h : K423Inner46FiveSimple) : K423Inner46FiveRest := by
  rintro X _ _ hX hJ hq hZ hSL
  rcases hX with hX | ⟨s, -, hX⟩
  · exact h X hX hJ hq hZ hSL
  · exact (false_of_isExtOf_three hq hZ hX).elim

theorem k423InnerCensus_of_open
    (h3 : K423Inner46Three) (h4 : K423Inner46FourAlt) (h5 : K423Inner46FiveSimple)
    (h6 : K423Inner46SixRest) (h7 : K423Inner46Seven) (h8 : K423Inner46Eight) :
    K423InnerCensus :=
  k423InnerCensus_of_rest'' h3 (k423Inner46Four_of h4) (k423Inner46FiveRest_of h5) h6 h7 h8

end CFSG.RankThree.PartTwo.Sec4
