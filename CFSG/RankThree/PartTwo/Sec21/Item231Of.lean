module

public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec21.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G]

theorem card_eq_of_mem_partTwoS [Finite G] (h611 : Sec6.Item6_11_1) {A : Subgroup G}
    (hA : Sec21Std G A) : Nat.card A = 3 ^ 3 ∨ Nat.card A = 3 ^ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe := hA.mem_S.1.1
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  obtain ⟨k, hk⟩ := hAp.exists_card_eq
  obtain ⟨E, hE, hEA⟩ := hA.mem_S.1.2.2
  have h27 : 3 ^ 3 ∣ 3 ^ k := by
    rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE.2.1]
    exact Subgroup.card_dvd_of_le hEA
  have hk3 : 3 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h27
  have hrank : k ≤ CFSG.Open.pRank 3 A :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three A)
      ⟨A, le_rfl, ⟨hAe.1, hAe.2⟩, hk⟩
  have hk4 : k ≤ 4 := hrank.trans (h611 G hA.standing A hA.mem_S.1)
  rw [hk]
  interval_cases k
  · left; rfl
  · right; rfl

@[expose] def Item231IStar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → starOf A (iGroup A) = Subgroup.closure (dStar A)

theorem natCard_subgroupOf (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
  rw [← Subgroup.inf_subgroupOf_right]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem centralizer_subgroupOf_eq {A I : Subgroup G} (hAI : A ≤ I) :
    Subgroup.centralizer ((A.subgroupOf I : Subgroup I) : Set I) =
      (Subgroup.centralizer (A : Set G)).subgroupOf I := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    exact congrArg Subtype.val (h ⟨a, hAI ha⟩ (Subgroup.mem_subgroupOf.mpr ha))
  · intro h a ha
    exact Subtype.ext (h a (Subgroup.mem_subgroupOf.mp ha))

theorem card_starOf_mul_card [Finite G] (A X : Subgroup G) :
    Nat.card (starOf A X) * Nat.card (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) =
      Nat.card (X ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) := by
  set N := Subgroup.normalizer (A : Set G)
  set H : Subgroup N := X.subgroupOf N
  set g : H →* MulAut A := A.normalizerMonoidHom.comp H.subtype
  have hrange : g.range = starOf A X := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : (g.ker.map H.subtype).map N.subtype = X ⊓ Subgroup.centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨Subgroup.mem_subgroupOf.mp h.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 : ((g h ⟨a, ha⟩ : A) : G) = a := by rw [MonoidHom.mem_ker.mp hh]; rfl
      change ((h : N) : G) * a * ((h : N) : G)⁻¹ = a at h1
      calc a * ((h : N) : G) = ((h : N) : G) * a * ((h : N) : G)⁻¹ * ((h : N) : G) := by
            rw [h1]
        _ = ((h : N) : G) * a := by group
    · rintro ⟨hxX, hxC⟩
      have hxN : x ∈ N := Subgroup.centralizer_le_normalizer _ hxC
      refine ⟨⟨x, hxN⟩, ⟨⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hxX⟩, ?_, rfl⟩, rfl⟩
      refine MonoidHom.mem_ker.mpr (MulEquiv.ext fun a => Subtype.ext ?_)
      change x * (a : G) * x⁻¹ = a
      rw [← Subgroup.mem_centralizer_iff.mp hxC a a.2, mul_inv_cancel_right]
  have hH : Nat.card H = Nat.card (X ⊓ N : Subgroup G) := natCard_subgroupOf X N
  rw [← hrange, ← hker, Subgroup.card_map_of_injective N.subtype_injective,
    Subgroup.card_map_of_injective H.subtype_injective, ← hH, ← Subgroup.index_ker, mul_comm]
  exact Subgroup.card_mul_index g.ker

theorem card_starOf_le_of_le [Finite G] {A I : Subgroup G} (hAI : A ≤ I) {k : ℕ}
    (h : Nat.card (Subgroup.normalizer ((A.subgroupOf I : Subgroup I) : Set I)) ≤
      k * Nat.card (Subgroup.centralizer ((A.subgroupOf I : Subgroup I) : Set I))) :
    Nat.card (starOf A I) ≤ k := by
  rw [← Subgroup.subgroupOf_normalizer_eq hAI, centralizer_subgroupOf_eq hAI,
    natCard_subgroupOf, natCard_subgroupOf, inf_comm, ← card_starOf_mul_card A I,
    inf_comm (Subgroup.centralizer _)] at h
  have hpos : 0 < Nat.card (I ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  exact le_of_mul_le_mul_right h hpos

end CFSG.RankThree.PartTwo.Sec21
