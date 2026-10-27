module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem mem_map_of_commute_of_coprime (A : Subgroup G) (hAF : A ∈ partTwoF G) {C : Subgroup G}
    (hAC : A ≤ C) (T : Subgroup ↥C) [T.Normal] (hT3 : Nat.Coprime 3 (Nat.card T))
    {x : ↥C ⧸ T}
    (hxA : ∀ g ∈ (A.subgroupOf C).map (QuotientGroup.mk' T), g * x = x * g)
    (hx3 : x ^ 3 = 1) :
    x ∈ (A.subgroupOf C).map (QuotientGroup.mk' T) := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective T x
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  set N : Subgroup G := T.map C.subtype with hNdef
  have hNC : ∀ t ∈ T, (t : G) ∈ N := fun t ht => Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
  have hN3 : Nat.Coprime 3 (Nat.card N) := by
    rw [hNdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact hT3
  have key : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hn
    have h7 := hNC _ ((inferInstance : T.Normal).conj_mem t ht ⟨c, hc⟩)
    simpa using h7
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact key c hc n hn
    · intro hn
      have h8 := key c⁻¹ (C.inv_mem hc) (c * n * c⁻¹) hn
      have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
      rw [e] at h8
      exact h8
  have hBN : A ≤ Subgroup.normalizer (N : Set G) := hAC.trans hCN
  have hk : ∀ b ∈ A, (j : G)⁻¹ * (b * (j : G) * b⁻¹) ∈ N := by
    intro b hb
    have hbC : b ∈ C := hAC hb
    have hmem : QuotientGroup.mk' T (⟨b, hbC⟩ : ↥C) ∈ (A.subgroupOf C).map (QuotientGroup.mk' T) :=
      Subgroup.mem_map.mpr ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have hc := hxA _ hmem
    have h2 : QuotientGroup.mk' T ((⟨b, hbC⟩ : ↥C) * j * (⟨b, hbC⟩ : ↥C)⁻¹) =
        QuotientGroup.mk' T j := by
      rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
    have h3 : (j : ↥C)⁻¹ * ((⟨b, hbC⟩ : ↥C) * j * (⟨b, hbC⟩ : ↥C)⁻¹) ∈ T := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at h2
      exact QuotientGroup.eq.mp h2.symm
    simpa using hNC _ h3
  obtain ⟨y, hy, hyA⟩ := exists_commute_mem_coset148 (k := (j : G))
    (isPGroup_three_of_pow148 hA3) hN3 hBN hk
  obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hy
  have hyC : y ∈ C := by
    have h1 : (j : G)⁻¹ * y ∈ C := by
      rw [← hte]
      exact t.2
    simpa using C.mul_mem j.2 h1
  have hyT : (j : ↥C)⁻¹ * (⟨y, hyC⟩ : ↥C) ∈ T := by
    have htj : t = (j : ↥C)⁻¹ * (⟨y, hyC⟩ : ↥C) := Subtype.ext (by simpa using hte)
    rw [← htj]
    exact ht
  have hαy : QuotientGroup.mk' T j = QuotientGroup.mk' T (⟨y, hyC⟩ : ↥C) := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq.mpr hyT
  obtain ⟨m, k, hm, hv⟩ := exists_pow_three_part148 (y := y)
  have hvC : y ^ m ∈ C := C.pow_mem hyC m
  have hαv : QuotientGroup.mk' T (⟨y ^ m, hvC⟩ : ↥C) = QuotientGroup.mk' T j := by
    have e1 : QuotientGroup.mk' T (⟨y ^ m, hvC⟩ : ↥C) =
        QuotientGroup.mk' T (⟨y, hyC⟩ : ↥C) ^ m := by
      rw [← map_pow]
      rfl
    rw [e1, ← hαy, ← Nat.div_add_mod m 3, hm, pow_add, pow_mul, hx3, one_pow, one_mul, pow_one]
  have hv3 : (y ^ m) ^ 3 = 1 := by
    have hv3C : (y ^ m) ^ 3 ∈ C := C.pow_mem hvC 3
    have h1 : (y ^ m) ^ 3 ∈ N := by
      have h5 : QuotientGroup.mk' T (⟨(y ^ m) ^ 3, hv3C⟩ : ↥C) = 1 := by
        rw [show (⟨(y ^ m) ^ 3, hv3C⟩ : ↥C) = (⟨y ^ m, hvC⟩ : ↥C) ^ 3 from rfl, map_pow, hαv,
          hx3]
      have h6 : (⟨(y ^ m) ^ 3, hv3C⟩ : ↥C) ∈ T := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5
        exact h5
      exact hNC _ h6
    refine eq_one_of_pow_three_pow_eq_one148 hN3 h1 (k := k) ?_
    rw [← pow_mul, show 3 * 3 ^ k = 3 ^ k * 3 by ring, pow_mul, hv, one_pow]
  have hvA : ∀ a ∈ A, a * y ^ m = y ^ m * a := fun a ha => (Commute.pow_right (hyA a ha) m).eq
  have hvAm : y ^ m ∈ A :=
    Sec4.mem_of_maximal_of_commute ⟨hAF.1, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩ hv3 hvA
  rw [← hαv]
  exact Subgroup.mem_map.mpr ⟨⟨y ^ m, hvC⟩, Subgroup.mem_subgroupOf.mpr hvAm, rfl⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
