module

public import CFSG.RankThree.PartTwo.Census.OddClassical.Component

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

variable {H : Type} [Group H] [Finite H]

theorem not_isCharTwoType_quotient_of_isPGroup (N : Subgroup H) [N.Normal] {t : H} (htN : t ∉ N)
    (ht2 : t ^ 2 ∈ N) {K J : Subgroup H} (hKt : ∀ k ∈ K, k * t * k⁻¹ * t⁻¹ ∈ N)
    (hKn : ∀ g : H, g * t * g⁻¹ * t⁻¹ ∈ N → ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hJK : J ≤ K)
    (hJn : ∀ g ∈ K, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hJN : IsPGroup 2 (J ⊓ N : Subgroup H))
    (hperf : ⁅J, J⁆ = J)
    (hJ2 : ∀ M : Subgroup H, M ≤ J → (∀ g ∈ J, ∀ m ∈ M, g * m * g⁻¹ ∈ M) → IsPGroup 2 M →
      M ≤ Subgroup.centralizer (J : Set H))
    (hJ : ¬ IsPGroup 2 J) : ¬ IsCharTwoType (H ⧸ N) := by
  set π := QuotientGroup.mk' N
  set L := Subgroup.normalizer (Subgroup.zpowers (π t) : Set (H ⧸ N))
  have hto : orderOf (π t) = 2 := orderOf_mk_eq_two N htN ht2
  have hL : IsTwoLocal L := by
    refine ⟨Subgroup.zpowers (π t), ?_, ?_, rfl⟩
    · rw [Ne, Subgroup.zpowers_eq_bot]
      intro h
      rw [h, orderOf_one] at hto
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
  have h2elt : ∀ x ∈ J, ∀ k : ℕ, π (x ^ 2 ^ k) = 1 → ∃ l : ℕ, x ^ 2 ^ l = 1 := by
    intro x hx k hk
    have hmem : x ^ 2 ^ k ∈ J ⊓ N :=
      Subgroup.mem_inf.mpr ⟨J.pow_mem hx _, (QuotientGroup.eq_one_iff _).mp hk⟩
    obtain ⟨l, hl⟩ := hJN ⟨_, hmem⟩
    refine ⟨k + l, ?_⟩
    have := congrArg Subtype.val hl
    rw [pow_add, pow_mul]
    simpa using this
  refine not_isCharTwoType_of_perfect_subnormal_subgroup (L := L) (K := K.map π) (J := J.map π)
    hL ?_ ?_ (Subgroup.map_mono hJK) ?_ ?_ ?_ ?_
  ·
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
    rintro _ ⟨n, rfl⟩
    have hc : π k * π t = π t * π k := by
      have h1 := hKt k hk
      rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, map_mul, map_mul,
        map_mul, map_inv, map_inv] at h1
      calc π k * π t = π k * π t * (π k)⁻¹ * (π t)⁻¹ * (π t * π k) := by group
        _ = π t * π k := by rw [h1, one_mul]
    exact (Commute.zpow_left hc.symm n).eq
  ·
    rintro g hg _ ⟨k, hk, rfl⟩
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective N g
    refine ⟨g' * k * g'⁻¹, hKn g' (commutator_mem_of_mem_normalizer N htN ht2 hg) k hk, ?_⟩
    rw [map_mul, map_mul, map_inv]
  ·
    rintro _ ⟨g, hg, rfl⟩ _ ⟨j, hj, rfl⟩
    exact ⟨g * j * g⁻¹, hJn g hg j hj, by rw [map_mul, map_mul, map_inv]⟩
  ·
    rw [← Subgroup.map_commutator, hperf]
  ·
    intro M hMJ hMn hM2
    set M' : Subgroup H := (M.comap π) ⊓ J
    have hM'2 : IsPGroup 2 M' := by
      intro x
      obtain ⟨k, hk⟩ := hM2 ⟨π x, (Subgroup.mem_inf.mp x.2).1⟩
      have hk' : π ((x : H) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      obtain ⟨l, hl⟩ := h2elt _ (Subgroup.mem_inf.mp x.2).2 k hk'
      exact ⟨l, Subtype.ext (by simpa using hl)⟩
    have hM'n : ∀ g ∈ J, ∀ m ∈ M', g * m * g⁻¹ ∈ M' := by
      intro g hg m hm
      obtain ⟨hmM, hmJ⟩ := Subgroup.mem_inf.mp hm
      refine Subgroup.mem_inf.mpr ⟨?_, J.mul_mem (J.mul_mem hg hmJ) (J.inv_mem hg)⟩
      change π (g * m * g⁻¹) ∈ M
      rw [map_mul, map_mul, map_inv]
      exact hMn (π g) ⟨g, hg, rfl⟩ (π m) hmM
    have hM'c := hJ2 M' inf_le_right hM'n hM'2
    intro x hx
    obtain ⟨j, hj, rfl⟩ := hMJ hx
    have hjM' : j ∈ M' := Subgroup.mem_inf.mpr ⟨hx, hj⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j', hj', rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hM'c hjM') j' hj'
    rw [← map_mul, ← map_mul, this]
  ·
    intro h2
    apply hJ
    intro x
    obtain ⟨k, hk⟩ := h2 ⟨π x, ⟨x, x.2, rfl⟩⟩
    have hk' : π ((x : H) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    obtain ⟨l, hl⟩ := h2elt _ x.2 k hk'
    exact ⟨l, Subtype.ext (by simpa using hl)⟩

theorem not_isCharTwoType_of_sl2_component' (N : Subgroup H) [N.Normal]
    (hNc : N ≤ Subgroup.center H) {t : H} (htN : t ∉ N) (ht2 : t ^ 2 ∈ N) {J : Subgroup H}
    (hJt : ∀ j ∈ J, j * t = t * j) (hJn : ∀ g : H, g * t = t * g → ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hJN : IsPGroup 2 (J ⊓ N : Subgroup H)) {F : Type*} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (hodd : Odd (Nat.card F)) (e : J ≃* SL(2, F)) :
    ¬ IsCharTwoType (H ⧸ N) := by
  refine not_isCharTwoType_quotient_of_isPGroup N htN ht2 (K := Subgroup.centralizer {t})
    (J := J) (fun k hk => ?_) (fun g hg k hk => ?_) (fun j hj => ?_) (fun g hg j hj => ?_) hJN
    (commutator_eq_self_of_mulEquiv_sl2 h4 e) (le_centralizer_of_mulEquiv_sl2 h4 hodd e)
    (not_isPGroup_two_of_mulEquiv_sl2 hodd e)
  · rw [Subgroup.mem_centralizer_singleton_iff] at hk
    rw [hk, mul_inv_cancel_right, mul_inv_cancel]
    exact N.one_mem
  · rw [Subgroup.mem_centralizer_singleton_iff] at hk ⊢
    exact conj_mem_centralizer_of_mem_center N hNc hg hk
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hJt j hj
  · rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact hJn g hg j hj

end CFSG.RankThree.PartTwo.Census
