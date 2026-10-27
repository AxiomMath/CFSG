module

public import CFSG.RankThree.PartTwo.Census.Criteria

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {H : Type} [Group H]

theorem card_map_mk_of_inf_eq_bot (N : Subgroup H) [N.Normal] {E : Subgroup H} (hEN : E ⊓ N = ⊥) :
    Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have : (x : H) ∈ E ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hx⟩
    rw [hEN, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  have hrange : E.map (QuotientGroup.mk' N) = ((QuotientGroup.mk' N).comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem orderOf_mk_eq_two (N : Subgroup H) [N.Normal] {t : H} (htN : t ∉ N) (ht2 : t ^ 2 ∈ N) :
    orderOf (QuotientGroup.mk' N t) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht2
  · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact htN

theorem le_localRank_quotient_of_commute [Finite H] (N : Subgroup H) [N.Normal] {p k : ℕ}
    (hp : p.Prime) {E : Subgroup H} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEN : E ⊓ N = ⊥) {t : H} (htN : t ∉ N) (ht2 : t ^ 2 ∈ N) (hEt : ∀ x ∈ E, x * t = t * x) :
    k ≤ localRank p (H ⧸ N) := by
  set π := QuotientGroup.mk' N
  refine le_localRank_of_commute_involution hp (orderOf_mk_eq_two N htN ht2)
    (E := E.map π) ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    (by rw [card_map_mk_of_inf_eq_bot N hEN, hc]) fun x hx => ?_
  · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    have hab : a' * b' = b' * a' :=
      congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    apply Subtype.ext
    change (a : H ⧸ N) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, hab]
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hE.2 x' hx', map_one]
  · obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_mul, ← map_mul, hEt x' hx']

theorem commutator_mem_of_mem_normalizer (N : Subgroup H) [N.Normal] {t g : H} (htN : t ∉ N)
    (ht2 : t ^ 2 ∈ N)
    (hg : QuotientGroup.mk' N g ∈
      Subgroup.normalizer (Subgroup.zpowers (QuotientGroup.mk' N t) : Set (H ⧸ N))) :
    g * t * g⁻¹ * t⁻¹ ∈ N := by
  set π := QuotientGroup.mk' N
  have hto : orderOf (π t) = 2 := orderOf_mk_eq_two N htN ht2
  have hmem := (Subgroup.mem_normalizer_iff.mp hg (π t)).mp (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hconj : π g * π t * (π g)⁻¹ = π t := by
    rw [← hk]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exfalso
      have h1 : π t ^ (m + m) = 1 := by
        rw [← two_mul, zpow_mul, zpow_ofNat, ← hto, pow_orderOf_eq_one, one_zpow]
      rw [h1] at hk
      have := hk.symm
      rw [mul_inv_eq_one, mul_eq_left] at this
      rw [this] at hto
      simp at hto
    · rw [zpow_add, zpow_mul, zpow_ofNat, ← hto, pow_orderOf_eq_one, one_zpow, one_mul,
        zpow_one]
  rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, map_mul, map_mul, map_mul,
    map_inv, map_inv, hconj, mul_inv_cancel]

theorem not_isCharTwoType_quotient [Finite H] (N : Subgroup H) [N.Normal] {t : H} (htN : t ∉ N)
    (ht2 : t ^ 2 ∈ N) {K J : Subgroup H} (hKt : ∀ k ∈ K, k * t * k⁻¹ * t⁻¹ ∈ N)
    (hKn : ∀ g : H, g * t * g⁻¹ * t⁻¹ ∈ N → ∀ k ∈ K, g * k * g⁻¹ ∈ K) (hJK : J ≤ K)
    (hJn : ∀ g ∈ K, ∀ j ∈ J, g * j * g⁻¹ ∈ J) (hJN : J ⊓ N = ⊥) (hperf : ⁅J, J⁆ = J)
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
  have hJinj : ∀ a ∈ J, ∀ b ∈ J, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a * b⁻¹ ∈ J ⊓ N := Subgroup.mem_inf.mpr ⟨J.mul_mem ha (J.inv_mem hb), by
      rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, map_mul, map_inv, hab,
        mul_inv_cancel]⟩
    rw [hJN, Subgroup.mem_bot, mul_inv_eq_one] at h1
    exact h1
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
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : π ((x : H) ^ 2 ^ k) = π 1 := by
        rw [map_pow, map_one]
        exact congrArg Subtype.val hk
      exact hJinj _ (J.pow_mem (Subgroup.mem_inf.mp x.2).2 _) _ J.one_mem h1
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
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : π ((x : H) ^ 2 ^ k) = π 1 := by
      rw [map_pow, map_one]
      exact congrArg Subtype.val hk
    exact hJinj _ (J.pow_mem x.2 _) _ J.one_mem h1

end CFSG.RankThree.PartTwo.Census
