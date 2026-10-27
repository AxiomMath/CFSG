module

public import CFSG.RankThree.GF2n.BenderStrongWC

public section

namespace CFSG.RankThree.GF2n

open CFSG.CGT.Timmesfeld75 CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

variable {K : Type} [Group K]

theorem StrongWC.conj {T : Subgroup K} (hT : StrongWC T) (x : K) : StrongWC (conjSubgroup x T) := by
  refine ⟨?_, fun t ht ht1 a ha g hg => ?_⟩
  · obtain ⟨⟨hc⟩, h2⟩ := hT.1
    refine ⟨⟨⟨fun p q => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · have hp := mem_conjSubgroup.mp p.2
      have hq := mem_conjSubgroup.mp q.2
      have h := congrArg Subtype.val (hc.comm ⟨_, hp⟩ ⟨_, hq⟩)
      have h' : x⁻¹ * ((p : K) * q) * x = x⁻¹ * ((q : K) * p) * x := by
        simpa [mul_assoc] using h
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mul_left_cancel (mul_right_cancel h')
    · have h := h2 _ (mem_conjSubgroup.mp hy)
      rw [show (x⁻¹ * y * x) ^ 2 = x⁻¹ * y ^ 2 * x by rw [sq, sq]; group] at h
      calc y ^ 2 = x * (x⁻¹ * y ^ 2 * x) * x⁻¹ := by group
        _ = 1 := by rw [h]; group
  · have ht' := mem_conjSubgroup.mp ht
    have ha' := mem_conjSubgroup.mp ha
    have ht1' : x⁻¹ * t * x ≠ 1 := fun h => ht1 (by
      rw [show t = x * (x⁻¹ * t * x) * x⁻¹ by group, h]; group)
    have hg' : (x⁻¹ * g * x)⁻¹ * (x⁻¹ * a * x) * (x⁻¹ * g * x) ∈
        Subgroup.centralizer ({x⁻¹ * t * x} : Set K) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
      calc (x⁻¹ * g * x)⁻¹ * (x⁻¹ * a * x) * (x⁻¹ * g * x) * (x⁻¹ * t * x) =
          x⁻¹ * (g⁻¹ * a * g * t) * x := by group
        _ = x⁻¹ * (t * (g⁻¹ * a * g)) * x := by rw [hg]
        _ = (x⁻¹ * t * x) * ((x⁻¹ * g * x)⁻¹ * (x⁻¹ * a * x) * (x⁻¹ * g * x)) := by group
    have h := hT.2 _ ht' ht1' _ ha' _ hg'
    rw [mem_conjSubgroup]
    rw [show (x⁻¹ * g * x)⁻¹ * (x⁻¹ * a * x) * (x⁻¹ * g * x) = x⁻¹ * (g⁻¹ * a * g) * x by group]
      at h
    exact h

theorem mem_smul_sylow_iff {P : Sylow 2 K} {k z : K} :
    z ∈ ((k • P : Sylow 2 K) : Subgroup K) ↔ k⁻¹ * z * k ∈ (P : Subgroup K) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

variable [Finite K]

theorem exists_borel_smul_eq {n i e : ℕ} (h : BenderType K n i e) {Q P P' : Sylow 2 K}
    (hP : P ≠ Q) (hP' : P' ≠ Q) : ∃ m ∈ borel (Q : Subgroup K), m • P = P' := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have key : ∀ R : Sylow 2 K, R ≠ Q → ∃ p ∈ (Q : Subgroup K), R = (p * t) • Q := by
    intro R hR
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q R
    have hgB : g ∉ borel (Q : Subgroup K) := fun hgN =>
      hR (by rw [← hg]; exact Sylow.smul_eq_iff_mem_normalizer.mpr hgN)
    obtain ⟨p, hp, m, hm, rfl⟩ := hc.bruhat hgB
    exact ⟨p, hp, by rw [← hg, mul_smul, Sylow.smul_eq_iff_mem_normalizer.mpr hm]⟩
  obtain ⟨p, hp, rfl⟩ := key P hP
  obtain ⟨p', hp', rfl⟩ := key P' hP'
  refine ⟨p' * p⁻¹, le_borel _ ((Q : Subgroup K).mul_mem hp' ((Q : Subgroup K).inv_mem hp)), ?_⟩
  rw [← mul_smul, show p' * p⁻¹ * (p * t) = p' * t by group]

omit [Finite K] in
theorem eq_one_of_odd_of_mul_self {x : K} (hx : x * x = 1) (hodd : Odd (orderOf x)) : x = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [sq]; exact hx)) with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · rw [h1] at hodd
    exact absurd hodd (by decide)

omit [Finite K] in
theorem exists_sylow_mem_of_mul_self {y : K} (hy : y * y = 1) : ∃ P : Sylow 2 K, y ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (Subgroup.zpowers y) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨P, hP⟩ := h2.exists_le_sylow
  exact ⟨P, hP (Subgroup.mem_zpowers y)⟩

omit [Finite K] in
theorem eq_one_of_odd_of_mem_sylow {P : Sylow 2 K} {g : K} (hg : g ∈ (P : Subgroup K))
    (hodd : Odd (orderOf g)) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨g, hg⟩
  rw [← Subgroup.orderOf_coe] at hk
  rw [hk] at hodd
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩))

theorem exists_mul_orderOf_eq {n i e : ℕ} (h : BenderType K n i e) {T T' : Subgroup K}
    (hT : StrongWC T) (hT1 : T ≠ ⊥) (hT' : StrongWC T') (hT'1 : T' ≠ ⊥) (hne : T ≠ T')
    {u v : K} (hu : u * u = 1) (hv : v * v = 1) (huv : Odd (orderOf (u * v))) (huv1 : u * v ≠ 1) :
    ∃ t ∈ T, ∃ s ∈ T', orderOf (t * s) = orderOf (u * v) := by
  obtain ⟨Q, hQ⟩ := eq_rootCenter_of_strongWC h hT hT1
  obtain ⟨Q', hQ'⟩ := eq_rootCenter_of_strongWC h hT' hT'1
  have hQQ' : Q' ≠ Q := fun h' => hne (by rw [hQ, hQ', h'])
  obtain ⟨Q₁, hu₁⟩ := exists_sylow_mem_of_mul_self hu
  obtain ⟨Q₂, hv₂⟩ := exists_sylow_mem_of_mul_self hv
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K Q₁ Q
  have huc : c * u * c⁻¹ ∈ (Q : Subgroup K) := by
    rw [← hc, mem_smul_sylow_iff, show c⁻¹ * (c * u * c⁻¹) * c = u by group]
    exact hu₁
  have hvc : c * v * c⁻¹ ∈ ((c • Q₂ : Sylow 2 K) : Subgroup K) := by
    rw [mem_smul_sylow_iff, show c⁻¹ * (c * v * c⁻¹) * c = v by group]
    exact hv₂
  have hord : ∀ g : K, orderOf (g * (u * v) * g⁻¹) = orderOf (u * v) := fun g =>
    by simpa using orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective (u * v)
  have hPQ : c • Q₂ ≠ Q := by
    intro h'
    rw [h'] at hvc
    have h1 : c * (u * v) * c⁻¹ ∈ (Q : Subgroup K) := by
      rw [show c * (u * v) * c⁻¹ = (c * u * c⁻¹) * (c * v * c⁻¹) by group]
      exact (Q : Subgroup K).mul_mem huc hvc
    have h2 := eq_one_of_odd_of_mem_sylow h1 ((hord c).symm ▸ huv)
    apply huv1
    rw [show u * v = c⁻¹ * (c * (u * v) * c⁻¹) * c by group, h2]
    group
  obtain ⟨m, hm, hmP⟩ := exists_borel_smul_eq h hPQ hQQ'
  obtain ⟨t₀, hc₀⟩ := h.exists_benderCore Q
  obtain ⟨t₁, hc₁⟩ := h.exists_benderCore Q'
  have hinv : ∀ g : K, ∀ x : K, x * x = 1 → (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := fun g x hx => by
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hx]
    group
  have hne1 : ∀ g x : K, x * x = 1 → x ≠ 1 → orderOf (g * x * g⁻¹) = 2 := fun g x hx hx1 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [sq]; exact hinv g x hx) fun h' => hx1 ?_
    rw [show x = g⁻¹ * (g * x * g⁻¹) * g by group, h']
    group
  have hu1 : u ≠ 1 := fun h' => by
    rw [h', one_mul] at huv1 huv
    exact huv1 (eq_one_of_odd_of_mul_self hv huv)
  have hv1 : v ≠ 1 := fun h' => by
    rw [h', mul_one] at huv1 huv
    exact huv1 (eq_one_of_odd_of_mul_self hu huv)
  refine ⟨m * (c * u * c⁻¹) * m⁻¹, ?_, m * (c * v * c⁻¹) * m⁻¹, ?_, ?_⟩
  · rw [hQ]
    refine hc₀.center_of_involution _ (le_borel _ ?_) ?_
    · have := (Subgroup.mem_normalizer_iff.mp hm (c * u * c⁻¹)).mp huc
      exact this
    · rw [show m * (c * u * c⁻¹) * m⁻¹ = (m * c) * u * (m * c)⁻¹ by group]
      exact hne1 _ u hu hu1
  · rw [hQ']
    refine hc₁.center_of_involution _ (le_borel _ ?_) ?_
    · rw [← hmP, mem_smul_sylow_iff, show m⁻¹ * (m * (c * v * c⁻¹) * m⁻¹) * m = c * v * c⁻¹ by
        group]
      exact hvc
    · rw [show m * (c * v * c⁻¹) * m⁻¹ = (m * c) * v * (m * c)⁻¹ by group]
      exact hne1 _ v hv hv1
  · rw [show m * (c * u * c⁻¹) * m⁻¹ * (m * (c * v * c⁻¹) * m⁻¹) =
      (m * c) * (u * v) * (m * c)⁻¹ by group, hord]

end CFSG.RankThree.GF2n
