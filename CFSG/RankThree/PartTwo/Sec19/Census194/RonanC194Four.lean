module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.SectionRank

theorem four_le_pRank_of_gens {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {x y z w : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hxw : Commute x w) (hyz : Commute y z)
    (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) (hz1 : ∀ n m : ℕ, x ^ n * y ^ m ≠ z)
    (hw1 : ∀ n m k : ℕ, x ^ n * y ^ m * z ^ k ≠ w) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  set B₀ : Subgroup G := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := exists_extend hc₀ hp₀ hcard₀ B₀.subtype
    Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := exists_extend hc₁ hp₁ hcard₁ F₁ hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ n m : ℕ, F₂ a = x ^ n * y ^ m := fun a => by
    obtain ⟨b, m, hb⟩ := hr₂ a
    obtain ⟨n, hn⟩ := hr₁' b
    exact ⟨n, m, by rw [hb, hn]⟩
  obtain ⟨F₃, hF₃, hc₃, hp₃, hcard₃, hr₃⟩ := exists_extend hc₂ hp₂ hcard₂ F₂ hF₂ (y := z) hz
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, hnm⟩ := hr₂' a
      exact hz1 n m (hnm ▸ ha))
    (fun a => by
      obtain ⟨n, m, hnm⟩ := hr₂' a
      rw [hnm]
      exact (hxz.pow_left n).mul_left (hyz.pow_left m))
  have hr₃' : ∀ a, ∃ n m k : ℕ, F₃ a = x ^ n * y ^ m * z ^ k := fun a => by
    obtain ⟨b, k, hb⟩ := hr₃ a
    obtain ⟨n, m, hnm⟩ := hr₂' b
    exact ⟨n, m, k, by rw [hb, hnm]⟩
  obtain ⟨F₄, hF₄, hc₄, hp₄, hcard₄, -⟩ := exists_extend hc₃ hp₃ hcard₃ F₃ hF₃ (y := w) hw
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, m, k, hnmk⟩ := hr₃' a
      exact hw1 n m k (hnmk ▸ ha))
    (fun a => by
      obtain ⟨n, m, k, hnmk⟩ := hr₃' a
      rw [hnmk]
      exact ((hxw.pow_left n).mul_left (hyw.pow_left m)).mul_left (hzw.pow_left k))
  exact le_pRank_of_injective hp.out.one_lt hc₄ hp₄ hcard₄ F₄ hF₄ le_top

theorem four_le_pRank_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {H : Subgroup (GL ι K)} {p : ℕ} [hp : Fact p.Prime] {x y z w : GL ι K}
    (hxH : x ∈ H) (hyH : y ∈ H) (hzH : z ∈ H) (hwH : w ∈ H)
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hz : z ^ p = 1) (hw : w ^ p = 1)
    (hxy : Commute x y) (hxz : Commute x z) (hxw : Commute x w) (hyz : Commute y z)
    (hyw : Commute y w) (hzw : Commute z w)
    (hx1 : x ∉ StatedScalars ι K)
    (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y)
    (hz1 : ∀ n m : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * c ≠ z)
    (hw1 : ∀ n m k : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * y ^ m * z ^ k * c ≠ w) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj H)) := by
  let N := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ p = 1 → π ⟨a, ha⟩ ^ p = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ p = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  have hcomm : ∀ (a b : GL ι K) (ha : a ∈ H) (hb : b ∈ H), Commute a b →
      Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := fun a b ha hb h =>
    Commute.map (show Commute (⟨a, ha⟩ : H) ⟨b, hb⟩ from Subtype.ext h.eq) π
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  refine four_le_pRank_of_gens (hpow x hxH hx) (hpow y hyH hy) (hpow z hzH hz)
    (hpow w hwH hw) (hcomm _ _ _ _ hxy) (hcomm _ _ _ _ hxz) (hcomm _ _ _ _ hxw)
    (hcomm _ _ _ _ hyz) (hcomm _ _ _ _ hyw) (hcomm _ _ _ _ hzw) (fun h => hx1 ?_)
    (fun n h => ?_) (fun n m h => ?_) (fun n m k h => ?_)
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)
  · rw [← map_pow, ← map_pow, ← map_mul] at h
    have := hmem _ _ h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at this
    exact hz1 n m _ this (mul_inv_cancel_left _ _)
  · rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
    have := hmem _ _ h
    simp only [Subgroup.coe_mul, SubgroupClass.coe_pow] at this
    exact hw1 n m k _ this (mul_inv_cancel_left _ _)

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
