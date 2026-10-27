module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin

theorem s16g_card_pair_subgroup {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x y : G}
    (hxy : Commute x y) (hx : orderOf x = p) (hy : orderOf y = p)
    (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 ∧
      ∀ b ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G), b ^ p = 1 := by
  have hcomm : ∀ (m : Subgroup.zpowers x) (n : Subgroup.zpowers y),
      Commute ((Subgroup.zpowers x).subtype m) ((Subgroup.zpowers y).subtype n) := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact hxy.zpow_zpow a b
  haveI : Fact (Nat.card (Subgroup.zpowers y)).Prime :=
    ⟨by rw [Nat.card_zpowers, hy]; exact hp⟩
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro z hzx hzy
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers x).subgroupOf (Subgroup.zpowers y)) with h | h
    · have hz : (⟨z, hzy⟩ : Subgroup.zpowers y) ∈
          (Subgroup.zpowers x).subgroupOf (Subgroup.zpowers y) := hzx
      rw [h, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    · exact absurd (show (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) ∈
        (Subgroup.zpowers x).subgroupOf (Subgroup.zpowers y) by rw [h]; trivial) hyx
  have hinj : Function.Injective (MonoidHom.noncommCoprod (Subgroup.zpowers x).subtype
      (Subgroup.zpowers y).subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨Subtype.coe_injective, Subtype.coe_injective,
      by simpa [Subgroup.range_subtype] using hdisj⟩
  have hrange : (MonoidHom.noncommCoprod (Subgroup.zpowers x).subtype
      (Subgroup.zpowers y).subtype hcomm).range = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hpow : ∀ {z : G}, orderOf z = p → ∀ a ∈ Subgroup.zpowers z, a ^ p = 1 := by
    intro z hz a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hz,
      pow_orderOf_eq_one, _root_.one_zpow]
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, Nat.card_zpowers, hx, hy, sq]
  · rw [← hrange] at hb
    obtain ⟨⟨a, c⟩, rfl⟩ := hb
    have ha : a ^ p = 1 := Subtype.ext (by simpa using hpow hx a a.2)
    have hc : c ^ p = 1 := Subtype.ext (by simpa using hpow hy c c.2)
    rw [← map_pow, Prod.pow_mk, ha, hc]
    exact map_one _

private def s16g_stab {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] (u : ι → K) :
    Subgroup (Matrix.GeneralLinearGroup ι K) where
  carrier := {b | (b : Matrix ι ι K) *ᵥ u = u}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change ((a * b : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u = u
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    change (a : Matrix ι ι K) *ᵥ u = u at ha
    change (b : Matrix ι ι K) *ᵥ u = u at hb
    rw [hb, ha]
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u = u
    change (a : Matrix ι ι K) *ᵥ u = u at ha
    conv_lhs => rw [← ha]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem s16g_fixed_of_pair {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {x y : Matrix.GeneralLinearGroup ι K} {u : ι → K} (hxu : (x : Matrix ι ι K) *ᵥ u = u)
    (hyu : (y : Matrix ι ι K) *ᵥ u = u) :
    ∀ b ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup (Matrix.GeneralLinearGroup ι K)),
      (b : Matrix ι ι K) *ᵥ u = u := fun b hb =>
  (sup_le ((Subgroup.zpowers_le).2 (show x ∈ s16g_stab u from hxu))
    ((Subgroup.zpowers_le).2 (show y ∈ s16g_stab u from hyu)) : _ ≤ s16g_stab u) hb

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem s16g_fixNc_of_fixed_pair (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {p : ℕ}
    (hp : p.Prime)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {x y : Matrix.GeneralLinearGroup ι K} (hxΓ : x ∈ Γ) (hyΓ : y ∈ Γ) (hxy : Commute x y)
    (hx : orderOf x = p) (hy : orderOf y = p) (hyx : y ∉ Subgroup.zpowers x) {u : ι → K}
    (hu : u ≠ 0) (hxu : (x : Matrix ι ι K) *ᵥ u = u) (hyu : (y : Matrix ι ι K) *ᵥ u = u) :
    FixNc Γ p := by
  obtain ⟨hcard, hexp⟩ := s16g_card_pair_subgroup hp hxy hx hy hyx
  exact s16g_fixNc_of_fixed_vector Γ hp htr
    (sup_le ((Subgroup.zpowers_le).2 hxΓ) ((Subgroup.zpowers_le).2 hyΓ)) hcard hexp hu
    (s16g_fixed_of_pair hxu hyu)

theorem s16g_fixNc_of_fixed_pair_singular [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΓQ : ∀ A ∈ Γ, ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q x = Q y → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {x y : Matrix.GeneralLinearGroup ι K} (hxΓ : x ∈ Γ) (hyΓ : y ∈ Γ) (hxy : Commute x y)
    (hx : orderOf x = p) (hy : orderOf y = p) (hyx : y ∉ Subgroup.zpowers x) {u : ι → K}
    (hu : u ≠ 0) (hQu : Q u = 0) (hxu : (x : Matrix ι ι K) *ᵥ u = u)
    (hyu : (y : Matrix ι ι K) *ᵥ u = u) : FixNc Γ p := by
  obtain ⟨hcard, hexp⟩ := s16g_card_pair_subgroup hp hxy hx hy hyx
  exact s16g_fixNc_of_fixed_singular Q hQ Γ hp hp2 hΓQ htr
    (sup_le ((Subgroup.zpowers_le).2 hxΓ) ((Subgroup.zpowers_le).2 hyΓ)) hcard hexp hu hQu
    (s16g_fixed_of_pair hxu hyu)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
