module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Smith81.LinCount

open scoped commutatorElement

private theorem comm_comm_eq_inv_sq {G : Type*} [Group G] {s u : G} (hs : s * s = 1) :
    ⁅s, ⁅s, u⁆⁆ = (⁅s, u⁆ * ⁅s, u⁆)⁻¹ := by
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h1 : s * ⁅s, u⁆ * s⁻¹ = ⁅s, u⁆⁻¹ := by
    calc s * ⁅s, u⁆ * s⁻¹ = (s * s) * u * s⁻¹ * u⁻¹ * s⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = u * s⁻¹ * u⁻¹ * s⁻¹ := by rw [hs, one_mul]
      _ = u * s * u⁻¹ * s⁻¹ := by rw [hsi]
      _ = ⁅s, u⁆⁻¹ := by
          simp only [commutatorElement_def]
          group
  calc ⁅s, ⁅s, u⁆⁆ = s * ⁅s, u⁆ * s⁻¹ * ⁅s, u⁆⁻¹ := commutatorElement_def _ _
    _ = ⁅s, u⁆⁻¹ * ⁅s, u⁆⁻¹ := by rw [h1]
    _ = (⁅s, u⁆ * ⁅s, u⁆)⁻¹ := (mul_inv_rev _ _).symm

theorem lin_card_le_of_fixed {G : Type*} [Group G] [Finite G] {V D S Z : Subgroup G}
    (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v * v = 1)
    (hZD : Z ≤ D) (hDV : D ≤ V) (hDne : ∃ u ∈ V, u ∉ D)
    (hSN : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V) (hS2 : ∀ s ∈ S, s * s = 1)
    (hfix : ∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ = d)
    (hker : ∀ s ∈ S, s ≠ 1 → ∀ v ∈ V, ⁅s, v⁆ ∈ Z → v ∈ D) :
    Nat.card S * Nat.card Z ≤ Nat.card D := by
  obtain ⟨u, huV, huD⟩ := hDne
  have hεV : ∀ s ∈ S, ⁅s, u⁆ ∈ V := fun s hs => by
    rw [commutatorElement_def]
    exact V.mul_mem (hSN s hs u huV) (V.inv_mem huV)
  have hεD : ∀ s ∈ S, ⁅s, u⁆ ∈ D := by
    intro s hs
    by_cases h1 : s = 1
    · rw [h1, commutatorElement_one_left]
      exact D.one_mem
    · refine hker s hs h1 _ (hεV s hs) ?_
      rw [comm_comm_eq_inv_sq (hS2 s hs), hV2 _ (hεV s hs), inv_one]
      exact Z.one_mem
  have hmul : ∀ s ∈ S, ∀ t ∈ S, ⁅s * t, u⁆ = ⁅s, u⁆ * ⁅t, u⁆ := by
    intro s hs t ht
    have h1 : ⁅s * t, u⁆ = (s * ⁅t, u⁆ * s⁻¹) * ⁅s, u⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1, hfix s hs _ (hεD t ht)]
    exact hVab _ (hεV t ht) _ (hεV s hs)
  let f : ↥S × ↥Z → ↥D := fun p =>
    ⟨⁅(p.1 : G), u⁆ * (p.2 : G), D.mul_mem (hεD p.1 p.1.2) (hZD p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, ⟨z, hz⟩⟩ ⟨⟨s', hs'⟩, ⟨z', hz'⟩⟩ h
    have h1 : ⁅s, u⁆ * z = ⁅s', u⁆ * z' := congrArg Subtype.val h
    have hinv : ⁅s', u⁆⁻¹ = ⁅s', u⁆ := inv_eq_of_mul_eq_one_right (hV2 _ (hεV s' hs'))
    have h2 : ⁅s' * s, u⁆ ∈ Z := by
      have h3 : ⁅s' * s, u⁆ = z' * z⁻¹ := by
        rw [hmul s' hs' s hs]
        calc ⁅s', u⁆ * ⁅s, u⁆ = ⁅s', u⁆⁻¹ * (⁅s, u⁆ * z) * z⁻¹ := by
              rw [hinv]
              group
          _ = ⁅s', u⁆⁻¹ * (⁅s', u⁆ * z') * z⁻¹ := by rw [h1]
          _ = z' * z⁻¹ := by group
      rw [h3]
      exact Z.mul_mem hz' (Z.inv_mem hz)
    have h4 : s' * s = 1 := by
      by_contra hne
      exact huD (hker (s' * s) (S.mul_mem hs' hs) hne u huV h2)
    have h5 : s = s' :=
      (eq_inv_of_mul_eq_one_right h4).trans (inv_eq_of_mul_eq_one_right (hS2 s' hs'))
    obtain rfl : s = s' := h5
    obtain rfl : z = z' := mul_left_cancel h1
    rfl
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at h

private theorem mem_zpowers_cases {G : Type*} [Group G] {a : G} (ha : a * a = 1) {t : G}
    (ht : t ∈ Subgroup.zpowers a) : t = 1 ∨ t = a := by
  obtain ⟨n, rfl⟩ := ht
  show a ^ n = 1 ∨ a ^ n = a
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul, h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem comm_mem_of_stable {G : Type*} [Group G] {V : Subgroup G} {a : G}
    (haN : ∀ v ∈ V, a * v * a⁻¹ ∈ V) {v : G} (hv : v ∈ V) : ⁅a, v⁆ ∈ V := by
  rw [commutatorElement_def]
  exact V.mul_mem (haN v hv) (V.inv_mem hv)

private theorem comm_mul_of_abelian {G : Type*} [Group G] {V : Subgroup G} {a : G}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (haN : ∀ v ∈ V, a * v * a⁻¹ ∈ V)
    {v w : G} (hv : v ∈ V) (hw : w ∈ V) : ⁅a, v * w⁆ = ⁅a, v⁆ * ⁅a, w⁆ := by
  have h1 : v⁻¹ * (a * w * a⁻¹) = (a * w * a⁻¹) * v⁻¹ := hVab _ (V.inv_mem hv) _ (haN w hw)
  have h2 : v⁻¹ * w⁻¹ = w⁻¹ * v⁻¹ := hVab _ (V.inv_mem hv) _ (V.inv_mem hw)
  calc ⁅a, v * w⁆ = (a * v * a⁻¹) * (a * w * a⁻¹) * (w⁻¹ * v⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = (a * v * a⁻¹) * (a * w * a⁻¹) * (v⁻¹ * w⁻¹) := by rw [h2]
    _ = (a * v * a⁻¹) * (v⁻¹ * (a * w * a⁻¹)) * w⁻¹ := by
        rw [h1]
        group
    _ = ⁅a, v⁆ * ⁅a, w⁆ := by
        simp only [commutatorElement_def]
        group

theorem lin_card_preimage_Z {G : Type*} [Group G] [Finite G] {V Z : Subgroup G} {a : G}
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hZV : Z ≤ V)
    (haN : ∀ v ∈ V, a * v * a⁻¹ ∈ V) (ha2 : a * a = 1) :
    Nat.card {v : G // v ∈ V ∧ ⁅a, v⁆ ∈ Z} * Nat.card ↥(⁅V, Subgroup.zpowers a⁆ ⊔ Z) =
      Nat.card V * Nat.card Z := by
  obtain ⟨ν, hν⟩ : ∃ ν : ↥V →* G, ∀ v : ↥V, ν v = ⁅a, (v : G)⁆ :=
    ⟨{ toFun := fun v => ⁅a, (v : G)⁆
       map_one' := by simp
       map_mul' := fun v w => comm_mul_of_abelian hVab haN v.2 w.2 }, fun v => rfl⟩
  have hcomm : ∀ (v : ↥V) (z : ↥Z), Commute (ν v) (Z.subtype z) := fun v z => by
    rw [hν]
    exact hVab _ (comm_mem_of_stable haN v.2) _ (hZV z.2)
  obtain ⟨θ, hθ, hrange⟩ : ∃ θ : ↥V × ↥Z →* G, (∀ p, θ p = ν p.1 * (p.2 : G)) ∧
      θ.range = ν.range ⊔ Z :=
    ⟨MonoidHom.noncommCoprod ν Z.subtype hcomm, fun p => rfl, by
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype]⟩
  have hN : ν.range = ⁅V, Subgroup.zpowers a⁆ := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [hν, ← commutatorElement_inv]
      exact Subgroup.inv_mem _
        (Subgroup.commutator_mem_commutator v.2 (Subgroup.mem_zpowers a))
    · rw [Subgroup.commutator_le]
      intro q hq t ht
      rcases mem_zpowers_cases ha2 ht with rfl | rfl
      · rw [commutatorElement_one_right]
        exact one_mem _
      · have h1 : ⁅t, q⁆ ∈ ν.range := ⟨⟨q, hq⟩, hν _⟩
        have h2 := ν.range.inv_mem h1
        rwa [commutatorElement_inv] at h2
  have hkerdef : ∀ p : ↥V × ↥Z, p ∈ θ.ker ↔ ⁅a, (p.1 : G)⁆ * (p.2 : G) = 1 := fun p => by
    rw [MonoidHom.mem_ker, hθ, hν]
  have hker : Nat.card θ.ker = Nat.card {v : G // v ∈ V ∧ ⁅a, v⁆ ∈ Z} := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun v => ⟨(⟨v.1, v.2.1⟩, ⟨⁅a, v.1⁆⁻¹, Z.inv_mem v.2.2⟩), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := (hkerdef x.1).mp x.2
      rw [mul_eq_one_iff_eq_inv.mp h]
      exact Z.inv_mem x.1.2.2
    · rw [hkerdef]
      exact mul_inv_cancel _
    · intro x
      have h := (hkerdef x.1).mp x.2
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact Subtype.ext (eq_inv_of_mul_eq_one_right h).symm
    · intro v
      rfl
  have h := Subgroup.card_ker_mul_card_range θ
  rw [Nat.card_prod, hrange, hN, hker] at h
  exact h

end CFSG.RankThree.GF2n.Smith81.LinCount

end
