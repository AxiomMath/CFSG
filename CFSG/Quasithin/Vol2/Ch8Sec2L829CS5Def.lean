module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Def

variable {Y : Type} [Group Y]

@[expose] def centerSub (S : Subgroup Y) : Subgroup Y := (Subgroup.center ↥S).map S.subtype

theorem mem_centerSub_cs5 {S : Subgroup Y} {z : Y} :
    z ∈ centerSub S ↔ z ∈ S ∧ ∀ s ∈ S, s * z = z * s := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun s hs => ?_⟩
    have := Subgroup.mem_center_iff.mp hx ⟨s, hs⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, hc⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hc s s.2), rfl⟩

theorem centerSub_le_cs5 (S : Subgroup Y) : centerSub S ≤ S := fun _ hz =>
  (mem_centerSub_cs5.mp hz).1

theorem conj_mem_centerSub_cs5 {S : Subgroup Y} {b : Y} (hb : b ∈ Subgroup.normalizer (S : Set Y))
    {z : Y} (hz : z ∈ centerSub S) : b * z * b⁻¹ ∈ centerSub S := by
  obtain ⟨hzS, hzc⟩ := mem_centerSub_cs5.mp hz
  rw [mem_centerSub_cs5]
  refine ⟨(Subgroup.mem_normalizer_iff.mp hb z).mp hzS, fun s hs => ?_⟩
  have hs' : b⁻¹ * s * b ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb) s).mp hs
    simpa using this
  calc s * (b * z * b⁻¹) = b * ((b⁻¹ * s * b) * z) * b⁻¹ := by group
    _ = b * (z * (b⁻¹ * s * b)) * b⁻¹ := by rw [hzc _ hs']
    _ = b * z * b⁻¹ * s := by group

theorem exists_two_pow_eq_one_of_mem_cs5 {S : Subgroup Y} (hS : IsPGroup 2 S) {s : Y}
    (hs : s ∈ S) : ∃ k : ℕ, s ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem pow_two_pow_conj_cs5 (g t : Y) {k : ℕ} (h : t ^ 2 ^ k = 1) :
    (g⁻¹ * t * g) ^ 2 ^ k = 1 := by
  have : g⁻¹ * t * g = g⁻¹ * t * g⁻¹⁻¹ := by rw [inv_inv]
  rw [this, conj_pow, h]
  simp

structure RankOneSyl (X S : Subgroup Y) (q : ℕ) : Prop where
  sylow : IsSylowTwoOf S X
  ti : ∀ g ∈ X, g ∉ Subgroup.normalizer (S : Set Y) → S ⊓ B6.conjSub g S = ⊥
  index : (X ⊓ Subgroup.normalizer (S : Set Y)).relIndex X = Nat.card S + 1
  core : ∀ N : Subgroup Y, N ≤ X ⊓ Subgroup.normalizer (S : Set Y) →
    (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N = ⊥
  zcard : Nat.card ↥(centerSub S) = q
  zexp : ∀ z ∈ centerSub S, z * z = 1
  ztrans : ∀ z ∈ centerSub S, z ≠ 1 → ∀ z' ∈ centerSub S, z' ≠ 1 →
    ∃ b ∈ X ⊓ Subgroup.normalizer (S : Set Y), b * z * b⁻¹ = z'
  omega1 : ∀ x ∈ S, x * x = 1 → x ∈ centerSub S
  three_le : 3 ≤ q

variable {X S : Subgroup Y} {q : ℕ}

theorem RankOneSyl.le (hR : RankOneSyl X S q) : S ≤ X := hR.sylow.1

theorem RankOneSyl.isPGroup (hR : RankOneSyl X S q) : IsPGroup 2 S := hR.sylow.2.1

theorem centerSub_ne_bot_cs5 (hR : RankOneSyl X S q) : centerSub S ≠ ⊥ := by
  intro h
  have h1 := hR.zcard
  rw [h, Subgroup.card_bot] at h1
  have := hR.three_le
  omega


end Def

end CFSG.Quasithin.H13
