module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Defs

public section

namespace CFSG.Quasithin.Fan86

namespace P514

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_fixIdx_interval' (F : FanTree Γ G) (T : Track Γ G) {g : G}
    (hg : g ∉ T.fixer) {i₀ : ℤ} (hi : i₀ ∈ T.line.fixIdx g) :
    ∃ tL tR : ℤ, ∀ i, i ∈ T.line.fixIdx g ↔ tL ≤ i ∧ i ≤ tR := by
  classical
  have hset : T.fixSet (Subgroup.zpowers g) = T.line.fixIdx g := by
    ext i
    refine ⟨fun h => h g (Subgroup.mem_zpowers g), fun h k hk => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hh : g • T.line.vert i = T.line.vert i := h
    clear hk
    induction n using Int.induction_on with
    | zero => simp
    | succ m ih => rw [zpow_add_one, mul_smul, hh, ih]
    | pred m ih =>
      rw [zpow_sub_one, mul_smul, inv_smul_eq_iff.2 hh.symm]
      exact ih
  rcases T.fixSet_eq_univ_or_bounded F.isTree F.adj_smul F.loc_finite
      (Subgroup.zpowers g) with hu | ⟨lo, hi', hb⟩
  · exfalso
    apply hg
    exact (T.mem_fixer).2 fun i => by
      have : i ∈ T.fixSet (Subgroup.zpowers g) := by rw [hu]; trivial
      rw [hset] at this
      exact this
  · rw [hset] at hb
    obtain ⟨tL, htL, hmin⟩ := Int.exists_least_of_bdd (P := fun i => i ∈ T.line.fixIdx g)
      ⟨lo, fun i hi => (hb i hi).1⟩ ⟨i₀, hi⟩
    obtain ⟨tR, htR, hmax⟩ := Int.exists_greatest_of_bdd (P := fun i => i ∈ T.line.fixIdx g)
      ⟨hi', fun i hi => (hb i hi).2⟩ ⟨i₀, hi⟩
    refine ⟨tL, tR, fun i => ⟨fun h => ⟨hmin i h, hmax i h⟩, fun ⟨h1, h2⟩ => ?_⟩⟩
    exact Line.fixes_between F.isTree F.adj_smul T.line h1 h2 htL htR

theorem exists_fixIdx_interval (F : FanTree Γ G) (T : Track Γ G) (hT : T.fixer = ⊥) {g : G}
    (hg : g ≠ 1) {i₀ : ℤ} (hi : i₀ ∈ T.line.fixIdx g) :
    ∃ tL tR : ℤ, ∀ i, i ∈ T.line.fixIdx g ↔ tL ≤ i ∧ i ≤ tR :=
  exists_fixIdx_interval' F T (fun h => hg (by rw [hT] at h; exact Subgroup.mem_bot.1 h)) hi

theorem exists_isCoreWith (ℓ : Line Γ) {P : ℤ → Prop} {z : G} {tL tR i : ℤ}
    (hfix : ∀ k, k ∈ ℓ.fixIdx z ↔ tL ≤ k ∧ k ≤ tR)
    (hP : ∀ k, P k → k ∈ ℓ.fixIdx z ∧ k + 1 ∈ ℓ.fixIdx z) (hi : P i) :
    ∃ a b : ℤ, a ≤ i ∧ i < b ∧ ℓ.IsCoreWith P z a b := by
  classical
  have hiL : tL ≤ i := ((hfix i).1 (hP i hi).1).1
  have hiR : i + 1 ≤ tR := ((hfix (i + 1)).1 (hP i hi).2).2
  obtain ⟨a, ⟨ha1, ha2, ha3⟩, hamin⟩ := Int.exists_least_of_bdd
    (P := fun a => tL ≤ a ∧ a ≤ i ∧ ∀ k, a ≤ k → k ≤ i → P k)
    ⟨tL, fun a ha => ha.1⟩ ⟨i, hiL, le_rfl, fun k h1 h2 => by
      have : k = i := le_antisymm h2 h1
      rwa [this]⟩
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, hbmax⟩ := Int.exists_greatest_of_bdd
    (P := fun b => i < b ∧ b ≤ tR ∧ ∀ k, i ≤ k → k < b → P k)
    ⟨tR, fun b hb => hb.2.1⟩ ⟨i + 1, by omega, hiR, fun k h1 h2 => by
      have : k = i := by omega
      rwa [this]⟩
  refine ⟨a, b, ha2, hb1, by omega, fun k h1 h2 => (hfix k).2 ⟨by omega, by omega⟩,
    fun k h1 h2 => ?_, ?_, ?_⟩
  · by_cases hk : k ≤ i
    · exact ha3 k h1 hk
    · exact hb3 k (by omega) h2
  · rintro ⟨h1, h2⟩
    have := hamin (a - 1) ⟨((hfix _).1 h1).1, by omega, fun k hk1 hk2 => by
      by_cases hk : k = a - 1
      · rw [hk]; exact h2
      · exact ha3 k (by omega) hk2⟩
    omega
  · rintro ⟨h1, h2⟩
    have := hbmax (b + 1) ⟨by omega, ((hfix _).1 (hP b h2).2).2, fun k hk1 hk2 => by
      by_cases hk : k = b
      · rw [hk]; exact h2
      · exact hb3 k hk1 (by omega)⟩
    omega

end P514

end CFSG.Quasithin.Fan86
