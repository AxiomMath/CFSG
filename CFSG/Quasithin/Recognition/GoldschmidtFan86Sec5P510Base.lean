module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4ZtMain
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Line

variable (ℓ : Line Γ)

theorem mem_edgeStab_iff {i : ℤ} {g : G} :
    g ∈ ℓ.edgeStab (G := G) i ↔
      g • ℓ.vert i = ℓ.vert i ∧ g • ℓ.vert (i + 1) = ℓ.vert (i + 1) := by
  simp [edgeStab, MulAction.mem_stabilizer_iff]

theorem zz_subset_zc {z : G} (hz : z ∈ ℓ.ZZ) : z ∈ ℓ.Zc := by
  obtain ⟨hzz, i, hzs, hzc⟩ := hz
  refine ⟨hzz, i, ?_, fun h hh => hzc h ?_⟩
  · have hzf := (ℓ.mem_edgeStab_iff).1 hzs
    by_cases h5 : valence Γ (ℓ.vert i) = 5
    · rw [ℓ.edgeCirc_of_five h5]
      exact ⟨⟨MulAction.mem_stabilizer_iff.2 hzf.1, MulAction.mem_stabilizer_iff.2 hzf.2⟩,
        by rw [hzz]; exact one_mem _⟩
    · rw [ℓ.edgeCirc_of_ne_five h5]
      exact ⟨⟨MulAction.mem_stabilizer_iff.2 hzf.2, MulAction.mem_stabilizer_iff.2 hzf.1⟩,
        by rw [hzz]; exact one_mem _⟩
  · exact (ℓ.mem_edgeStab_iff).2 (ℓ.edgeCirc_fix hh)

theorem exists_core {z : G} {i₀ tL tR : ℤ} (hc : z ∈ Cen (ℓ.edgeStab (G := G) i₀ : Set G))
    (hfix : ∀ i, i ∈ ℓ.fixIdx z ↔ tL ≤ i ∧ i ≤ tR) : ∃ a b : ℤ, ℓ.IsCore z a b := by
  classical
  set cen : ℤ → Prop := fun i => z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) with hcen
  have hf0 : ∀ i, cen i → z • ℓ.vert i = ℓ.vert i ∧ z • ℓ.vert (i + 1) = ℓ.vert (i + 1) :=
    fun i hi => (ℓ.mem_edgeStab_iff).1 hi.1
  have hL : ∃ a : ℤ, (a ≤ i₀ ∧ ∀ i, a ≤ i → i ≤ i₀ → cen i) ∧
      ∀ j, (j ≤ i₀ ∧ ∀ i, j ≤ i → i ≤ i₀ → cen i) → a ≤ j := by
    refine Int.exists_least_of_bdd (P := fun j => j ≤ i₀ ∧ ∀ i, j ≤ i → i ≤ i₀ → cen i)
      ⟨tL, fun j hj => ?_⟩ ⟨i₀, le_rfl, fun i h1 h2 => by rwa [show i = i₀ by omega]⟩
    exact ((hfix j).1 (hf0 j (hj.2 j le_rfl hj.1)).1).1
  have hR : ∃ b : ℤ, (i₀ + 1 ≤ b ∧ ∀ i, i₀ ≤ i → i < b → cen i) ∧
      ∀ k, (i₀ + 1 ≤ k ∧ ∀ i, i₀ ≤ i → i < k → cen i) → k ≤ b := by
    refine Int.exists_greatest_of_bdd (P := fun k => i₀ + 1 ≤ k ∧ ∀ i, i₀ ≤ i → i < k → cen i)
      ⟨tR, fun k hk => ?_⟩ ⟨i₀ + 1, le_rfl, fun i h1 h2 => by rwa [show i = i₀ by omega]⟩
    have := (hf0 (k - 1) (hk.2 (k - 1) (by omega) (by omega))).2
    rw [show k - 1 + 1 = k by omega] at this
    exact ((hfix k).1 this).2
  obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := hL
  obtain ⟨b, ⟨hb1, hb2⟩, hb3⟩ := hR
  have hcen : ∀ i, a ≤ i → i < b → cen i := fun i h1 h2 => by
    by_cases h : i ≤ i₀
    · exact ha2 i h1 h
    · exact hb2 i (by omega) h2
  refine ⟨a, b, by omega, fun i h1 h2 => ?_, hcen, ?_, ?_⟩
  · by_cases h : i < b
    · exact (hf0 i (hcen i h1 h)).1
    · have hib : i = b := by omega
      have := (hf0 (b - 1) (hcen (b - 1) (by omega) (by omega))).2
      rw [show b - 1 + 1 = b by omega] at this
      rw [hib]
      exact this
  · rintro ⟨-, h⟩
    have := ha3 (a - 1) ⟨by omega, fun i h1 h2 => by
      by_cases hi : i = a - 1
      · rwa [hi]
      · exact ha2 i (by omega) h2⟩
    omega
  · rintro ⟨-, h⟩
    have := hb3 (b + 1) ⟨by omega, fun i h1 h2 => by
      by_cases hi : i = b
      · rwa [hi]
      · exact hb2 i h1 (by omega)⟩
    omega

end Line

theorem exists_fixInterval (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h48 : Fan48Two F) (T : Track Γ G) {z : G} (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1) :
    ∃ tL tR : ℤ, ∀ i, i ∈ T.line.fixIdx z ↔ tL ≤ i ∧ i ≤ tR := by
  classical
  obtain ⟨-, i₀, hzs, hzc⟩ := hz
  have hi0 : z • T.line.vert i₀ = T.line.vert i₀ := ((T.line.mem_edgeStab_iff).1 hzs).1
  have hnot : ¬ ∀ i, z • T.line.vert i = T.line.vert i := fun hall =>
    hz1 (fan49 F h40 h28 h33 h48 T i₀ z ((T.mem_fixer).2 hall) fun g hg => hzc g hg)
  have hfix : ∀ i, i ∈ T.fixSet (Subgroup.zpowers z) ↔ z • T.line.vert i = T.line.vert i := by
    intro i
    constructor
    · exact fun h => h z (Subgroup.mem_zpowers z)
    · intro h g hg
      exact MulAction.mem_stabilizer_iff.1
        ((Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h)) hg)
  rcases T.fixSet_eq_univ_or_bounded F.isTree F.adj_smul F.loc_finite (Subgroup.zpowers z) with
    h | ⟨A, B, hAB⟩
  · exact absurd (fun i => (hfix i).1 (by rw [h]; trivial)) hnot
  · obtain ⟨tR, htR, hRmax⟩ := Int.exists_greatest_of_bdd
      (P := fun i => z • T.line.vert i = T.line.vert i)
      ⟨B, fun i hi => (hAB i ((hfix i).2 hi)).2⟩ ⟨i₀, hi0⟩
    obtain ⟨tL, htL, hLmin⟩ := Int.exists_least_of_bdd
      (P := fun i => z • T.line.vert i = T.line.vert i)
      ⟨A, fun i hi => (hAB i ((hfix i).2 hi)).1⟩ ⟨i₀, hi0⟩
    exact ⟨tL, tR, fun i => ⟨fun hi => ⟨hLmin i hi, hRmax i hi⟩, fun hi =>
      Line.fixes_between F.isTree F.adj_smul T.line hi.1 hi.2 htL htR⟩⟩

theorem exists_coreFix (F : FanTree Γ G) (h40 : Fan40 F) (h28 : Fan28) (h33 : Fan33 F)
    (h48 : Fan48Two F) (T : Track Γ G) {z : G} (hz : z ∈ T.line.ZZ) (hz1 : z ≠ 1) :
    ∃ a b tL tR : ℤ, T.line.IsCoreFix z a b tL tR := by
  obtain ⟨tL, tR, hfix⟩ := exists_fixInterval F h40 h28 h33 h48 T hz hz1
  obtain ⟨-, i₀, hc⟩ := hz
  obtain ⟨a, b, hcore⟩ := Line.exists_core T.line hc hfix
  exact ⟨a, b, tL, tR, ⟨hfix, hcore⟩⟩

end CFSG.Quasithin.Fan86
