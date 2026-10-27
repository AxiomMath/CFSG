module

public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Quasithin
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem le_normalizer_of_isNormalIn_chief {H U N : Subgroup G} (h : IsNormalIn H U N) :
    H ≤ normalizer (N : Set G) := fun g hg => by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h.2 g hg x, fun hx => ?_⟩
  have h1 := h.2 g⁻¹ (inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem commutator_le_iff_isCentralStep {H L N : Subgroup G} :
    ⁅N, H⁆ ≤ L ↔ IsCentralStep H L N := by
  rw [commutator_le]
  constructor
  · intro h g hg x hx
    have h1 := inv_mem (h x hx g hg)
    rwa [commutatorElement_def, show (x * g * x⁻¹ * g⁻¹)⁻¹ = g * x * g⁻¹ * x⁻¹ by group] at h1
  · intro h x hx g hg
    rw [commutatorElement_def]
    have h1 := inv_mem (h g hg x hx)
    rwa [show (g * x * g⁻¹ * x⁻¹)⁻¹ = x * g * x⁻¹ * g⁻¹ by group] at h1

theorem chain_snoc {H U L N : Subgroup G} (hstep : IsChiefStep H U L N) {k : ℕ}
    {C : Fin (k + 1) → Subgroup G} (hC0 : C 0 = ⊥) (hCk : C (Fin.last k) = L)
    (hCn : ∀ i, H ≤ normalizer (C i : Set G))
    (hCs : ∀ i : Fin k, C i.castSucc < C i.succ ∧ ∀ X : Subgroup G, H ≤ normalizer (X : Set G) →
      C i.castSucc ≤ X → X ≤ C i.succ → X = C i.castSucc ∨ X = C i.succ) :
    ∃ C' : Fin (k + 2) → Subgroup G, C' 0 = ⊥ ∧ C' (Fin.last (k + 1)) = N ∧
      (∀ i, H ≤ normalizer (C' i : Set G)) ∧
      (∀ i : Fin (k + 1), C' i.castSucc < C' i.succ ∧ ∀ X : Subgroup G,
        H ≤ normalizer (X : Set G) → C' i.castSucc ≤ X → X ≤ C' i.succ →
          X = C' i.castSucc ∨ X = C' i.succ) ∧
      (∀ j : Fin k, C' j.castSucc.succ = C j.succ ∧ C' j.castSucc.castSucc = C j.castSucc) ∧
      C' (Fin.last k).succ = N ∧ C' (Fin.last k).castSucc = L := by
  set C' : Fin (k + 2) → Subgroup G := Fin.snoc C N with hC'
  have hcs : ∀ j : Fin (k + 1), C' j.castSucc = C j := fun j => by
    rw [hC', Fin.snoc_castSucc]
  have hl : C' (Fin.last (k + 1)) = N := by
    rw [hC', Fin.snoc_last]
  have hval : ∀ j : Fin k, C' j.castSucc.succ = C j.succ ∧ C' j.castSucc.castSucc = C j.castSucc :=
    fun j => ⟨by rw [Fin.succ_castSucc, hcs], hcs _⟩
  have hlast : C' (Fin.last k).succ = N ∧ C' (Fin.last k).castSucc = L :=
    ⟨by rw [Fin.succ_last]; exact hl, by rw [hcs, hCk]⟩
  refine ⟨C', ?_, hl, fun i => ?_, fun i => ?_, hval, hlast⟩
  · rw [← Fin.castSucc_zero, hcs, hC0]
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [hcs]
      exact hCn j
    · rw [hl]
      exact le_normalizer_of_isNormalIn_chief hstep.1
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [(hval j).1, (hval j).2]
      exact hCs j
    · rw [hlast.1, hlast.2]
      refine ⟨hstep.2.2.1, fun X hX hLX hXN => hstep.2.2.2 X ⟨hXN.trans hstep.1.1,
        fun g hg x hx => (mem_normalizer_iff.mp (hX hg) x).mp hx⟩ hLX hXN⟩

theorem exists_chain_of_isChiefSeriesFrom {H U N : Subgroup G} {n : ℕ}
    (h : IsChiefSeriesFrom H U N n) :
    ∃ (k : ℕ) (C : Fin (k + 1) → Subgroup G), C 0 = ⊥ ∧ C (Fin.last k) = N ∧
      (∀ i, H ≤ normalizer (C i : Set G)) ∧
      (∀ i : Fin k, C i.castSucc < C i.succ ∧ ∀ X : Subgroup G, H ≤ normalizer (X : Set G) →
        C i.castSucc ≤ X → X ≤ C i.succ → X = C i.castSucc ∨ X = C i.succ) ∧
      (n = 0 → ∀ i : Fin k, ⁅C i.succ, H⁆ ≤ C i.castSucc) ∧
      (n = 1 → ∃! i : Fin k, ¬ ⁅C i.succ, H⁆ ≤ C i.castSucc) := by
  induction h with
  | bot =>
    refine ⟨0, fun _ => ⊥, rfl, rfl, fun _ => ?_, fun i => i.elim0, fun _ i => i.elim0,
      fun h => absurd h zero_ne_one⟩
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  | @central N L n hstep hcent _ ih =>
    obtain ⟨k, C, hC0, hCk, hCn, hCs, h0, h1⟩ := ih
    obtain ⟨C', hC0', hCk', hCn', hCs', hold, hnew⟩ := chain_snoc hstep hC0 hCk hCn hCs
    have hc : ⁅N, H⁆ ≤ L := commutator_le_iff_isCentralStep.mpr hcent
    refine ⟨k + 1, C', hC0', hCk', hCn', hCs', fun hn i => ?_, fun hn => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [(hold j).1, (hold j).2]
        exact h0 hn j
      · rw [hnew.1, hnew.2]
        exact hc
    · obtain ⟨j₀, hj₀, hu⟩ := h1 hn
      refine ⟨j₀.castSucc, by beta_reduce; rw [(hold j₀).1, (hold j₀).2]; exact hj₀,
        fun i hi => ?_⟩
      beta_reduce at hi
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [(hold j).1, (hold j).2] at hi
        rw [hu j hi]
      · rw [hnew.1, hnew.2] at hi
        exact absurd hc hi
  | @noncentral N L n hstep hnc _ ih =>
    obtain ⟨k, C, hC0, hCk, hCn, hCs, h0, -⟩ := ih
    obtain ⟨C', hC0', hCk', hCn', hCs', hold, hnew⟩ := chain_snoc hstep hC0 hCk hCn hCs
    have hc : ¬ ⁅N, H⁆ ≤ L := fun h => hnc (commutator_le_iff_isCentralStep.mp h)
    refine ⟨k + 1, C', hC0', hCk', hCn', hCs', fun hn => absurd hn (Nat.succ_ne_zero n),
      fun hn => ?_⟩
    have hn0 : n = 0 := by omega
    refine ⟨Fin.last k, by beta_reduce; rw [hnew.1, hnew.2]; exact hc, fun i hi => ?_⟩
    beta_reduce at hi
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [(hold j).1, (hold j).2] at hi
      exact absurd (h0 hn0 j) hi
    · rfl

end CFSG.Quasithin.H13.NQCore
