module

public import CFSG.RankThree.PartOne.N1322.Core
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix

theorem exists_refl_pair {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d) :
    ∃ ρ t₀ : d.Lm, DihGens d.Lm d.n ρ t₀ ∧ (t₀ : GL (Fin 3) (ZMod p)) ∈ d.D ∧
      ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) ∈ d.D := by
  obtain ⟨e'⟩ := h.Ldih
  obtain ⟨ρ, t₀, hg⟩ := exists_gens h.n_mem e'
  have hcover := hcover_of_hyp (two_ne_zero_of_five_le h.p5) h.toMonoHyp
  exact ⟨ρ, t₀, hg, hcover t₀ ((hg.nc_iff t₀).mpr ⟨0, by simp⟩),
    hcover (t₀ * ρ) ((hg.nc_iff _).mpr ⟨1, by simp⟩)⟩

theorem lm_not_conj {K : Type*} [Field K] {d : CoreData K} {n : ℕ} {ρ t₀ : d.Lm}
    (hg : DihGens d.Lm n ρ t₀) (l : GL (Fin 3) K) (hl : l ∈ d.Lm) :
    l * (t₀ : GL (Fin 3) K) * l⁻¹ ≠ ((t₀ * ρ : d.Lm) : GL (Fin 3) K) := by
  intro heq
  apply hg.not_conj 0 1 ⟨0, by norm_num⟩ ⟨l, hl⟩
  apply Subtype.ext
  simpa using heq

theorem pair_not_X_conj {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (hkA : KAStmt d)
    (hn4 : d.n = 4) {ρ t₀ : d.Lm} (hg : DihGens d.Lm d.n ρ t₀)
    (ht₀ : (t₀ : GL (Fin 3) (ZMod p)) ∈ d.D)
    (hs₀ : ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) ∈ d.D) {k : GL (Fin 3) (ZMod p)}
    (hk : k ∈ d.X)
    (hns : ¬ ∃ μ : ZMod p, (k : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ d.c = μ • d.c) :
    k * (t₀ : GL (Fin 3) (ZMod p)) * k⁻¹ ≠ ((t₀ * ρ : d.Lm) : GL (Fin 3) (ZMod p)) :=
  hkA hn4 k hk hns _ ht₀ _ hs₀ t₀.2 (t₀ * ρ).2 (fun l hl => lm_not_conj hg l hl)

theorem mem_X_of_mem_D {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {t : GL (Fin 3) (ZMod p)} (ht : t ∈ d.D) : t ∈ d.X := by
  rw [h.gen]
  exact Subgroup.subset_closure ht

theorem four_ne_zero_of_five_le {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) : (4 : ZMod p) ≠ 0 := by
  have h2 := two_ne_zero_of_five_le (p := p) hp5
  have : (4 : ZMod p) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

end CFSG.RankThree.PartOne.N1322
