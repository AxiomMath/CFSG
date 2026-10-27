module

public import CFSG.RankThree.GF2n.Smith81.OrthModel

public section

namespace CFSG.RankThree.GF2n.Smith81

section PairTypesTensor

variable {K : Type} [Field K] [CharP K 2] {ι : Type}

private theorem tsim_det {g : Matrix (Fin 2) (Fin 2) K} (hg : g.det ≠ 0) :
    g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
  rwa [Matrix.det_fin_two] at hg

private theorem tsim_two_by_two {a b c d x y : K} (hD : a * d - b * c ≠ 0)
    (h1 : a * x + b * y = 0) (h2 : c * x + d * y = 0) : x = 0 ∧ y = 0 := by
  have hx : x * (a * d - b * c) = 0 := by linear_combination d * h1 - b * h2
  have hy : y * (a * d - b * c) = 0 := by linear_combination a * h2 - c * h1
  exact ⟨(mul_eq_zero.mp hx).resolve_right hD, (mul_eq_zero.mp hy).resolve_right hD⟩

private theorem tsim_comb_ne (σ : K ≃+* K) (g : Matrix (Fin 2) (Fin 2) K) (hg : g.det ≠ 0)
    {c₁ c₂ : K} (hc : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    g 0 0 * σ c₁ + g 0 1 * σ c₂ ≠ 0 ∨ g 1 0 * σ c₁ + g 1 1 * σ c₂ ≠ 0 := by
  by_contra hcon
  simp only [not_or, ne_eq, not_not] at hcon
  obtain ⟨hs1, hs2⟩ := tsim_two_by_two (tsim_det hg) hcon.1 hcon.2
  have hc1 : c₁ = 0 := σ.injective (hs1.trans (map_zero σ).symm)
  have hc2 : c₂ = 0 := σ.injective (hs2.trans (map_zero σ).symm)
  rcases hc with h | h
  · exact h hc1
  · exact h hc2

private theorem tsim_smul_pair (σ : K ≃+* K) (g : Matrix (Fin 2) (Fin 2) K)
    (o : (ι → K) → (ι → K)) (ho_smul : ∀ (c : K) u, o (c • u) = σ c • o u)
    (c₁ c₂ : K) (u : ι → K) :
    orthTensor g o (c₁ • u, c₂ • u) =
      ((g 0 0 * σ c₁ + g 0 1 * σ c₂) • o u, (g 1 0 * σ c₁ + g 1 1 * σ c₂) • o u) := by
  simp only [orthTensor, ho_smul, smul_smul, ← add_smul]

private theorem tsim_o_zero (σ : K ≃+* K) (o : (ι → K) → (ι → K))
    (ho_bij : Function.Bijective o) (ho_smul : ∀ (c : K) u, o (c • u) = σ c • o u)
    (w : ι → K) (hw : o w = 0) : w = 0 := by
  have h0 : o 0 = 0 := by simpa using ho_smul 0 0
  exact ho_bij.1 (hw.trans h0.symm)

theorem pairTypeA_orthTensor (q : QuadraticForm K (ι → K)) (σ : K ≃+* K)
    (g : Matrix (Fin 2) (Fin 2) K) (hg : g.det ≠ 0) (o : (ι → K) → (ι → K))
    (ho_bij : Function.Bijective o) (ho_add : ∀ u v, o (u + v) = o u + o v)
    (ho_smul : ∀ (c : K) u, o (c • u) = σ c • o u) (ρ : K) (hρ : ρ ≠ 0)
    (ho_q : ∀ u, q (o u) = ρ * σ (q u)) {p : (ι → K) × (ι → K)} (h : PairTypeA q p) :
    PairTypeA q (orthTensor g o p) := by
  obtain ⟨c₁, c₂, u, hc, hu, hqu, rfl⟩ := h
  refine ⟨g 0 0 * σ c₁ + g 0 1 * σ c₂, g 1 0 * σ c₁ + g 1 1 * σ c₂, o u,
    tsim_comb_ne σ g hg hc, fun h0 => hu (tsim_o_zero σ o ho_bij ho_smul u h0), ?_,
    tsim_smul_pair σ g o ho_smul c₁ c₂ u⟩
  rw [ho_q, hqu, map_zero, mul_zero]

end PairTypesTensor

end CFSG.RankThree.GF2n.Smith81
