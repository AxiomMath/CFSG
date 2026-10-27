module

public import CFSG.RankThree.GF2n.Smith81.S81RRangeIndep
public import CFSG.RankThree.GF2n.Smith81.S81RRangeCentre
public import CFSG.RankThree.GF2n.Smith81.S81RFrameCentre

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix

variable {K : Type*} [Field K]

private theorem exists_smul_of_not_li {a b : Fin 6 → K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ¬ LinearIndependent K ![a, b]) : ∃ l : K, l ≠ 0 ∧ b = l • a := by
  rw [LinearIndependent.pair_iff] at h
  simp only [not_forall] at h
  obtain ⟨s, t, hst, hne⟩ := h
  have ht : t ≠ 0 := by
    intro ht
    rw [ht, zero_smul, add_zero] at hst
    have hs : s = 0 := (smul_eq_zero.mp hst).resolve_right ha
    exact hne ⟨hs, ht⟩
  have h1 : t • b = -(s • a) := eq_neg_of_add_eq_zero_right hst
  have h2 : b = (-(t⁻¹ * s)) • a := by
    calc b = t⁻¹ • (t • b) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = t⁻¹ • (-(s • a)) := by rw [h1]
      _ = (-(t⁻¹ * s)) • a := by rw [smul_neg, smul_smul, neg_smul]
  refine ⟨-(t⁻¹ * s), ?_, h2⟩
  intro h0
  rw [h0, zero_smul] at h2
  exact hb h2

theorem pure_of_range_inf_range [CharP K 2] {x y : GL (Fin 6) K} (hx : IsTransvec K x)
    (hy : IsTransvec K y)
    (hnot : ¬ ∃ s : K, (y : Matrix (Fin 6) (Fin 6) K) - 1 = s • ((x : Matrix (Fin 6) (Fin 6) K) - 1)) :
    ∀ ξ ∈ LinearMap.range (rho K x - 1) ⊓ LinearMap.range (rho K y - 1), IsPure K ξ := by
  obtain ⟨a, f, ha, hf, hfa, hxa⟩ := IsTransvec.exists hx
  obtain ⟨b, g, hb, hg, hgb, hyb⟩ := IsTransvec.exists hy
  by_cases hab : LinearIndependent K ![a, b]
  · exact pure_of_range_inf_range_indep hxa hyb hab
  · obtain ⟨l, hl0, hbl⟩ := exists_smul_of_not_li ha hb hab
    have hyb' : (y : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a (l • g) := by
      rw [hyb, hbl, smul_vecMulVec, vecMulVec_smul]
    have hga : (l • g) ⬝ᵥ a = 0 := by
      have h1 : g ⬝ᵥ b = l * (g ⬝ᵥ a) := by rw [hbl, dotProduct_smul, smul_eq_mul]
      rw [smul_dotProduct, smul_eq_mul, ← h1, hgb]
    have hlg : l • g ≠ 0 := fun h => hg ((smul_eq_zero.mp h).resolve_left hl0)
    by_cases hfg : LinearIndependent K ![f, l • g]
    · obtain ⟨c, α, β, hdet, -, -, h1, h2, h3⟩ := exists_frame_centre ha hfa hga hfg
      exact pure_of_range_inf_range_centre hxa hyb' ⟨c, α, β, hdet, h1, h2, h3⟩
    · obtain ⟨μ, hμ0, hμ⟩ := exists_smul_of_not_li hf hlg hfg
      exfalso
      apply hnot
      refine ⟨μ, ?_⟩
      rw [hyb', hxa, add_sub_cancel_left, add_sub_cancel_left, hμ, vecMulVec_smul]

end CFSG.RankThree.GF2n.Smith81.A5Cube
