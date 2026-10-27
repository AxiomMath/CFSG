module

public import CFSG.RankThree.GF2n.Smith81.S81A5Basic
public import CFSG.RankThree.GF2n.Smith81.S81RDot

open Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type} [Field K]

private theorem linearIndependent_four_of_dot_eq_one {f a p q c : Fin 6 → K}
    (hs : LinearIndependent K ![a, p, q]) (hfa : f ⬝ᵥ a = 0) (hfp : f ⬝ᵥ p = 0)
    (hfq : f ⬝ᵥ q = 0) (hc : f ⬝ᵥ c = 1) :
    LinearIndependent K ![a, p, q, c] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : g 0 • a + g 1 • p + g 2 • q + g 3 • c = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have h3 : g 3 = 0 := by
    have h : f ⬝ᵥ (g 0 • a + g 1 • p + g 2 • q + g 3 • c) = 0 := by
      rw [key, dotProduct_zero]
    simpa [dotProduct_add, dotProduct_smul, hfa, hfp, hfq, hc] using h
  have key3 : g 0 • a + g 1 • p + g 2 • q = 0 := by
    rw [h3, zero_smul, add_zero] at key
    exact key
  have hs' := Fintype.linearIndependent_iff.mp hs ![g 0, g 1, g 2] (by
    simpa [Fin.sum_univ_three] using key3)
  have h0 : g 0 = 0 := by simpa using hs' 0
  have h1 : g 1 = 0 := by simpa using hs' 1
  have h2 : g 2 = 0 := by simpa using hs' 2
  intro i
  fin_cases i <;> simp [h0, h1, h2, h3]

theorem exists_sl_fix_axis_map {f a u₁ v₁ u v : Fin 6 → K} (hf : f ≠ 0)
    (hs : LinearIndependent K ![a, u₁, v₁]) (ht : LinearIndependent K ![a, u, v])
    (hfa : f ⬝ᵥ a = 0) (hfu₁ : f ⬝ᵥ u₁ = 0) (hfv₁ : f ⬝ᵥ v₁ = 0)
    (hfu : f ⬝ᵥ u = 0) (hfv : f ⬝ᵥ v = 0) :
    ∃ G : Matrix (Fin 6) (Fin 6) K, G.det = 1 ∧ G.mulVec a = a ∧ G.mulVec u₁ = u ∧
      G.mulVec v₁ = v ∧ ∀ x, f ⬝ᵥ G.mulVec x = f ⬝ᵥ x := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 6 → K, f ⬝ᵥ c = 1 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
    have hj' : f j ≠ 0 := hj
    exact ⟨(f j)⁻¹ • (Pi.single j 1 : Fin 6 → K), by
      rw [dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, inv_mul_cancel₀ hj']⟩
  obtain ⟨g, hgdet, hg⟩ := exists_sl_of_linearIndependent (by norm_num : 4 < 6)
    (linearIndependent_four_of_dot_eq_one hs hfa hfu₁ hfv₁ hc)
    (linearIndependent_four_of_dot_eq_one ht hfa hfu hfv hc)
  have e0 : g *ᵥ a = a := by simpa using hg 0
  have e1 : g *ᵥ u₁ = u := by simpa using hg 1
  have e2 : g *ᵥ v₁ = v := by simpa using hg 2
  have e3 : g *ᵥ c = c := by simpa using hg 3
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin 6 → K, ∀ x, δ ⬝ᵥ x = f ⬝ᵥ g *ᵥ x - f ⬝ᵥ x :=
    ⟨f ᵥ* g - f, fun x => by rw [sub_dotProduct, dotProduct_mulVec]⟩
  have hδa : δ ⬝ᵥ a = 0 := by rw [hδ, e0, sub_self]
  have hδu₁ : δ ⬝ᵥ u₁ = 0 := by rw [hδ, e1, hfu, hfu₁, sub_zero]
  have hδv₁ : δ ⬝ᵥ v₁ = 0 := by rw [hδ, e2, hfv, hfv₁, sub_zero]
  have hδc : δ ⬝ᵥ c = 0 := by rw [hδ, e3, hc, sub_self]
  have ht_mulVec : ∀ x, (1 + vecMulVec (-c) δ).mulVec x = x - (δ ⬝ᵥ x) • c := by
    intro x
    rw [one_add_vecMulVec_mulVec, smul_neg, sub_eq_add_neg]
  have ht_det : (1 + vecMulVec (-c) δ).det = 1 := by
    rw [det_one_add_vecMulVec, dotProduct_neg, hδc, neg_zero, add_zero]
  refine ⟨g * (1 + vecMulVec (-c) δ), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, hgdet, ht_det, one_mul]
  · rw [← Matrix.mulVec_mulVec, ht_mulVec, hδa, zero_smul, sub_zero, e0]
  · rw [← Matrix.mulVec_mulVec, ht_mulVec, hδu₁, zero_smul, sub_zero, e1]
  · rw [← Matrix.mulVec_mulVec, ht_mulVec, hδv₁, zero_smul, sub_zero, e2]
  · intro x
    rw [← Matrix.mulVec_mulVec, ht_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, e3,
      dotProduct_sub, dotProduct_smul, hc, hδ x, smul_eq_mul, mul_one]
    ring

end CFSG.RankThree.GF2n.Smith81.A5Cube
