module

public import CFSG.RankThree.GF2n.Smith81.S81RD8Span
public import CFSG.RankThree.GF2n.Smith81.S81RD8Adapt
public import CFSG.RankThree.GF2n.Smith81.S81RD8Map

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type} [Field K]

theorem exists_comm_move {x y : GL (Fin 6) K} {a f b g : Fin 6 → K}
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f)
    (hy : (y : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec b g)
    (hfa : f ⬝ᵥ a = 0) (hga : g ⬝ᵥ a = 0) (ha : a ≠ 0) (hf : f ≠ 0)
    {s : Fin 3 → Fin 6 → K} (hs : LinearIndependent K s) (hsf : ∀ i, f ⬝ᵥ s i = 0)
    (has : a ∈ Submodule.span K (Set.range s)) :
    ∃ G : GL (Fin 6) K, (G : Matrix (Fin 6) (Fin 6) K).det = 1 ∧ G * x = x * G ∧
      ∀ i, ((y : Matrix (Fin 6) (Fin 6) K) - 1).mulVec
        ((G : Matrix (Fin 6) (Fin 6) K).mulVec (s i)) = 0 := by
  obtain ⟨u₁, v₁, hli₁, hu₁s, hv₁s, hspan⟩ := exists_adapted_triple hs has ha
  obtain ⟨u, v, hli₂, hfu, hfv, hgu, hgv⟩ :=
    exists_pair_in_kernels (a := a) (f := f) (g := g) ha
  have hfu₁ : f ⬝ᵥ u₁ = 0 := dot_eq_zero_of_mem_span hsf hu₁s
  have hfv₁ : f ⬝ᵥ v₁ = 0 := dot_eq_zero_of_mem_span hsf hv₁s
  obtain ⟨Gm, hdet, hGa, hGu, hGv, hGf⟩ :=
    exists_sl_fix_axis_map hf hli₁ hli₂ hfa hfu₁ hfv₁ hfu hfv
  have hdet0 : Gm.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Gm hdet0, hdet, ?_, ?_⟩
  ·
    apply Units.ext
    show Gm * (x : Matrix (Fin 6) (Fin 6) K) = (x : Matrix (Fin 6) (Fin 6) K) * Gm
    have hf' : f ᵥ* Gm = f := by
      ext j
      have h := hGf (Pi.single j 1)
      rw [Matrix.dotProduct_mulVec] at h
      simpa [dotProduct_single] using h
    rw [hx, mul_add, add_mul, mul_one, one_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hGa,
      hf']
  · intro i
    have hz := mulVec_mem_span_of_images (hspan i) hGa hGu hGv
    have hg0 : g ⬝ᵥ Gm.mulVec (s i) = 0 := by
      refine dot_eq_zero_of_mem_span (s := ![a, u, v]) ?_ hz
      intro j
      fin_cases j
      · exact hga
      · exact hgu
      · exact hgv
    show ((y : Matrix (Fin 6) (Fin 6) K) - 1).mulVec (Gm.mulVec (s i)) = 0
    rw [hy, Matrix.sub_mulVec, one_add_vecMulVec_mulVec, Matrix.one_mulVec, add_sub_cancel_left,
      hg0, zero_smul]

end CFSG.RankThree.GF2n.Smith81.A5Cube
