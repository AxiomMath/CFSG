module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.ClassicalPosition.Geo

private lemma gDP_conj_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G B A : Matrix ι ι F) (hGG : G * G⁻¹ = 1) :
    G⁻¹ * (B * A) * G = (G⁻¹ * B * G) * (G⁻¹ * A * G) := by
  rw [Matrix.mul_assoc (G⁻¹ * B) G ((G⁻¹ * A) * G),
      ← Matrix.mul_assoc G (G⁻¹ * A) G, ← Matrix.mul_assoc G G⁻¹ A,
      hGG, Matrix.one_mul, ← Matrix.mul_assoc (G⁻¹ * B) A G, ← Matrix.mul_assoc G⁻¹ B A]

private lemma gDP_conj_self {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G a N : Matrix ι ι F) (hGG : G⁻¹ * G = 1) (hN : N * G = 1) :
    G⁻¹ * (G * (a * N)) * G = a := by
  rw [← Matrix.mul_assoc G a N, ← Matrix.mul_assoc G⁻¹ (G * a) N,
      ← Matrix.mul_assoc G⁻¹ G a, hGG, Matrix.one_mul, Matrix.mul_assoc a N G, hN,
      Matrix.mul_one]

theorem formAdj_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G a b : Matrix ι ι F) : formAdj σ G (a + b) = formAdj σ G a + formAdj σ G b := by
  unfold formAdj
  rw [Matrix.map_add σ (map_add σ), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem formAdj_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (G : Matrix ι ι F) (c : F) (a : Matrix ι ι F) :
    formAdj σ G (c • a) = σ c • formAdj σ G a := by
  unfold formAdj
  rw [Matrix.map_smul' σ c a (map_mul σ), Matrix.transpose_smul, Matrix.mul_smul,
      Matrix.smul_mul]

theorem formAdj_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    {G : Matrix ι ι F} (hG : IsUnit G.det) (a b : Matrix ι ι F) :
    formAdj σ G (a * b) = formAdj σ G b * formAdj σ G a := by
  unfold formAdj
  rw [Matrix.map_mul, Matrix.transpose_mul]
  exact gDP_conj_mul G (Matrix.transpose (b.map σ)) (Matrix.transpose (a.map σ))
    (Matrix.mul_nonsing_inv G hG)

theorem formAdj_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    {G : Matrix ι ι F} (hG : IsUnit G.det) : formAdj σ G (1 : Matrix ι ι F) = 1 := by
  unfold formAdj
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.mul_one,
      Matrix.nonsing_inv_mul G hG]

theorem formAdj_formAdj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (σ : F →+* F)
    (hσ : ∀ x, σ (σ x) = x) {G : Matrix ι ι F} (hG : IsUnit G.det)
    (hGh : Matrix.transpose (G.map σ) = G) (a : Matrix ι ι F) :
    formAdj σ G (formAdj σ G a) = a := by
  have hGG' : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
  have hA : (a.map σ).map σ = a := by
    rw [Matrix.map_map]
    have hcomp : σ ∘ σ = id := by
      funext x
      exact hσ x
    rw [hcomp, Matrix.map_id]
  have hN : Matrix.transpose ((G⁻¹).map σ) * G = 1 := by
    calc Matrix.transpose ((G⁻¹).map σ) * G
        = Matrix.transpose ((G⁻¹).map σ) * Matrix.transpose (G.map σ) := by rw [hGh]
      _ = Matrix.transpose (G.map σ * (G⁻¹).map σ) := by rw [← Matrix.transpose_mul]
      _ = Matrix.transpose ((G * G⁻¹).map σ) := by rw [← Matrix.map_mul]
      _ = Matrix.transpose ((1 : Matrix ι ι F).map σ) := by
            rw [Matrix.mul_nonsing_inv G hG]
      _ = 1 := by rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
  unfold formAdj
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hA, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hGh]
  exact gDP_conj_self G a (Matrix.transpose ((G⁻¹).map σ)) hGG' hN

theorem formAdj_eq_inv_of_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) (s : GL ι F)
    (hs : Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G) :
    formAdj σ G (s : Matrix ι ι F) = ((s⁻¹ : GL ι F) : Matrix ι ι F) := by
  have hss : (s : Matrix ι ι F) * ((s⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : Matrix.transpose ((s : Matrix ι ι F).map σ) * G =
      G * ((s⁻¹ : GL ι F) : Matrix ι ι F) := by
    calc Matrix.transpose ((s : Matrix ι ι F).map σ) * G
        = Matrix.transpose ((s : Matrix ι ι F).map σ) * G * 1 := (Matrix.mul_one _).symm
      _ = Matrix.transpose ((s : Matrix ι ι F).map σ) * G * ((s : Matrix ι ι F) *
            ((s⁻¹ : GL ι F) : Matrix ι ι F)) := by rw [hss]
      _ = (Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F)) *
            ((s⁻¹ : GL ι F) : Matrix ι ι F) := by rw [← Matrix.mul_assoc]
      _ = G * ((s⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hs]
  unfold formAdj
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]

private lemma gDP_inv_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    {S : Set (GL ι F)} (s : GL ι F) (hs : s ∈ S) :
    ((s⁻¹ : GL ι F) : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) := by
  have hsA : (s : Matrix ι ι F) ∈ Algebra.adjoin F (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hs, rfl⟩
  have hfin : 0 < orderOf s := orderOf_pos s
  have hpow : s ^ (orderOf s - 1) = s⁻¹ := by
    have h1 : s ^ (orderOf s - 1) * s = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hfin, pow_orderOf_eq_one]
    exact eq_inv_of_mul_eq_one_left h1
  rw [← hpow, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ hsA _

theorem formAdj_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {S : Set (GL ι F)}
    (hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι F).map σ) * G * (s : Matrix ι ι F) = G)
    {a : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S)) :
    formAdj σ G a ∈ Algebra.adjoin F (Units.val '' S) := by
  refine Algebra.adjoin_induction
    (p := fun x _ => formAdj σ G x ∈ Algebra.adjoin F (Units.val '' S)) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    rw [formAdj_eq_inv_of_isometry σ hG s (hSU s hs)]
    exact gDP_inv_mem_adjoin s hs
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, formAdj_smul, formAdj_one σ hG,
        ← Algebra.algebraMap_eq_smul_one]
    exact Subalgebra.algebraMap_mem _ (σ r)
  · intro x y hx hy hpx hpy
    rw [formAdj_add]
    exact Subalgebra.add_mem _ hpx hpy
  · intro x y hx hy hpx hpy
    rw [formAdj_mul σ hG]
    exact Subalgebra.mul_mem _ hpy hpx

end CFSG.StandardType.ClassicalPosition.Geo
