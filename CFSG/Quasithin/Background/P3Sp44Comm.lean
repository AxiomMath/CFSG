module

public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Open.StatedAPI

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic

theorem sp44_commutant_core {K : Type} [Field K] (f : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hup : ∀ (i : Fin 2) (s : K) (v : Fin 2 ⊕ Fin 2 → K),
      f (Pi.single (Sum.inl i) (s * v (Sum.inr i))) = Pi.single (Sum.inl i) (s * f v (Sum.inr i)))
    (hlow : ∀ (i : Fin 2) (s : K) (v : Fin 2 ⊕ Fin 2 → K),
      f (Pi.single (Sum.inr i) (s * v (Sum.inl i))) = Pi.single (Sum.inr i) (s * f v (Sum.inl i)))
    (hsw : ∀ (s : K) (v : Fin 2 ⊕ Fin 2 → K),
      f (Pi.single (Sum.inl 0) (s * v (Sum.inr 1)) + Pi.single (Sum.inl 1) (s * v (Sum.inr 0))) =
        Pi.single (Sum.inl 0) (s * f v (Sum.inr 1)) + Pi.single (Sum.inl 1) (s * f v (Sum.inr 0))) :
    ∃ p : K, ∀ v, f v = p • v := by
  set g : Fin 2 → K → K := fun i c => f (Pi.single (Sum.inl i) c) (Sum.inl i) with hg
  have hr : ∀ i w, f w (Sum.inr i) = g i (w (Sum.inr i)) := by
    intro i w
    have := congrArg (fun u : Fin 2 ⊕ Fin 2 → K => u (Sum.inl i)) (hup i 1 w)
    simpa [hg] using this.symm
  have hl : ∀ i w, f w (Sum.inl i) = f (Pi.single (Sum.inr i) (w (Sum.inl i))) (Sum.inr i) := by
    intro i w
    have := congrArg (fun u : Fin 2 ⊕ Fin 2 → K => u (Sum.inr i)) (hlow i 1 w)
    simpa using this.symm
  have hl' : ∀ i w, f w (Sum.inl i) = g i (w (Sum.inl i)) := by
    intro i w
    rw [hl, hr]
    simp
  have hmul : ∀ i s c, g i (s * c) = s * g i c := by
    intro i s c
    have := congrArg (fun u : Fin 2 ⊕ Fin 2 → K => u (Sum.inl i))
      (hup i s (Pi.single (Sum.inr i) c))
    simp only [Pi.single_eq_same] at this
    rw [hr i] at this
    simpa [hg] using this
  have hlin : ∀ i c, g i c = c * g i 1 := by
    intro i c
    have := hmul i c 1
    simpa using this
  have hsw' : g 0 1 = g 1 1 := by
    have h := congrArg (fun u : Fin 2 ⊕ Fin 2 → K => u (Sum.inl 0))
      (hsw 1 (Pi.single (Sum.inr 1) 1))
    simp only [hl' 0, hr 1] at h
    simpa using h
  refine ⟨g 0 1, fun v => ?_⟩
  ext a
  rcases a with i | i
  · rw [hl', hlin]
    fin_cases i
    · simp [mul_comm]
    · simp [mul_comm, hsw']
  · rw [hr, hlin]
    fin_cases i
    · simp [mul_comm]
    · simp [mul_comm, hsw']


variable {K : Type} [Field K]

theorem sp44_upper_mulVec (i : Fin 2) (s : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (fromBlocks 0 (Matrix.single i i s) 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      Pi.single (Sum.inl i) (s * v (Sum.inr i)) := by
  ext a
  rcases a with j | j
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem sp44_lower_mulVec (i : Fin 2) (s : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (fromBlocks 0 0 (Matrix.single i i s) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      Pi.single (Sum.inr i) (s * v (Sum.inl i)) := by
  ext a
  rcases a with j | j
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.single_apply]

theorem sp44_swap_mulVec (s : K) (v : Fin 2 ⊕ Fin 2 → K) :
    (fromBlocks 0 (Matrix.single 0 1 s + Matrix.single 1 0 s) 0 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      Pi.single (Sum.inl 0) (s * v (Sum.inr 1)) + Pi.single (Sum.inl 1) (s * v (Sum.inr 0)) := by
  ext a
  rcases a with j | j
  · fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]


theorem sp44_commutant (f : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hf : ∀ g ∈ StatedSp 2 K, ∀ v,
      f ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f v) :
    ∃ p : K, ∀ v, f v = p • v := by
  have hU : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S → ∀ v,
      f ((fromBlocks 0 S 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (fromBlocks 0 S 0 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f v := by
    intro S hS v
    have hmem : (upperUnipotent (n := 2) hS : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := by
      rw [statedSp_eq_GLSymplectic]
      exact (upperUnipotent (n := 2) hS).2
    have h := hf _ hmem v
    have hcoe : ((upperUnipotent (n := 2) hS : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 + fromBlocks 0 S 0 0 := by
      rw [coe_upperUnipotent, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
      simp
    rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, map_add, Matrix.add_mulVec,
      Matrix.one_mulVec] at h
    exact add_left_cancel h
  have hL : ∀ S : Matrix (Fin 2) (Fin 2) K, Sᵀ = S → ∀ v,
      f ((fromBlocks 0 0 S 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (fromBlocks 0 0 S 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f v := by
    intro S hS v
    have hmem : (lowerUnipotent (n := 2) hS : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := by
      rw [statedSp_eq_GLSymplectic]
      exact (lowerUnipotent (n := 2) hS).2
    have h := hf _ hmem v
    have hcoe : ((lowerUnipotent (n := 2) hS : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 + fromBlocks 0 0 S 0 := by
      rw [coe_lowerUnipotent, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
      simp
    rw [hcoe, Matrix.add_mulVec, Matrix.one_mulVec, map_add, Matrix.add_mulVec,
      Matrix.one_mulVec] at h
    exact add_left_cancel h
  have hsymm : ∀ (i : Fin 2) (s : K), (Matrix.single i i s)ᵀ = Matrix.single i i s := by
    intro i s
    simp [Matrix.transpose_single]
  refine sp44_commutant_core f ?_ ?_ ?_
  · intro i s v
    rw [← sp44_upper_mulVec, ← sp44_upper_mulVec]
    exact hU _ (hsymm i s) v
  · intro i s v
    rw [← sp44_lower_mulVec, ← sp44_lower_mulVec]
    exact hL _ (hsymm i s) v
  · intro s v
    rw [← sp44_swap_mulVec, ← sp44_swap_mulVec]
    refine hU _ ?_ v
    rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single, add_comm]


theorem sp44_commutant_matrix (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hX : ∀ g ∈ StatedSp 2 K,
      X * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (g : Matrix _ _ K) * X) :
    ∃ d : K, X = Matrix.scalar (Fin 2 ⊕ Fin 2) d := by
  refine eq_scalar_of_commute_unipotents X (fun B hB => ?_) (fun C hC => ?_)
  · have hmem : (upperUnipotent (n := 2) hB : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := by
      rw [statedSp_eq_GLSymplectic]
      exact (upperUnipotent (n := 2) hB).2
    simpa using hX _ hmem
  · have hmem : (lowerUnipotent (n := 2) hC : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedSp 2 K := by
      rw [statedSp_eq_GLSymplectic]
      exact (lowerUnipotent (n := 2) hC).2
    simpa using hX _ hmem

@[expose, reducible] def sp44J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 (-1) 0

theorem sp44J_mul_self : (sp44J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * sp44J = -1 := by
  simp [sp44J, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]

theorem sp44J_transpose : (sp44J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ = -sp44J := by
  simp [sp44J, fromBlocks_transpose, fromBlocks_neg]

theorem sp44_mem_iff (g : GL (Fin 2 ⊕ Fin 2) K) :
    g ∈ StatedSp 2 K ↔
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * sp44J *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp44J :=
  CFSG.Open.StatedAPI.mem_statedSp_iff


theorem sp44_gram_scalar (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hN : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * N *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = N) :
    ∃ μ : K, N = μ • (sp44J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  have hX : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      (sp44J * N) * (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (sp44J * N) := by
    intro g hg
    set gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hgm
    set gi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
      ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hgi
    have hggi : gm * gi = 1 := by simp [hgm, hgi]
    have hJ : gmᵀ * sp44J * gm = sp44J := (sp44_mem_iff g).1 hg
    have h1 : N * gm = giᵀ * N := by
      calc N * gm = (giᵀ * gmᵀ) * N * gm := by
            rw [← transpose_mul, hggi, transpose_one, Matrix.one_mul]
        _ = giᵀ * (gmᵀ * N * gm) := by simp only [Matrix.mul_assoc]
        _ = giᵀ * N := by rw [hN g hg]
    have h2 : sp44J * gm = giᵀ * sp44J := by
      calc sp44J * gm = (giᵀ * gmᵀ) * sp44J * gm := by
            rw [← transpose_mul, hggi, transpose_one, Matrix.one_mul]
        _ = giᵀ * (gmᵀ * sp44J * gm) := by simp only [Matrix.mul_assoc]
        _ = giᵀ * sp44J := by rw [hJ]
    have h3 : sp44J * giᵀ = gm * sp44J := by
      calc sp44J * giᵀ = - (sp44J * giᵀ * (sp44J * sp44J)) := by
            rw [sp44J_mul_self]; simp
        _ = -(sp44J * (giᵀ * sp44J) * sp44J) := by simp only [Matrix.mul_assoc]
        _ = -(sp44J * (sp44J * gm) * sp44J) := by rw [h2]
        _ = -((sp44J * sp44J) * gm * sp44J) := by simp only [Matrix.mul_assoc]
        _ = gm * sp44J := by rw [sp44J_mul_self]; simp
    calc sp44J * N * gm = sp44J * (N * gm) := by rw [Matrix.mul_assoc]
      _ = sp44J * (giᵀ * N) := by rw [h1]
      _ = (sp44J * giᵀ) * N := by rw [Matrix.mul_assoc]
      _ = (gm * sp44J) * N := by rw [h3]
      _ = gm * (sp44J * N) := by rw [Matrix.mul_assoc]
  obtain ⟨d, hd⟩ := sp44_commutant_matrix _ hX
  refine ⟨-d, ?_⟩
  have h : sp44J * (sp44J * N) = d • sp44J := by
    rw [hd, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, sp44J_mul_self] at h
  have h' : N = (-d) • sp44J := by
    have := congrArg (fun M => -M) h
    simpa using this
  exact h'


@[expose] def sp44ω (v w : Fin 2 ⊕ Fin 2 → K) : K := v ⬝ᵥ (sp44J *ᵥ w)

theorem sp44ω_add_left (v v' w : Fin 2 ⊕ Fin 2 → K) :
    sp44ω (v + v') w = sp44ω v w + sp44ω v' w := by
  simp [sp44ω, add_dotProduct]

theorem sp44ω_smul_left (t : K) (v w : Fin 2 ⊕ Fin 2 → K) :
    sp44ω (t • v) w = t * sp44ω v w := by
  simp [sp44ω, smul_dotProduct]

theorem sp44ω_add_right (v w w' : Fin 2 ⊕ Fin 2 → K) :
    sp44ω v (w + w') = sp44ω v w + sp44ω v w' := by
  simp [sp44ω, Matrix.mulVec_add, dotProduct_add]

theorem sp44ω_smul_right (t : K) (v w : Fin 2 ⊕ Fin 2 → K) :
    sp44ω v (t • w) = t * sp44ω v w := by
  simp [sp44ω, Matrix.mulVec_smul, dotProduct_smul]

theorem sp44ω_mulVec (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hg : gᵀ * sp44J * g = sp44J) (v w : Fin 2 ⊕ Fin 2 → K) :
    sp44ω (g *ᵥ v) (g *ᵥ w) = sp44ω v w := by
  have h1 : ∀ (u x : Fin 2 ⊕ Fin 2 → K), (g *ᵥ u) ⬝ᵥ x = u ⬝ᵥ (gᵀ *ᵥ x) := by
    intro u x
    rw [← Matrix.vecMul_transpose g u, Matrix.dotProduct_mulVec]
  simp only [sp44ω]
  rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]



theorem sp44_bilin_gram (β : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K) → K)
    (h1 : ∀ v v' w, β (v + v') w = β v w + β v' w) (h2 : ∀ (t : K) v w, β (t • v) w = t * β v w)
    (h3 : ∀ v w w', β v (w + w') = β v w + β v w') (h4 : ∀ (t : K) v w, β v (t • w) = t * β v w) :
    ∃ G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, ∀ v w, β v w = v ⬝ᵥ (G *ᵥ w) := by
  let B : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K) := LinearMap.mk₂ K β h1 h2 h3 h4
  refine ⟨LinearMap.BilinForm.toMatrix' B, fun v w => ?_⟩
  have e : Matrix.toBilin' (LinearMap.BilinForm.toMatrix' B) = B := by
    simp
  have := congrArg (fun F : LinearMap.BilinForm K (Fin 2 ⊕ Fin 2 → K) => F v w) e
  simp only [Matrix.toBilin'_apply'] at this
  exact this.symm

theorem sp44_form_mul (β : (Fin 2 ⊕ Fin 2 → K) → (Fin 2 ⊕ Fin 2 → K) → K)
    (h1 : ∀ v v' w, β (v + v') w = β v w + β v' w) (h2 : ∀ (t : K) v w, β (t • v) w = t * β v w)
    (h3 : ∀ v w w', β v (w + w') = β v w + β v w') (h4 : ∀ (t : K) v w, β v (t • w) = t * β v w)
    (hinv : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K → ∀ v w,
      β ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)
        ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) = β v w) :
    ∃ μ : K, ∀ v w, β v w = μ * sp44ω v w := by
  obtain ⟨G, hG⟩ := sp44_bilin_gram β h1 h2 h3 h4
  have hmat : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * G *
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = G := by
    intro g hg
    have key : ∀ v w : Fin 2 ⊕ Fin 2 → K,
        v ⬝ᵥ (((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * G *
          (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *ᵥ w) = v ⬝ᵥ (G *ᵥ w) := by
      intro v w
      have h := hinv g hg v w
      rw [hG, hG] at h
      have e : ∀ (u x : Fin 2 ⊕ Fin 2 → K),
          ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) ⬝ᵥ x =
            u ⬝ᵥ ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *ᵥ x) := by
        intro u x
        rw [← Matrix.vecMul_transpose (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) u,
          Matrix.dotProduct_mulVec]
      rw [e, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h
      exact h
    ext i j
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  obtain ⟨μ, hμ⟩ := sp44_gram_scalar G hmat
  refine ⟨μ, fun v w => ?_⟩
  rw [hG, hμ]
  simp [sp44ω, Matrix.smul_mulVec, dotProduct_smul]

end G118

end G11

end CFSG.Quasithin
