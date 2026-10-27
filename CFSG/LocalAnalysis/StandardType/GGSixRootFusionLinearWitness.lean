module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinear

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Witness

open Matrix

variable {F : Type*} [Field F] {n : ℕ}

theorem diagonal_mul_ggInvMatrix_comm {l : ℕ} (d : Fin n → F)
    (hd : ∀ a b : Fin n, (b : ℕ) < l → (a : ℕ) = b + (n - l) → d a = d b) :
    Matrix.diagonal d * ggInvMatrix n l F = ggInvMatrix n l F * Matrix.diagonal d := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [ggInvMatrix, Matrix.add_apply, Matrix.one_apply, ggInvNil_apply]
  by_cases hab : a = b
  · subst hab
    ring
  · rw [ite_eq_right hab, zero_add]
    split_ifs with h
    · rw [mul_one, one_mul, hd a b h.1 h.2.1]
    · rw [mul_zero, zero_mul]

theorem ggWitnessMid_comm {l : ℕ} (h : 2 * l < n) (c : F) :
    Matrix.diagonal (Pi.mulSingle (⟨l, by omega⟩ : Fin n) c) * ggInvMatrix n l F =
      ggInvMatrix n l F * Matrix.diagonal (Pi.mulSingle (⟨l, by omega⟩ : Fin n) c) := by
  refine diagonal_mul_ggInvMatrix_comm _ fun a b hb ha => ?_
  have ha' : a ≠ ⟨l, by omega⟩ := fun h' => by
    have := congrArg Fin.val h'
    simp only at this
    omega
  have hb' : b ≠ ⟨l, by omega⟩ := fun h' => by
    have := congrArg Fin.val h'
    simp only at this
    omega
  rw [Pi.mulSingle_eq_of_ne ha', Pi.mulSingle_eq_of_ne hb']

theorem ggWitnessPair_comm {l : ℕ} (hl : 1 ≤ l) (h : n = 2 * l) (c : F) :
    Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) c *
        Pi.mulSingle (⟨l, by omega⟩ : Fin n) c) * ggInvMatrix n l F =
      ggInvMatrix n l F * Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) c *
        Pi.mulSingle (⟨l, by omega⟩ : Fin n) c) := by
  refine diagonal_mul_ggInvMatrix_comm _ fun a b hb ha => ?_
  simp only [Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem ggWitnessVariant_comm {l : ℕ} (hl : 1 ≤ l) (h : 2 * l < n) (c e : F) :
    Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) c *
        Pi.mulSingle (⟨n - l, by omega⟩ : Fin n) c * Pi.mulSingle (⟨l, by omega⟩ : Fin n) e) *
        ggInvMatrix n l F =
      ggInvMatrix n l F * Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) c *
        Pi.mulSingle (⟨n - l, by omega⟩ : Fin n) c * Pi.mulSingle (⟨l, by omega⟩ : Fin n) e) := by
  refine diagonal_mul_ggInvMatrix_comm _ fun a b hb ha => ?_
  simp only [Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

theorem ggWitnessVariantPair_comm {l : ℕ} (hl : 2 ≤ l) (h : n = 2 * l) (c e : F) :
    Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) c *
        Pi.mulSingle (⟨l, by omega⟩ : Fin n) c * Pi.mulSingle (⟨1, by omega⟩ : Fin n) e *
        Pi.mulSingle (⟨l + 1, by omega⟩ : Fin n) e) * ggInvMatrix n l F =
      ggInvMatrix n l F * Matrix.diagonal (Pi.mulSingle (⟨0, by omega⟩ : Fin n) c *
        Pi.mulSingle (⟨l, by omega⟩ : Fin n) c * Pi.mulSingle (⟨1, by omega⟩ : Fin n) e *
        Pi.mulSingle (⟨l + 1, by omega⟩ : Fin n) e) := by
  refine diagonal_mul_ggInvMatrix_comm _ fun a b hb ha => ?_
  simp only [Pi.mul_apply, Pi.mulSingle_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | simp

@[expose] def ggGLConjSL (g : GL (Fin n) F) :
    Matrix.SpecialLinearGroup (Fin n) F →* Matrix.SpecialLinearGroup (Fin n) F where
  toFun A := ⟨g.val * (A : Matrix (Fin n) (Fin n) F) * g.inv, by
    rw [Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, g.val_inv,
      Matrix.det_one, one_mul, A.2]⟩
  map_one' := by
    refine Subtype.ext ?_
    change g.val * 1 * g.inv = 1
    rw [Matrix.mul_one, g.val_inv]
  map_mul' A B := by
    refine Subtype.ext ?_
    change g.val * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) * g.inv =
      (g.val * (A : Matrix (Fin n) (Fin n) F) * g.inv) *
        (g.val * (B : Matrix (Fin n) (Fin n) F) * g.inv)
    calc g.val * ((A : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) * g.inv
        = g.val * (A : Matrix (Fin n) (Fin n) F) * (g.inv * g.val) *
            (B : Matrix (Fin n) (Fin n) F) * g.inv := by
          rw [g.inv_val, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_ggGLConjSL (g : GL (Fin n) F) (A : Matrix.SpecialLinearGroup (Fin n) F) :
    ((ggGLConjSL g A : Matrix.SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      g.val * (A : Matrix (Fin n) (Fin n) F) * g.inv :=
  rfl

theorem ggGLConjSL_eq_self {g : GL (Fin n) F} {u : Matrix.SpecialLinearGroup (Fin n) F}
    (hgu : g.val * (u : Matrix (Fin n) (Fin n) F) = u * g.val) : ggGLConjSL g u = u := by
  refine Subtype.ext ?_
  rw [coe_ggGLConjSL, hgu, Matrix.mul_assoc, g.val_inv, Matrix.mul_one]

theorem ggRootFusionWitnessAlt_of_realizes {G : Type} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G) {p : ℕ} {Bs D E G₀ M : Subgroup G}
    {t : StatedLieTag} {f : ℕ} {r : G} {u : Matrix.SpecialLinearGroup (Fin n) F}
    {g : GL (Fin n) F} (hgu : g.val * (u : Matrix (Fin n) (Fin n) F) = u * g.val) {y : G}
    (hy : ∀ z, y * ψ z * y⁻¹ = ψ (ggGLConjSL g z)) {m : G} (hm : m ∈ M)
    (hw : GGSixFusionWitness p Bs D E G₀ t f (m * y * m⁻¹)) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ u) := by
  refine Or.inr (Or.inl ⟨y, ?_, m, hm, hw⟩)
  have h := hy u
  rw [ggGLConjSL_eq_self hgu] at h
  calc y * ψ u = y * ψ u * y⁻¹ * y := by group
    _ = ψ u * y := by rw [h]

theorem ggRootFusionWitnessAlt_of_commute {G : Type} [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin n) F →* G) {p : ℕ} {Bs D E G₀ M : Subgroup G}
    {t : StatedLieTag} {f : ℕ} {r : G} {u d : Matrix.SpecialLinearGroup (Fin n) F}
    (hdu : d * u = u * d) {m : G} (hm : m ∈ M)
    (hw : GGSixFusionWitness p Bs D E G₀ t f (m * ψ d * m⁻¹)) :
    GGRootFusionWitnessAlt p Bs D E G₀ M t f r (ψ u) :=
  Or.inr (Or.inl ⟨ψ d, by rw [← map_mul, hdu, map_mul], m, hm, hw⟩)

end Witness

end CFSG.StandardType
