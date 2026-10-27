module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Coord

public section

namespace CFSG.Quasithin.F7Two.U3Odd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {p f : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def jGL : GL (HypIndex 1 1) K :=
  ⟨hypGram 1 1 K, hypGram 1 1 K, hypGram_mul_self, hypGram_mul_self⟩

theorem coe_jGL : ((jGL K : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
    hypGram 1 1 K := rfl

theorem coe_jGL_inv : (((jGL K)⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
    hypGram 1 1 K := rfl

theorem jGL_mul_self : jGL K * jGL K = 1 :=
  Units.ext (by rw [Units.val_mul, coe_jGL, hypGram_mul_self, Units.val_one])

theorem jGL_inv : (jGL K)⁻¹ = jGL K := inv_eq_of_mul_eq_one_right jGL_mul_self

theorem glAut_jGL (σ : K ≃+* K) : glAut σ (jGL K) = jGL K :=
  Units.ext (by rw [coe_glAut, coe_jGL, hypGram_map_ringEquiv])

theorem jGL_conj_apply (g : GL (HypIndex 1 1) K) (a b : HypIndex 1 1) :
    ((jGL K * g * (jGL K)⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a b =
      (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (hypPartner a) (hypPartner b) := by
  rw [Units.val_mul, Units.val_mul, coe_jGL, coe_jGL_inv, mul_hypGram_apply, hypGram_mul_apply]

variable (h : UnitaryFieldData p f K)

theorem jGL_mem_hypUnitary : jGL K ∈ hypUnitary h 1 1 := by
  rw [mem_hypUnitary, coe_jGL, hypGram_conjTranspose h, hypGram_mul_self, Matrix.one_mul]

theorem jGL_conj_mem_hypSU {g : GL (HypIndex 1 1) K} (hg : g ∈ hypSU h 1 1) :
    jGL K * g * (jGL K)⁻¹ ∈ hypSU h 1 1 := by
  have hx : (SemidirectProduct.inl (jGL K) : SemiGL (HypIndex 1 1) K) ∈
      semilinearSimilitudes h 1 1 :=
    ⟨1, one_ne_zero, map_one _, by
      rw [SemidirectProduct.left_inl, one_smul]
      exact mem_hypUnitary.mp (jGL_mem_hypUnitary h)⟩
  have := conj_mem_hypSU (h := h) hx ⟨g, hg⟩
  rwa [SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one, MulAut.one_apply] at this

@[expose] def lowerU : Subgroup (hypSU h 1 1) :=
  (fullUnitriangular 1 1 K).comap
    ((MulAut.conj (jGL K)).toMonoidHom.comp (hypSU h 1 1).subtype)

variable {h}

theorem mem_lowerU {g : hypSU h 1 1} :
    g ∈ lowerU h ↔
      jGL K * (g : GL (HypIndex 1 1) K) * (jGL K)⁻¹ ∈ fullUnitriangular 1 1 K := Iff.rfl

theorem mem_hypUnitriangular_iff {g : hypSU h 1 1} :
    g ∈ hypUnitriangular h 1 1 ↔ (g : GL (HypIndex 1 1) K) ∈ fullUnitriangular 1 1 K := Iff.rfl

theorem blockTriangular_of_diag {D : GL (HypIndex 1 1) K}
    (hD : ∃ d, (D : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d) :
    (D : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
  obtain ⟨d, hd⟩ := hD
  rw [hd]
  exact blockTriangular_diagonal _

theorem conj_mem_fullUnitriangular_of_diag {D : GL (HypIndex 1 1) K}
    (hD : ∃ d, (D : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d) (σ : K ≃+* K)
    {g : GL (HypIndex 1 1) K} (hg : g ∈ fullUnitriangular 1 1 K) :
    D * glAut σ g * D⁻¹ ∈ fullUnitriangular 1 1 K :=
  u3_conj_mem_fullUnitriangular (blockTriangular_of_diag hD) σ hg

theorem jGL_conj_diag {D : GL (HypIndex 1 1) K}
    (hD : ∃ d, (D : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d) :
    ∃ d, ((jGL K * D * (jGL K)⁻¹ : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d := by
  obtain ⟨d, hd⟩ := hD
  refine ⟨fun a => d (hypPartner a), ?_⟩
  ext a b
  rw [jGL_conj_apply, hd, diagonal_apply, diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · have : hypPartner a ≠ hypPartner b := fun e => hab (hypPartner_injective e)
    simp [hab, this]

theorem conj_mem_lowerU_aux {D : GL (HypIndex 1 1) K}
    (hD : ∃ d, (D : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d) (σ : K ≃+* K)
    {g : GL (HypIndex 1 1) K} (hg : jGL K * g * (jGL K)⁻¹ ∈ fullUnitriangular 1 1 K) :
    jGL K * (D * glAut σ g * D⁻¹) * (jGL K)⁻¹ ∈ fullUnitriangular 1 1 K := by
  have := conj_mem_fullUnitriangular_of_diag (jGL_conj_diag hD) σ hg
  have e : (jGL K * D * (jGL K)⁻¹) * glAut σ (jGL K * g * (jGL K)⁻¹) *
      (jGL K * D * (jGL K)⁻¹)⁻¹ = jGL K * (D * glAut σ g * D⁻¹) * (jGL K)⁻¹ := by
    rw [map_mul, map_mul, map_inv, glAut_jGL]
    group
  rwa [e] at this

end CFSG.Quasithin.F7Two.U3Odd
