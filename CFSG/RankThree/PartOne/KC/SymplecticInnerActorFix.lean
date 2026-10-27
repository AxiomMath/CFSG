module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBlock

public section

namespace CFSG.RankThree.PartOne.KCSpComm

open Matrix Polynomial Module CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (semilinConj semilinConj_apply semilin_symm_smul)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spFmap (g : SemiGSp r K) : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K) :=
  SteinbergBY.spSemilin g.right (g.left : GL (Fin r ⊕ Fin r) K)

theorem spFmap_apply (g : SemiGSp r K) (v : Fin r ⊕ Fin r → K) :
    spFmap g v = ((g.left : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
      fun i => g.right (v i) := rfl

theorem spFmap_smul (g : SemiGSp r K) (c : K) (v : Fin r ⊕ Fin r → K) :
    spFmap g (c • v) = g.right c • spFmap g v :=
  SteinbergBY.spSemilin_smul g.right _ c v

section Comm

variable [Finite K]

theorem spFmap_comm {p : ℕ} (hr : 1 ≤ r) (hp : Odd p) {x : StatedSp r K} (hxp : x ^ p = 1)
    (g : SemiGSp r K)
    (hg : spPsi r K g * conjAut r K (spXg x) * (spPsi r K g)⁻¹ = conjAut r K (spXg x))
    (v : Fin r ⊕ Fin r → K) : spFmap g (spEquiv x v) = spEquiv x (spFmap g v) := by
  have hXp : (spXg x) ^ p = 1 := Subtype.ext (by
    have := congrArg (fun y : StatedSp r K => (y : GL (Fin r ⊕ Fin r) K)) hxp
    simpa [spXg] using this)
  have h1 := sp_semilin_conj_eq_self hr hp (X := spXg x) x.2 hXp g hg
  have h2 := congrArg (fun A : gsp r K =>
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
  simp only [Subgroup.coe_mul, Units.val_mul, coe_gspAut] at h2
  set M := ((g.left : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set X := ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hX
  have h3 : M * X.map g.right = X * M := by
    set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
      (((g.left : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
    have hMinv : Mi * M = 1 := by
      rw [hMi, hM, ← Units.val_mul]
      simp
    have h2' : M * X.map g.right * Mi = X := by
      have h2'' := h2
      rw [coe_glFieldEquiv] at h2''
      exact h2''
    calc M * X.map g.right = M * X.map g.right * Mi * M := by
          rw [Matrix.mul_assoc _ Mi M, hMinv, Matrix.mul_one]
      _ = X * M := by rw [h2']
  rw [spFmap_apply, spFmap_apply, spEquiv_apply, spEquiv_apply, ← hX, ← hM,
    SteinbergBY.map_mulVec_ringEquiv', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]

end Comm

section Iterate

variable [Finite K]

theorem spFmap_iterate_scalar (hr : 1 ≤ r) {g : SemiGSp r K} {m : ℕ}
    (hm : (spPsi r K g) ^ m = 1) :
    g.right ^ m = 1 ∧ ∃ c : K, ∀ v, (spFmap g)^[m] v = c • v := by
  have h1 : (conjAut r K g.left * fieldAut r K g.right) ^ m = 1 := by
    rw [← spPsi_mk g.left g.right]
    exact hm
  rw [SteinbergBY.conjAut_mul_fieldAut_pow] at h1
  obtain ⟨hσ, c, hc⟩ :=
    (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff
      hr _ _).mp h1
  refine ⟨hσ, (c : K), fun v => ?_⟩
  have h2 := SteinbergBY.iterate_spSemilin g.right g.left m v
  change (⇑(SteinbergBY.spSemilin g.right (g.left : GL (Fin r ⊕ Fin r) K)))^[m] v = _ at h2
  change (⇑(SteinbergBY.spSemilin g.right (g.left : GL (Fin r ⊕ Fin r) K)))^[m] v = _
  rw [h2, hc, hσ]
  ext i
  simp [Matrix.mulVec_diagonal, Matrix.scalar_apply, Matrix.GeneralLinearGroup.coe_scalar]

theorem spFmap_map_primaryFactor {p : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {x : StatedSp r K}
    (hxp : x ^ p = 1) (hsq : Squarefree (minpoly K (spEnd x))) {g : SemiGSp r K} {j : ℕ}
    (hgj : (spPsi r K g) ^ p ^ j = 1)
    (hFx : ∀ v, spFmap g (spEquiv x v) = spEquiv x (spFmap g v)) {h : K[X]}
    (hh : h ∈ primaryFactors (spEnd x)) : h.map (g.right : K →+* K) = h := by
  obtain ⟨hσj, -⟩ := spFmap_iterate_scalar hr hgj
  exact KCOrthComm.map_eq_self_of_pow_eq_one hp hsq (spEnd_pow hxp) hσj
    (KCOrthComm.map_minpoly_eq (x := spEnd x) g.right (spFmap g) (spFmap_smul g) hFx) hh

end Iterate

section Conj

theorem blockScalar_semilinConj [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    {xe : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {σ : K ≃+* K} {F : (Fin r ⊕ Fin r → K) ≃+ (Fin r ⊕ Fin r → K)}
    (hF : ∀ (c : K) (v : Fin r ⊕ Fin r → K), F (c • v) = σ c • F v)
    (hFx : ∀ v, F (xe v) = xe (F v)) {h : K[X]} (hσh : h.map (σ : K →+* K) = h)
    {M : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} (hM : KCOrthComm.BlockScalar xe M h) :
    KCOrthComm.BlockScalar xe (semilinConj F σ hF M) h := by
  obtain ⟨f, hf⟩ := hM
  refine ⟨f.map (σ : K →+* K), fun v hv => ?_⟩
  have hFx' : ∀ v, F.symm (xe v) = xe (F.symm v) := fun v => by
    apply F.injective
    rw [AddEquiv.apply_symm_apply, hFx, AddEquiv.apply_symm_apply]
  have hF' : ∀ (c : K) (v : Fin r ⊕ Fin r → K), F.symm (c • v) = σ.symm c • F.symm v :=
    semilin_symm_smul F σ hF
  have hvF : F.symm v ∈ primaryComponent xe.toLinearMap h := by
    have := KCOrthComm.F_mem_primaryComponent σ.symm F.symm hF' hFx' hv
    rwa [KCOrthComm.map_symm_eq_self hσh] at this
  rw [semilinConj_apply, hf _ hvF,
    KCOrthComm.F_aeval σ F hF hFx, AddEquiv.apply_symm_apply]

theorem spFmap_mulVec_symm (g : SemiGSp r K)
    (Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (v : Fin r ⊕ Fin r → K) :
    spFmap g (Y *ᵥ (spFmap g).symm v) =
      (((g.left : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        Y.map g.right *
        (((g.left : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) *ᵥ v := by
  set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((g.left : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have h1 : (spFmap g).symm v = fun i => g.right.symm ((Mi *ᵥ v) i) := rfl
  rw [spFmap_apply, h1, SteinbergBY.map_mulVec_ringEquiv']
  have h2 : (fun i => g.right (g.right.symm ((Mi *ᵥ v) i))) = Mi *ᵥ v :=
    funext fun i => RingEquiv.apply_symm_apply _ _
  rw [h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

end Conj

end CFSG.RankThree.PartOne.KCSpComm
