module

public import CFSG.RankThree.PartOne.KC.UnitaryRigidityFrame

public section

namespace CFSG.RankThree.PartOne.KCUnitaryBlock

open Polynomial Module Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame

section Degree

variable {K : Type} [Field K]

theorem dualPoly_X_sub_C {σ : K →+* K} {μ : K} (hμ : σ μ ≠ 0) :
    dualPoly σ (X - C μ) = X - C (σ μ)⁻¹ := by
  have h0 : (X - C μ : K[X]).coeff 0 = -μ := by simp
  have hmap : (X - C μ : K[X]).map σ = X + C (-σ μ) := by simp [sub_eq_add_neg]
  have hrev : (X + C (-σ μ) : K[X]).reverse = 1 + C (-σ μ) * X := by
    rw [Polynomial.reverse_add_C]
    have hX : (X : K[X]).reverse = 1 := by
      have h1 := Polynomial.reverse_mul_X (1 : K[X])
      rw [one_mul] at h1
      rw [h1]
      simpa using Polynomial.reverse_C (1 : K)
    rw [hX, natDegree_X, pow_one, mul_comm]
  have hne : (-σ μ)⁻¹ * (-σ μ) = 1 := inv_mul_cancel₀ (neg_ne_zero.mpr hμ)
  unfold dualPoly
  rw [h0, map_neg, hmap, hrev]
  calc C (-σ μ)⁻¹ * (1 + C (-σ μ) * X)
      = C (-σ μ)⁻¹ + C ((-σ μ)⁻¹ * (-σ μ)) * X := by rw [C_mul]; ring
    _ = X - C (σ μ)⁻¹ := by rw [hne, C_1, inv_neg, C_neg]; ring

theorem eq_one_of_norm_eq_one {μ : K} (d : AdjoinRoot (X - C μ : K[X]))
    (hd : Algebra.norm K d = 1) : d = 1 := by
  have : Fact (Irreducible (X - C μ : K[X])) := ⟨irreducible_X_sub_C μ⟩
  obtain ⟨r, rfl⟩ := AdjoinRoot.mk_surjective d
  have h1 : AdjoinRoot.mk (X - C μ : K[X]) r = algebraMap K _ (r.eval μ) := by
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, AdjoinRoot.mk_eq_mk]
    exact X_sub_C_dvd_sub_C_eval
  rw [h1, Algebra.norm_algebraMap, finrank_adjoinRoot, natDegree_X_sub_C, pow_one] at hd
  rw [h1, hd, map_one]

end Degree

section Block

universe u

variable {ℓ f : ℕ} {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {hK : UnitaryFieldData ℓ f K} {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem mem_specialBlock_of_degree_one (H : UnitaryPrimaryData hK.bar B x) {μ : K}
    (hμ : hK.bar μ * μ = 1)
    (ha : (X - C μ : K[X]) ∈ primaryFactors (x : Module.End K V))
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ sesqUnitaryGroup B)
    (hcomm : Commute (g : Module.End K V) (x : Module.End K V))
    (hid : ∀ v : V, (∀ w ∈ primaryComponent (x : Module.End K V) (X - C μ), B w v = 0) →
      (g : Module.End K V) v = v)
    (hdet : LinearMap.det (g : Module.End K V) = 1) :
    g ∈ specialBlock B x (X - C μ) := by
  have : Fact (Irreducible (X - C μ : K[X])) := ⟨irreducible_X_sub_C μ⟩
  have hbar0 : hK.bar μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ
    exact zero_ne_one hμ
  have hdual : dualPoly hK.bar (X - C μ) = X - C μ := by
    rw [dualPoly_X_sub_C hbar0]
    congr 2
    exact (inv_eq_of_mul_eq_one_right hμ)
  have hunit : g ∈ unitaryCentralizer B x := mem_unitaryCentralizer.mpr ⟨hg, hcomm⟩
  have hoff : ∀ b ∈ primaryFactors (x : Module.End K V), b ≠ X - C μ →
      ∀ v ∈ primaryComponent (x : Module.End K V) b, (g : Module.End K V) v = v := by
    intro b hb hbμ v hv
    refine hid v fun w hw => ?_
    exact orthogonal_of_ne_dualPoly H ha hb (by rw [hdual]; exact hbμ) hw hv
  have hgc : g ∈ gl_centralizer x := mem_gl_centralizer.mpr hcomm
  refine mem_specialBlock.mpr ⟨⟨hunit, fun b hb hbS v hv => hoff b hb (fun hbμ =>
    hbS (Or.inl hbμ)) v hv⟩, hgc, ?_⟩
  apply Units.ext
  rw [blockDetHom, MonoidHom.comp_apply, blockGLDet, Units.coe_map]
  set γ := (blockRestrict x (X - C μ) ⟨g, hgc⟩).val with hγ
  have hres : γ.restrictScalars K = (g : Module.End K V).restrict
      (fun _ hv => apply_mem_primaryComponent hcomm hv) := by
    ext v
    rfl
  have h1 := det_restrictScalars_blockGL (x := (x : Module.End K V)) (X - C μ) γ
  rw [hres, ← det_eq_det_restrict_of_trivial_off H.squarefree ha hcomm hoff, hdet] at h1
  have h2 := eq_one_of_norm_eq_one (LinearMap.det γ) h1.symm
  rw [h2]
  rfl

end Block

section Torus

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

theorem toLinU_apply_eq (A : primeFormUnitary h (idGram K n)) (v : Fin n → K) :
    ((toLinU h n A : LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem idForm_apply_of_eigen {g : LinearMap.GeneralLinearGroup K (Fin n → K)}
    (hg : g ∈ sesqUnitaryGroup (idForm h n)) {μ : K} (hμ : h.bar μ * μ = 1) {b : Fin n → K}
    (hb : (g : Module.End K (Fin n → K)) b = μ • b) (v : Fin n → K) :
    idForm h n b ((g : Module.End K (Fin n → K)) v) = μ * idForm h n b v := by
  have h1 := (mem_sesqUnitaryGroup.mp hg) b v
  rw [hb, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
  have h2 : idForm h n b ((g : Module.End K (Fin n → K)) v) =
      μ * (h.bar μ * idForm h n b ((g : Module.End K (Fin n → K)) v)) := by
    rw [← mul_assoc, mul_comm μ, hμ, one_mul]
  rw [h2, h1]

theorem torusUnitary_mem_idSpecialBlock (x : gramSU h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n (liftUnitary x))) {μ : K}
    (hμ : h.bar μ * μ = 1)
    (ha : (X - C μ : K[X]) ∈ primaryFactors ((toLinU h n (liftUnitary x) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)))
    {b₁ b₂ : Fin n → K} (hb : IsONPair h b₁ b₂)
    (hx₁ : ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₁ = μ • b₁)
    (hx₂ : ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) b₂ = μ • b₂) (c : Kˣ) (hc : h.norm (c : K) = 1) :
    torusUnitary h hb c hc ∈ idSpecialBlock h x (X - C μ) := by
  set T := torusUnitary h hb c hc with hT
  have hTmat : (((T : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = torusMat h b₁ b₂ c := rfl
  have hgapply : ∀ v, ((toLinU h n T : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = torusMat h b₁ b₂ c *ᵥ v := fun v => by
    rw [toLinU_apply_eq, hTmat]
  have hxiso := toLinU_mem (liftUnitary x)
  refine mem_specialBlock_of_degree_one H hμ ha (toLinU_mem T) ?_ ?_ ?_
  · show (_ : Module.End K (Fin n → K)) * _ = _ * _
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hgapply, hgapply, torusMat_mulVec,
      torusMat_mulVec, map_add, map_add, map_smul, map_smul, hx₁, hx₂,
      idForm_apply_of_eigen h hxiso hμ hx₁, idForm_apply_of_eigen h hxiso hμ hx₂]
    module
  · intro v hv
    have h1 : idForm h n b₁ v = 0 := hv b₁ (by simp [mem_primaryComponent, hx₁])
    have h2 : idForm h n b₂ v = 0 := hv b₂ (by simp [mem_primaryComponent, hx₂])
    rw [hgapply, torusMat_mulVec, h1, h2]
    simp
  · have : ((toLinU h n T : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) = Matrix.toLin' (torusMat h b₁ b₂ c) :=
      LinearMap.ext fun v => by rw [hgapply, Matrix.toLin'_apply]
    rw [this, LinearMap.det_toLin']
    exact det_torusMat h hb c.ne_zero

end Torus

end CFSG.RankThree.PartOne.KCUnitaryBlock
