module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
import CFSG.RankThree.GF2n.Stroth80.Sec715ConjAvg

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Module

theorem eq_zero_of_forall_semilinear {K V W : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    {S : Set ((V →ₗ[K] V) × (W →ₗ[K] W))} (g : V →+ W)
    (hg : ∀ p ∈ S, ∀ v, g (p.1 v) = p.2 (g v))
    (hsemi : ∀ σ : K ≃+* K, ∀ h : V →+ W, (∀ (c : K) (v : V), h (c • v) = σ c • h v) →
      (∀ p ∈ S, ∀ v, h (p.1 v) = p.2 (h v)) → h = 0) :
    g = 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  set b := Module.finBasis (ZMod 2) K
  have hgF : ∀ (r : ZMod 2) (v : V),
      g (algebraMap (ZMod 2) K r • v) = algebraMap (ZMod 2) K r • g v := by
    intro r v
    have e : algebraMap (ZMod 2) K r = ((r.val : ℕ) : K) := by
      rw [← map_natCast (algebraMap (ZMod 2) K), ZMod.natCast_zmod_val]
    rw [e, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  have hexp : ∀ (k : K) (v : V),
      k • v = ∑ j, algebraMap (ZMod 2) K (b.repr k j) • b j • v := by
    intro k v
    conv_lhs => rw [← b.sum_repr k]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_smul]
  let gσ : (K ≃ₐ[ZMod 2] K) → V →+ W := fun σ =>
    { toFun := fun v => ∑ i, σ (b.traceDual i) • g (b i • v)
      map_zero' := by simp
      map_add' := fun v v' => by simp [smul_add, Finset.sum_add_distrib] }
  have hgσ : ∀ σ v, gσ σ v = ∑ i, σ (b.traceDual i) • g (b i • v) := fun σ v => rfl
  have hsemiσ : ∀ (σ : K ≃ₐ[ZMod 2] K) (c : K) (v : V), gσ σ (c • v) = σ c • gσ σ v := by
    intro σ c v
    have e1 : ∀ i, g ((b i * c) • v) =
        ∑ j, algebraMap (ZMod 2) K (b.repr (b i * c) j) • g (b j • v) := by
      intro i
      rw [hexp (b i * c) v, map_sum]
      exact Finset.sum_congr rfl fun j _ => hgF _ _
    rw [hgσ, hgσ]
    simp only [smul_smul, e1, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have h := congrArg σ (sum_repr_mul_smul_traceDual b c j)
    rw [map_sum, map_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def, mul_comm]
  have hSσ : ∀ σ, ∀ p ∈ S, ∀ v, gσ σ (p.1 v) = p.2 (gσ σ v) := by
    intro σ p hp v
    rw [hgσ, hgσ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul p.2, ← hg p hp, map_smul p.1]
  have hzero : ∀ σ, gσ σ = 0 := fun σ =>
    hsemi σ.toRingEquiv (gσ σ) (hsemiσ σ) (hSσ σ)
  ext v
  have hone : ∑ i, algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K (b.traceDual i)) * b i = 1 := by
    conv_rhs => rw [← b.sum_repr 1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_eq_trace_mul_traceDual, one_mul, Algebra.smul_def]
  have hsum : g v = ∑ σ : K ≃ₐ[ZMod 2] K, gσ σ v := by
    simp only [hgσ]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← trace_eq_sum_automorphisms]
    conv_lhs => rw [← one_smul K v, ← hone, Finset.sum_smul]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul, hgF]
  rw [hsum]
  simp [hzero]

private theorem symm_comp_smul_map {K : Type*} [Field K] (σ : K ≃+* K)
    (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K) :
    (fun i => σ.symm ((Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v) i)) =
      A • fun i => σ.symm (v i) := by
  ext i
  simp only [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec,
    dotProduct, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, map_sum, map_mul, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

theorem eq_scalar_of_sl4HomW3 (hW3 : SL4HomW3Statement) {K : Type} [Field K] [Finite K]
    [CharP K 2] [Algebra (ZMod 2) K] (hK : 4 ≤ Nat.card K)
    (g : (Fin 4 → K) → Module.End K (Fin 3 ⊕ Fin 3 → K))
    (hadd : ∀ v w : Fin 4 → K, ∃ c : K, g (v + w) = g v + g w + c • LinearMap.id)
    (hg : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) (v : Fin 4 → K), ∃ c : K,
      g (A • v) = (PartOne.K159.Klein.rho A).toLinearMap ∘ₗ g v ∘ₗ
        (PartOne.K159.Klein.rho A⁻¹).toLinearMap + c • LinearMap.id) :
    ∀ v, ∃ c : K, g v = c • LinearMap.id := by
  classical
  set I := K ∙ (LinearMap.id : Module.End K (Fin 3 ⊕ Fin 3 → K)) with hI
  let cj : Matrix.SpecialLinearGroup (Fin 4) K → Module.End K (Fin 3 ⊕ Fin 3 → K) →ₗ[K]
      Module.End K (Fin 3 ⊕ Fin 3 → K) := fun A =>
    (LinearMap.llcomp K _ _ _ (PartOne.K159.Klein.rho A).toLinearMap).comp
      ((LinearMap.llcomp K _ _ _).flip (PartOne.K159.Klein.rho A⁻¹).toLinearMap)
  have hcj : ∀ A X, cj A X = (PartOne.K159.Klein.rho A).toLinearMap ∘ₗ X ∘ₗ
      (PartOne.K159.Klein.rho A⁻¹).toLinearMap := fun A X => rfl
  have hcjI : ∀ A, I ≤ I.comap (cj A) := by
    intro A X hX
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hX
    refine Submodule.mem_comap.mpr (Submodule.mem_span_singleton.mpr ⟨c, ?_⟩)
    rw [hcj]
    ext w
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe, map_smul]
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one PartOne.K159.Klein.rho]
    rfl
  let cjQ : Matrix.SpecialLinearGroup (Fin 4) K → (Module.End K (Fin 3 ⊕ Fin 3 → K) ⧸ I) →ₗ[K]
      (Module.End K (Fin 3 ⊕ Fin 3 → K) ⧸ I) := fun A => I.mapQ I (cj A) (hcjI A)
  have hI0 : ∀ c : K, I.mkQ (c • LinearMap.id) = 0 := fun c =>
    (Submodule.Quotient.mk_eq_zero I).mpr (Submodule.mem_span_singleton.mpr ⟨c, rfl⟩)
  let gQ : (Fin 4 → K) →+ (Module.End K (Fin 3 ⊕ Fin 3 → K) ⧸ I) :=
    AddMonoidHom.mk' (fun v => I.mkQ (g v)) fun v w => by
      obtain ⟨c, hc⟩ := hadd v w
      rw [hc, map_add, map_add, hI0, add_zero]
  have hgQ : ∀ A v, gQ (A • v) = cjQ A (gQ v) := by
    intro A v
    obtain ⟨c, hc⟩ := hg A v
    show I.mkQ (g (A • v)) = I.mapQ I (cj A) (hcjI A) (I.mkQ (g v))
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, hc, ← hcj,
      Submodule.Quotient.mk_add,
      (Submodule.Quotient.mk_eq_zero I).mpr (Submodule.mem_span_singleton.mpr ⟨c, rfl⟩),
      add_zero]
  let S : Set (((Fin 4 → K) →ₗ[K] (Fin 4 → K)) ×
      ((Module.End K (Fin 3 ⊕ Fin 3 → K) ⧸ I) →ₗ[K] (Module.End K (Fin 3 ⊕ Fin 3 → K) ⧸ I))) :=
    Set.range fun A : Matrix.SpecialLinearGroup (Fin 4) K => (Matrix.mulVecLin A.1, cjQ A)
  have hzero : gQ = 0 := by
    refine eq_zero_of_forall_semilinear (S := S) gQ ?_ ?_
    · rintro _ ⟨A, rfl⟩ v
      exact hgQ A v
    · intro σ h hσ hhS
      let τ : (Fin 4 → K) → (Fin 4 → K) := fun v i => σ.symm (v i)
      have hτadd : ∀ v w, τ (v + w) = τ v + τ w := fun v w => by ext i; simp [τ]
      have hτsmul : ∀ (c : K) v, τ (c • v) = σ.symm c • τ v := fun c v => by ext i; simp [τ]
      let f₀ : (Fin 4 → K) →ₗ[K] (Module.End K (Fin 3 ⊕ Fin 3 → K) ⧸ I) :=
        { toFun := fun v => h (τ v)
          map_add' := fun v w => by rw [hτadd, map_add]
          map_smul' := fun c v => by
            rw [hτsmul, hσ, RingEquiv.apply_symm_apply]
            rfl }
      have hf₀ : ∀ (A : Matrix.SpecialLinearGroup (Fin 4) K) v,
          f₀ (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v) = cjQ A (f₀ v) := by
        intro A v
        show h (τ (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v)) = cjQ A (h (τ v))
        rw [show τ (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v) = A • τ v from
          symm_comp_smul_map σ A v]
        exact hhS _ ⟨A, rfl⟩ (τ v)
      obtain ⟨f, hf⟩ := Module.projective_lifting_property I.mkQ f₀ (Submodule.mkQ_surjective I)
      have hW := hW3 K hK σ f fun A v => by
        have e : I.mkQ (f (Matrix.SpecialLinearGroup.map (σ : K →+* K) A • v)) =
            I.mkQ (cj A (f v)) := by
          rw [← LinearMap.comp_apply, hf, hf₀, ← hf, LinearMap.comp_apply]
          rfl
        rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
          Submodule.mem_span_singleton] at e
        obtain ⟨c, hc⟩ := e
        exact ⟨c, by rw [← hcj, hc, add_sub_cancel]⟩
      refine AddMonoidHom.ext fun v => ?_
      have hv : h v = f₀ (fun i => σ (v i)) := by
        show h v = h (τ fun i => σ (v i))
        congr 1
        ext i
        simp [τ]
      obtain ⟨c, hc⟩ := hW (fun i => σ (v i))
      rw [AddMonoidHom.zero_apply, hv, ← hf, LinearMap.comp_apply, hc, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  intro v
  have h0 : gQ v = 0 := by rw [hzero]; rfl
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.Quotient.mk_eq_zero I).mp h0)
  exact ⟨c, hc.symm⟩

end CFSG.RankThree.GF2n.Stroth80
