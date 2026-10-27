module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Smith81.S81Z.Tr

variable {K K' K'' ι : Type*} [Field K] [Field K'] [Field K'']

@[expose] noncomputable def vMapG (σ : K ≃+* K') : (ι →₀ K) ≃+ (ι →₀ K') :=
  Finsupp.mapRange.addEquiv σ.toAddEquiv

@[simp]
theorem vMapG_apply (σ : K ≃+* K') (v : ι →₀ K) (a : ι) : vMapG σ v a = σ (v a) := by
  simp [vMapG, Finsupp.mapRange_apply]

theorem vMapG_smul (σ : K ≃+* K') (c : K) (v : ι →₀ K) :
    vMapG σ (c • v) = σ c • vMapG σ v := by
  ext a
  simp [vMapG_apply, map_mul]

theorem vMapG_symm_smul (σ : K ≃+* K') (c : K') (v : ι →₀ K') :
    (vMapG σ).symm (c • v) = σ.symm c • (vMapG σ).symm v := by
  apply (vMapG σ).injective
  rw [AddEquiv.apply_symm_apply, vMapG_smul, AddEquiv.apply_symm_apply,
    RingEquiv.apply_symm_apply]

theorem vMapG_single (σ : K ≃+* K') (a : ι) (c : K) :
    vMapG σ (Finsupp.single a c) = Finsupp.single a (σ c) := by
  ext b
  by_cases h : a = b
  · subst h
    simp
  · simp [Finsupp.single_apply, h]

theorem vMapG_trans (σ : K ≃+* K') (σ' : K' ≃+* K'') (v : ι →₀ K) :
    vMapG σ' (vMapG σ v) = vMapG (σ.trans σ') v := by
  ext a
  simp [vMapG_apply]

theorem vMapG_refl (v : ι →₀ K) : vMapG (RingEquiv.refl K) v = v := by
  ext a
  simp [vMapG_apply]

theorem vMapG_surj (σ : K ≃+* K') (w : ι →₀ K') : ∃ v : ι →₀ K, vMapG σ v = w :=
  ⟨(vMapG σ).symm w, (vMapG σ).apply_symm_apply w⟩

@[expose] noncomputable def twistEnd (σ : K ≃+* K') (φ : Module.End K (ι →₀ K)) :
    Module.End K' (ι →₀ K') where
  toFun v := vMapG σ (φ ((vMapG σ).symm v))
  map_add' v w := by simp [map_add]
  map_smul' c v := by
    simp [vMapG_symm_smul, vMapG_smul, map_smul, RingEquiv.apply_symm_apply]

theorem twistEnd_vMap (σ : K ≃+* K') (φ : Module.End K (ι →₀ K)) (v : ι →₀ K) :
    twistEnd σ φ (vMapG σ v) = vMapG σ (φ v) := by
  simp [twistEnd]

theorem twist_ext (σ : K ≃+* K') {f g : Module.End K' (ι →₀ K')}
    (h : ∀ v : ι →₀ K, f (vMapG σ v) = g (vMapG σ v)) : f = g := by
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := vMapG_surj σ w
  exact h v

theorem end_ext_single {f g : Module.End K' (ι →₀ K')}
    (h : ∀ a : ι, f (Finsupp.single a 1) = g (Finsupp.single a 1)) : f = g := by
  refine Finsupp.lhom_ext' fun a => LinearMap.ext_ring ?_
  simpa using h a

theorem twistEnd_one (σ : K ≃+* K') : twistEnd σ (1 : Module.End K (ι →₀ K)) = 1 := by
  apply twist_ext σ
  intro v
  simp [twistEnd_vMap, Module.End.one_apply]

theorem twistEnd_mul (σ : K ≃+* K') (φ ψ : Module.End K (ι →₀ K)) :
    twistEnd σ (φ * ψ) = twistEnd σ φ * twistEnd σ ψ := by
  apply twist_ext σ
  intro v
  simp [twistEnd_vMap, Module.End.mul_apply]

theorem twistEnd_add (σ : K ≃+* K') (φ ψ : Module.End K (ι →₀ K)) :
    twistEnd σ (φ + ψ) = twistEnd σ φ + twistEnd σ ψ := by
  apply twist_ext σ
  intro v
  simp [twistEnd_vMap, map_add]

theorem twistEnd_smul (σ : K ≃+* K') (c : K) (φ : Module.End K (ι →₀ K)) :
    twistEnd σ (c • φ) = σ c • twistEnd σ φ := by
  apply twist_ext σ
  intro v
  simp [twistEnd_vMap, vMapG_smul]

theorem twistEnd_zero (σ : K ≃+* K') : twistEnd σ (0 : Module.End K (ι →₀ K)) = 0 := by
  apply twist_ext σ
  intro v
  simp [twistEnd_vMap]

theorem twistEnd_trans (σ : K ≃+* K') (σ' : K' ≃+* K'') (φ : Module.End K (ι →₀ K)) :
    twistEnd σ' (twistEnd σ φ) = twistEnd (σ.trans σ') φ := by
  apply twist_ext (σ.trans σ')
  intro v
  rw [twistEnd_vMap (σ.trans σ') φ v, ← vMapG_trans σ σ' v,
    twistEnd_vMap σ' (twistEnd σ φ) (vMapG σ v), twistEnd_vMap σ φ v,
    vMapG_trans σ σ' (φ v)]

theorem twistEnd_refl (φ : Module.End K (ι →₀ K)) : twistEnd (RingEquiv.refl K) φ = φ := by
  apply twist_ext (RingEquiv.refl K)
  intro v
  rw [twistEnd_vMap, vMapG_refl, vMapG_refl]

theorem twistEnd_single (σ : K ≃+* K') (φ : Module.End K (ι →₀ K)) (a : ι) :
    twistEnd σ φ (Finsupp.single a 1) = vMapG σ (φ (Finsupp.single a 1)) := by
  have h1 : (vMapG σ).symm (Finsupp.single a 1) = Finsupp.single a 1 := by
    rw [AddEquiv.symm_apply_eq, vMapG_single, map_one]
  show vMapG σ (φ ((vMapG σ).symm (Finsupp.single a 1))) = _
  rw [h1]

theorem twistEnd_linearCombination (σ : K ≃+* K') (f : ι → (ι →₀ K)) :
    twistEnd σ (Finsupp.linearCombination K f) =
      Finsupp.linearCombination K' (fun a => vMapG σ (f a)) := by
  apply end_ext_single
  intro a
  simp [twistEnd_single, Finsupp.linearCombination_single]

@[expose] noncomputable def twistEndEquiv (σ : K ≃+* K') :
    Module.End K (ι →₀ K) ≃* Module.End K' (ι →₀ K') where
  toFun := twistEnd σ
  invFun := twistEnd σ.symm
  left_inv φ := by
    show twistEnd σ.symm (twistEnd σ φ) = φ
    rw [twistEnd_trans, RingEquiv.self_trans_symm, twistEnd_refl]
  right_inv ψ := by
    show twistEnd σ (twistEnd σ.symm ψ) = ψ
    rw [twistEnd_trans, RingEquiv.symm_trans_self, twistEnd_refl]
  map_mul' φ ψ := twistEnd_mul σ φ ψ

end CFSG.RankThree.GF2n.Smith81.S81Z.Tr
