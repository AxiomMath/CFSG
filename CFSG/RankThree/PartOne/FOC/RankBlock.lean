module

public import CFSG.RankThree.PartOne.FOC.RankTorus
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne

universe u

section Iota

variable {E : Type} {W : Type*} [Field E] [AddCommGroup W] [Module E W] {m : ℕ}

@[expose] noncomputable def iotaGL (e : Basis (Fin m) E W) : GL (Fin m) E →* (W →ₗ[E] W)ˣ :=
  Units.map (Matrix.toLinAlgEquiv e).toAlgHom.toMonoidHom

theorem iotaGL_apply (e : Basis (Fin m) E W) (A : GL (Fin m) E) :
    ((iotaGL e A : (W →ₗ[E] W)ˣ) : W →ₗ[E] W) =
      Matrix.toLin e e (A : Matrix (Fin m) (Fin m) E) := rfl

theorem det_iotaGL (e : Basis (Fin m) E W) (A : GL (Fin m) E) :
    LinearMap.det ((iotaGL e A : (W →ₗ[E] W)ˣ) : W →ₗ[E] W) =
      (A : Matrix (Fin m) (Fin m) E).det := by
  rw [iotaGL_apply, LinearMap.det_toLin]

theorem iotaGL_injective (e : Basis (Fin m) E W) : Function.Injective (iotaGL e) := by
  intro A B h
  apply Units.ext
  have := congrArg (fun u : (W →ₗ[E] W)ˣ => (u : W →ₗ[E] W)) h
  simp only [iotaGL_apply] at this
  exact (Matrix.toLin e e).injective this

theorem iotaGL_entry (e : Basis (Fin m) E W) (A : GL (Fin m) E) (i j : Fin m) :
    e.repr (((iotaGL e A : (W →ₗ[E] W)ˣ) : W →ₗ[E] W) (e j)) i =
      (A : Matrix (Fin m) (Fin m) E) i j := by
  rw [iotaGL_apply, ← LinearMap.toMatrix_apply, LinearMap.toMatrix_toLin]

theorem iotaGL_mem_sesqUnitary {σ : E →+* E} {Hf : W →ₛₗ[σ] W →ₗ[E] E} (e : Basis (Fin m) E W)
    (he : ∀ i j, Hf (e i) (e j) = if i = j then 1 else 0) (A : GL (Fin m) E)
    (hA : UnitaryMat σ (A : Matrix (Fin m) (Fin m) E)) : iotaGL e A ∈ sesqUnitaryGroup Hf := by
  rw [mem_sesqUnitaryGroup]
  have hfr : ⇑e ∈ CFSG.LinearGroups.orthonormalFrames Hf m :=
    CFSG.LinearGroups.mem_orthonormalFrames.mpr he
  refine CFSG.LinearGroups.isometry_of_mem_orthonormalFrames e hfr
    (φ := ((iotaGL e A : (W →ₗ[E] W)ˣ) : W →ₗ[E] W)) ?_
  rw [CFSG.LinearGroups.mem_orthonormalFrames]
  intro i j
  rw [iotaGL_apply, Matrix.toLin_self, Matrix.toLin_self,
    CFSG.LinearGroups.sesq_sum_smul_of_mem hfr]
  have h1 := congrFun (congrFun hA i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simpa [Matrix.transpose_apply, Matrix.map_apply] using h1

end Iota

section Abstract

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type u}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_torus_of_iso (a : primaryFactors (x : Module.End K V))
    (Γ : Subgroup (blockGL (x : Module.End K V) (a : K[X])))
    (φ : orbitFactor B x (a : K[X]) ≃* Γ)
    (hφ : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v)
    {M : Type} [CommGroup M]
    (R₁ : M × M × M →* blockGL (x : Module.End K V) (a : K[X])) (hR₁Γ : ∀ r, R₁ r ∈ Γ)
    (hR₁det : ∀ r, LinearMap.det ((R₁ r : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) = 1)
    (hR₁inj : Function.Injective R₁) (u₁ : blockGL (x : Module.End K V) (a : K[X]))
    (hu₁Γ : u₁ ∈ Γ) (hu₁sq : u₁ ^ 2 = 1)
    (hu₁det : LinearMap.det ((u₁ : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) = 1)
    (hu₁comm : ∀ r, u₁ * R₁ r = R₁ r * u₁)
    (hu₁ns : ∀ c : AdjoinRoot (a : K[X]), ∃ w : primaryComponent (x : Module.End K V) (a : K[X]),
      ((u₁ : blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) w ≠ c • w) :
    ∃ (R : M × M × M →* LinearMap.GeneralLinearGroup K V) (u : LinearMap.GeneralLinearGroup K V),
      (∀ r, R r ∈ specialBlock B x (a : K[X])) ∧ u ∈ specialBlock B x (a : K[X]) ∧
      Function.Injective R ∧ u ^ 2 = 1 ∧ (∀ r, u * R r = R r * u) ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  classical
  let R₂ : M × M × M →* Γ := R₁.codRestrict Γ hR₁Γ
  have hsb : ∀ γ : Γ, LinearMap.det ((γ : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 →
      ((φ.symm γ : orbitFactor B x (a : K[X])) : LinearMap.GeneralLinearGroup K V) ∈
        specialBlock B x (a : K[X]) := by
    intro γ hγ
    rw [mem_specialBlock]
    refine ⟨(φ.symm γ).2, orbitFactor_le_gl_centralizer (φ.symm γ).2, ?_⟩
    have hres : blockRestrict x (a : K[X]) ⟨((φ.symm γ : orbitFactor B x (a : K[X])) :
        LinearMap.GeneralLinearGroup K V), orbitFactor_le_gl_centralizer (φ.symm γ).2⟩ =
        (γ : blockGL (x : Module.End K V) (a : K[X])) := by
      refine blockGL_ext fun v hv => ?_
      rw [blockApply_blockRestrict]
      have := hφ (φ.symm γ) v hv
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    apply Units.ext
    change LinearMap.det ((blockRestrict x (a : K[X]) ⟨((φ.symm γ : orbitFactor B x (a : K[X])) :
      LinearMap.GeneralLinearGroup K V), orbitFactor_le_gl_centralizer (φ.symm γ).2⟩ :
        blockGL (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) = _
    rw [hres, hγ]
    rfl
  refine ⟨(orbitFactor B x (a : K[X])).subtype.comp (φ.symm.toMonoidHom.comp R₂),
    ((φ.symm ⟨u₁, hu₁Γ⟩ : orbitFactor B x (a : K[X])) : LinearMap.GeneralLinearGroup K V),
    fun r => hsb (R₂ r) (hR₁det r), hsb ⟨u₁, hu₁Γ⟩ hu₁det, ?_, ?_, ?_, ?_⟩
  · intro r r' h
    have h1 : φ.symm (R₂ r) = φ.symm (R₂ r') := Subtype.ext h
    have h2 := φ.symm.injective h1
    exact hR₁inj (congrArg Subtype.val h2)
  · have : (⟨u₁, hu₁Γ⟩ : Γ) ^ 2 = 1 := Subtype.ext hu₁sq
    have h2 : (φ.symm ⟨u₁, hu₁Γ⟩) ^ 2 = 1 := by rw [← map_pow, this, map_one]
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro r
    have : (⟨u₁, hu₁Γ⟩ : Γ) * R₂ r = R₂ r * ⟨u₁, hu₁Γ⟩ := Subtype.ext (hu₁comm r)
    have h2 : φ.symm ⟨u₁, hu₁Γ⟩ * φ.symm (R₂ r) = φ.symm (R₂ r) * φ.symm ⟨u₁, hu₁Γ⟩ := by
      rw [← map_mul, ← map_mul, this]
    exact congrArg Subtype.val h2
  · rintro ⟨c, hc⟩
    obtain ⟨w, hw⟩ := hu₁ns c
    apply hw
    have h1 := hφ (φ.symm ⟨u₁, hu₁Γ⟩) w.1 w.2
    rw [MulEquiv.apply_symm_apply] at h1
    have h3 := hc w
    exact Subtype.ext (h1.trans h3)


theorem torus_data_blockGL (a : primaryFactors (x : Module.End K V))
    (e : Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])))
    (hm : 5 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]))
    (M : Subgroup (AdjoinRoot (a : K[X]))ˣ) :
    (∀ r : M × M × M, LinearMap.det (((iotaGL e).comp (torusRep _ _ M) r : blockGL
      (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) = 1) ∧
    Function.Injective ((iotaGL e).comp (torusRep (primaryMultiplicity (x : Module.End K V)
      (a : K[X])) (AdjoinRoot (a : K[X])) M)) ∧
    (iotaGL e (invol _ (AdjoinRoot (a : K[X])) (by omega)) : blockGL (x : Module.End K V)
      (a : K[X])) ^ 2 = 1 ∧
    LinearMap.det ((iotaGL e (invol _ (AdjoinRoot (a : K[X])) (by omega)) : blockGL
      (x : Module.End K V) (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
        (primaryComponent (x : Module.End K V) (a : K[X]))) = 1 ∧
    (∀ r : M × M × M, (iotaGL e (invol _ (AdjoinRoot (a : K[X])) (by omega)) : blockGL
      (x : Module.End K V) (a : K[X])) * ((iotaGL e).comp (torusRep _ _ M) r) =
        ((iotaGL e).comp (torusRep _ _ M) r) * (iotaGL e (invol _ (AdjoinRoot (a : K[X]))
          (by omega)))) ∧
    (∀ c : AdjoinRoot (a : K[X]), ∃ w : primaryComponent (x : Module.End K V) (a : K[X]),
      ((iotaGL e (invol _ (AdjoinRoot (a : K[X])) (by omega)) : blockGL (x : Module.End K V)
        (a : K[X])) : Module.End (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X]))) w ≠ c • w) := by
  refine ⟨fun r => ?_, (iotaGL_injective e).comp (torusRep_injective hm M), ?_, ?_, fun r => ?_,
    fun c => ?_⟩
  · rw [MonoidHom.comp_apply]
    refine (det_iotaGL e _).trans ?_
    have := congrArg Units.val (det_torusRep hm M r)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  · rw [← map_pow, invol_sq, map_one]
  · refine (det_iotaGL e _).trans ?_
    have := congrArg Units.val (det_invol (m := primaryMultiplicity (x : Module.End K V) (a : K[X]))
      (E := AdjoinRoot (a : K[X])) (by omega))
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  · rw [MonoidHom.comp_apply, ← map_mul, ← map_mul]
    exact congrArg _ (invol_commute_torusRep hm M r).eq
  · refine ⟨e ⟨0, by omega⟩, fun h => ?_⟩
    have h1 := congrArg (fun w => e.repr w ⟨1, by omega⟩) h
    simp only [iotaGL_entry, map_smul, Basis.repr_self, Finsupp.smul_apply] at h1
    have h2 := invol_apply_one_zero (m := primaryMultiplicity (x : Module.End K V) (a : K[X]))
      (E := AdjoinRoot (a : K[X])) (by omega)
    simp [h2, Fin.ext_iff] at h1

theorem exists_torus_paired {a : primaryFactors (x : Module.End K V)}
    (hP : PairedPrimaryBlock hK B x a)
    (hm : 5 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]))
    (M : Subgroup (AdjoinRoot (a : K[X]))ˣ) :
    ∃ (R : M × M × M →* LinearMap.GeneralLinearGroup K V) (u : LinearMap.GeneralLinearGroup K V),
      (∀ r, R r ∈ specialBlock B x (a : K[X])) ∧ u ∈ specialBlock B x (a : K[X]) ∧
      Function.Injective R ∧ u ^ 2 = 1 ∧ (∀ r, u * R r = R r * u) ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
  let e : Basis (Fin (primaryMultiplicity (x : Module.End K V) (a : K[X])))
      (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X])) :=
    Module.finBasis _ _
  obtain ⟨hdet, hinj, hsq, hudet, hcomm, hns⟩ := torus_data_blockGL a e hm M
  let φ' : orbitFactor B x (a : K[X]) ≃*
      (⊤ : Subgroup (blockGL (x : Module.End K V) (a : K[X]))) :=
    φ.trans Subgroup.topEquiv.symm
  exact exists_torus_of_iso a ⊤ φ' (fun g v hv => hφ g v hv) ((iotaGL e).comp (torusRep _ _ M))
    (fun r => Subgroup.mem_top _) hdet hinj _ (Subgroup.mem_top _) hsq hudet hcomm hns

theorem exists_torus_selfDual {a : primaryFactors (x : Module.End K V)}
    (hself : dualPoly hK.bar (a : K[X]) = a) (hS : SelfDualPrimaryBlock hK B x a)
    (hm : 5 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]))
    (M : Subgroup (AdjoinRoot (a : K[X]))ˣ)
    (hM : ∀ y ∈ M, ((y : (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) ^
      ((ℓ ^ f) ^ (a : K[X]).natDegree + 1) = 1) :
    ∃ (R : M × M × M →* LinearMap.GeneralLinearGroup K V) (u : LinearMap.GeneralLinearGroup K V),
      (∀ r, R r ∈ specialBlock B x (a : K[X])) ∧ u ∈ specialBlock B x (a : K[X]) ∧
      Function.Injective R ∧ u ^ 2 = 1 ∧ (∀ r, u * R r = R r * u) ∧
      ¬ ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent (x : Module.End K V) (a : K[X]),
        ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v : V) =
          ((c • v : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
  obtain ⟨hE, hbar, -, Hf, hHf, hHfl, -, ⟨e, he⟩, φ₀, hφ₀, -⟩ := hS.unitaryForm
  have hsupp : orbitFactor B x (a : K[X]) = supportedUnitary B x {(a : K[X])} :=
    orbitFactor_eq_supportedUnitary_of_selfDual hself
  let φ : orbitFactor B x (a : K[X]) ≃* sesqUnitaryGroup Hf :=
    (MulEquiv.subgroupCongr hsupp).trans φ₀
  have hφact : ∀ (g : orbitFactor B x (a : K[X])) (v : V)
      (hv : v ∈ primaryComponent (x : Module.End K V) (a : K[X])),
      blockApply (φ g : blockGL (x : Module.End K V) (a : K[X])) v hv =
        ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v :=
    fun g v hv => hφ₀ ((MulEquiv.subgroupCongr hsupp) g) v hv
  have hMn : ∀ y ∈ M, hE.bar ((y : (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) *
      ((y : (AdjoinRoot (a : K[X]))ˣ) : AdjoinRoot (a : K[X])) = 1 := by
    intro y hy
    rw [hbar, mul_comm, ← pow_succ']
    exact hM y hy
  obtain ⟨hdet, hinj, hsq, hudet, hcomm, hns⟩ := torus_data_blockGL a e hm M
  exact exists_torus_of_iso a (sesqUnitaryGroup Hf) φ hφact ((iotaGL e).comp (torusRep _ _ M))
    (fun r => iotaGL_mem_sesqUnitary e he _ (unitaryMat_torusRep hE.bar M hMn r)) hdet hinj _
    (iotaGL_mem_sesqUnitary e he _ (unitaryMat_invol hE.bar (by omega))) hsq hudet hcomm hns

end Abstract

end CFSG.RankThree.PartOne.FOC
