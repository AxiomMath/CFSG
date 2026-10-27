module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.KGNatSemi
public import CFSG.Quasithin.Vol2.KGNatSp4Flag

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace KA

variable {K : Type} [Field K]

theorem exists_matrix_of_semilinear [Finite K]
    {T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K)} (σ : K ≃+* K)
    (hσ : ∀ (c : K) (x : Fin 2 ⊕ Fin 2 → K), T (c • x) = σ c • T x)
    (hinj : Function.Injective T) :
    ∃ A : GL (Fin 2 ⊕ Fin 2) K, ∀ (g g' : GL (Fin 2 ⊕ Fin 2) K),
      (∀ x, T ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ T x) →
      A * Matrix.GeneralLinearGroup.map σ.toRingHom g * A⁻¹ = g' := by
  let L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    { toFun := fun x => T (σ.symm ∘ x)
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        funext i
        simp [map_add]
      map_smul' := fun c x => by
        have h1 : σ.symm ∘ (c • x) = σ.symm c • (σ.symm ∘ x) := by
          funext i
          simp [map_mul]
        change T (σ.symm ∘ (c • x)) = c • T (σ.symm ∘ x)
        rw [h1, hσ, RingEquiv.apply_symm_apply] }
  have hLx : ∀ x, L x = T (σ.symm ∘ x) := fun x => rfl
  have hLinj : Function.Injective L := fun x y h => by
    have h1 := hinj h
    funext i
    have := congrFun h1 i
    simpa using this
  have hLbij : Function.Bijective L := ⟨hLinj, Finite.surjective_of_injective hLinj⟩
  set A := Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.ofBijective L hLbij)) with hAdef
  have hA : ∀ v, (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = L v := fun v => by
    rw [hAdef, ← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin,
      MulEquiv.apply_symm_apply]
    rfl
  refine ⟨A, fun g g' hg => ?_⟩
  have hAinv : ∀ v, ((A⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ L v = v := fun v => by
    rw [← hA, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hmap : ∀ y : Fin 2 ⊕ Fin 2 → K,
      σ.symm ∘ (((Matrix.GeneralLinearGroup.map σ.toRingHom g : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ y) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ (σ.symm ∘ y) := fun y => by
    funext i
    simp [Matrix.mulVec, dotProduct]
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := hLbij.2 x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAinv, hA, hLx, hLx, hmap]
  exact hg _

end KA

theorem factNoGraphSp4_holds : Ch11.SecA.FactNoGraphSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ _ Tb hTbH hTbZ t ht
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have htZ : ∀ z ∈ Z, t z ∈ Z := fun z hz => (hTbZ t ht z).mp hz
  have htZ' : ∀ z ∈ Z, t⁻¹ z ∈ Z := fun z hz => by
    have h1 := (hTbZ t ht (t⁻¹ z)).mpr
    rw [MulAut.apply_inv_self] at h1
    exact h1 hz
  have htH' : ∀ h ∈ H, t⁻¹ * h * t ∈ H := fun h hh => by
    have h1 := hTbH t⁻¹ (Tb.inv_mem ht) h hh
    rwa [inv_inv] at h1
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨σ₀, hσ₀⟩ := hf.exists_semilinear (fun T hT => commutant_statedSp T hT) he0 t htZ
    htZ' htH'
  obtain ⟨T, hTf, hσ⟩ : ∃ T : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K),
      (∀ w, T (f w) = f (t w)) ∧ ∀ (c : K) x, T (c • x) = σ₀ c • T x :=
    ⟨hf.autMap t htZ, hf.autMap_apply _ _, hσ₀⟩
  have hTinj : Function.Injective T := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := hf.surj x
    obtain ⟨b, rfl⟩ := hf.surj y
    rw [hTf, hTf, hf.eq_iff] at hxy
    rw [hf.eq_iff]
    have := htZ' _ hxy
    rwa [← map_inv, ← map_mul, MulAut.inv_apply_self] at this
  set σ : K ≃+* K := RingEquiv.ofBijective σ₀
    ⟨σ₀.injective, Finite.surjective_of_injective σ₀.injective⟩
  obtain ⟨A, hA⟩ := KA.exists_matrix_of_semilinear σ (fun c x => hσ c x) hTinj
  have key : ∀ γ : ↥(StatedSp 2 K), ∃ γ' : ↥(StatedSp 2 K),
      A * Matrix.GeneralLinearGroup.map σ.toRingHom (γ : GL (Fin 2 ⊕ Fin 2) K) * A⁻¹ = γ' ∧
        ((π γ' : ↥H) : MulAut W) = t * ((π γ : ↥H) : MulAut W) * t⁻¹ := by
    intro γ
    obtain ⟨γ', hγ'⟩ : ∃ γ' : ↥(StatedSp 2 K), π γ' = ⟨_, hTbH t ht _ (π γ).2⟩ := hf.onto _
    refine ⟨γ', hA _ _ fun x => ?_, by rw [hγ']⟩
    obtain ⟨w, rfl⟩ := hf.surj x
    have e : t (((π γ : ↥H) : MulAut W) w) = ((π γ' : ↥H) : MulAut W) (t w) := by
      rw [hγ']
      simp [MulAut.mul_apply]
    show T (mat 2 K γ *ᵥ f w) = mat 2 K γ' *ᵥ T (f w)
    rw [← hf.act4, hTf, hTf, e, hf.act4]
  refine ⟨A, σ, fun γ => ?_, fun γ h => ?_⟩
  · obtain ⟨γ', h1, -⟩ := key γ
    rw [h1]
    exact γ'.2
  · obtain ⟨γ', h1, h2⟩ := key γ
    have h3 : (⟨_, h⟩ : ↥(StatedSp 2 K)) = γ' := Subtype.ext h1
    rw [h3, h2]

end CFSG.Quasithin.Vol2.KGNat
