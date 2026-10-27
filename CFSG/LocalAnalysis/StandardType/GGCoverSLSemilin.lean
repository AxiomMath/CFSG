module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLPSL
public import CFSG.LocalAnalysis.StandardType.GGL45TALinLift
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem exists_comp_eq_of_model_SL {d : ℕ} {K : Type} [Field K] [CharP K 2]
    (hd : 3 ≤ d)
    {φ : SpecialLinearGroup (Fin d) K →* projectiveSL d K} (hφs : Function.Surjective φ)
    (hφk : ∀ g, φ g = 1 → g ∈ scalars d K) :
    ∃ α₀ : MulAut (projectiveSL d K), ∀ x, φ x = α₀ (proj d K x) := by
  have hZ : Subgroup.center (projectiveSL d K) = ⊥ :=
    SlNsRootGen.center_projectiveSL_eq_bot_charTwo
  have hkerπ : (proj d K).ker = scalars d K := by
    ext x
    rw [MonoidHom.mem_ker, proj_eq_one_iff]
  have hle_phi_pi : φ.ker ≤ (proj d K).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hc : x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) :=
      scalars_le_center d K (hφk x hx)
    have hcent : proj d K x ∈ Subgroup.center (projectiveSL d K) :=
      Subgroup.map_center_le_center (f := proj d K) (proj_surjective d K) ⟨x, hc, rfl⟩
    rwa [hZ, Subgroup.mem_bot] at hcent
  have hle_pi_phi : (proj d K).ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxscal : x ∈ scalars d K := hkerπ ▸ hx
    have hc : x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := scalars_le_center d K hxscal
    have hcent : φ x ∈ Subgroup.center (projectiveSL d K) :=
      Subgroup.map_center_le_center (f := φ) hφs ⟨x, hc, rfl⟩
    rwa [hZ, Subgroup.mem_bot] at hcent
  let eπ : (SpecialLinearGroup (Fin d) K ⧸ (proj d K).ker) ≃* projectiveSL d K :=
    QuotientGroup.liftEquiv (N := (proj d K).ker) (φ := proj d K) (proj_surjective d K) rfl
  have heπ : ∀ x, eπ (QuotientGroup.mk' (proj d K).ker x) = proj d K x :=
    fun x => QuotientGroup.liftEquiv_mk (N := (proj d K).ker) (φ := proj d K)
      (proj_surjective d K) rfl x
  let ψ : (SpecialLinearGroup (Fin d) K ⧸ (proj d K).ker) →* projectiveSL d K :=
    QuotientGroup.lift (proj d K).ker φ hle_pi_phi
  have hψ' : ∀ x, ψ (QuotientGroup.mk' (proj d K).ker x) = φ x :=
    fun x => QuotientGroup.lift_mk' (N := (proj d K).ker) (φ := φ) hle_pi_phi x
  have hψsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨x, rfl⟩ := hφs r
    exact ⟨QuotientGroup.mk' (proj d K).ker x, hψ' x⟩
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proj d K).ker r
    rw [Subgroup.mem_bot]
    have hx : φ x = 1 := by rw [← hψ' x, hr]
    exact (QuotientGroup.eq_one_iff x).mpr (hle_phi_pi (MonoidHom.mem_ker.mpr hx))
  refine ⟨eπ.symm.trans (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩), fun x => ?_⟩
  change φ x = (eπ.symm.trans (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩)) (proj d K x)
  rw [MulEquiv.trans_apply]
  change φ x = ψ (eπ.symm (proj d K x))
  rw [← heπ x, MulEquiv.symm_apply_apply, hψ' x]

theorem exists_semilin_through_model_SL {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2)
    {φ : SpecialLinearGroup (Fin d) K →* projectiveSL d K} (hφs : Function.Surjective φ)
    (hφk : ∀ g, φ g = 1 → g ∈ scalars d K)
    {a : MulAut (projectiveSL d K)} (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    ∃ (g : GL (Fin d) K) (σ : K ≃+* K) (m : ℕ), σ ^ p ^ m = 1 ∧
      ∀ x y : SpecialLinearGroup (Fin d) K,
        SpecialLinearGroup.toGL y =
          g * Matrix.GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL x) * g⁻¹ →
        a (φ x) = φ y := by
  obtain ⟨α₀, hα₀⟩ := exists_comp_eq_of_model_SL hd hφs hφk
  set E' : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) ≃*
      MulAut (projectiveSL d K) := MulAut.congr (TypeA.recipeEquiv d K) with hE'
  let a₁ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    E'.symm (MulAut.conj α₀.symm a)
  obtain ⟨k, hk⟩ := ha
  have ha₁ : GGL45IsPElt p a₁ := by
    refine ⟨k, ?_⟩
    exact E'.injective (by
      rw [map_pow, MulEquiv.apply_symm_apply, map_one]
      have h1 := map_pow (MulAut.conj α₀.symm) a (p ^ k)
      rw [hk, map_one] at h1
      exact h1.symm)
  obtain ⟨g, σ, m, hσ, hsem⟩ :=
    GGL45TA.exists_semilin_of_pElt (k := K) (d := d) hd hp hp2 (α := a₁) ha₁
  refine ⟨g, σ, m, hσ, ?_⟩
  intro x y hy
  let hx : LargeEvenSLGroup (Fin d) K := (TypeA.slKerEquiv d K).symm x
  let hy' : LargeEvenSLGroup (Fin d) K := (TypeA.slKerEquiv d K).symm y
  have hcoe_x : (hx : GL (Fin d) K) = SpecialLinearGroup.toGL x := rfl
  have hcoe_y : (hy' : GL (Fin d) K) = SpecialLinearGroup.toGL y := rfl
  have hxy : (hy' : GL (Fin d) K) =
      g * Matrix.GeneralLinearGroup.map σ.toRingHom (hx : GL (Fin d) K) * g⁻¹ := by
    rw [hcoe_y, hcoe_x]
    exact hy
  have hsemxy : a₁ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hx) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hy' := hsem hx hy' hxy
  have hproj_x : proj d K x = TypeA.recipeEquiv d K
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hx) := by
    have hx' : TypeA.slKerEquiv d K hx = x := MulEquiv.apply_symm_apply _ _
    rw [← hx', TypeA.recipeEquiv_mk]
  have hproj_y : proj d K y = TypeA.recipeEquiv d K
      (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hy') := by
    have hy'' : TypeA.slKerEquiv d K hy' = y := MulEquiv.apply_symm_apply _ _
    rw [← hy'', TypeA.recipeEquiv_mk]
  have hEa : E' a₁ = MulAut.conj α₀.symm a := MulEquiv.apply_symm_apply E' _
  have key : ∀ z : projectiveSL d K,
      a (α₀ z) = α₀ (TypeA.recipeEquiv d K (a₁ ((TypeA.recipeEquiv d K).symm z))) := by
    intro z
    have h := DFunLike.congr_fun hEa z
    have h2 : (E' a₁) z =
        TypeA.recipeEquiv d K (a₁ ((TypeA.recipeEquiv d K).symm z)) := by
      rw [hE', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
    rw [h2] at h
    rw [h]
    show a (α₀ z) = α₀ ((MulAut.conj α₀.symm a) z)
    rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_def,
      MulEquiv.symm_symm, MulEquiv.apply_symm_apply]
  have keyx := key (TypeA.recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hx))
  rw [MulEquiv.symm_apply_apply] at keyx
  calc a (φ x) = a (α₀ (proj d K x)) := by rw [hα₀ x]
    _ = a (α₀ (TypeA.recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hx))) := by
          rw [hproj_x]
    _ = α₀ (TypeA.recipeEquiv d K (a₁ (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hx))) := keyx
    _ = α₀ (TypeA.recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) hy')) := by
          rw [hsemxy]
    _ = α₀ (proj d K y) := by rw [hproj_y]
    _ = φ y := (hα₀ y).symm

end CFSG.StandardType
