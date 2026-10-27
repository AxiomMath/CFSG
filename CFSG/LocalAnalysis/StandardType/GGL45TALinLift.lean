module

public import CFSG.LocalAnalysis.StandardType.GGL45TALinH123
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover

public section

namespace CFSG.StandardType.GGL45TA

open CFSG CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {d : ℕ} {k : Type} [Field k]

theorem exists_cover_linear [Finite k] (hd : 3 ≤ d) (hk8 : 8 ≤ Nat.card k) {K : Type} [Group K]
    (hK : commutator K = ⊤)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) k)) :
    ∃ π : LargeEvenSLGroup (Fin d) k →* K, Function.Surjective π ∧
      (∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) ∧
      ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk _ h := by
  let ψ' : K →* projectiveSL d k := (TypeA.recipeEquiv d k).toMonoidHom.comp
    (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
  have hψs : Function.Surjective ψ' := by
    intro x
    obtain ⟨r, rfl⟩ := (TypeA.recipeEquiv d k).surjective x
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
    exact ⟨y, rfl⟩
  have hker : ψ'.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : θ (QuotientGroup.mk' (Subgroup.center K) x) = 1 :=
      (TypeA.recipeEquiv d k).injective (by rw [map_one]; exact hx)
    have h2 : QuotientGroup.mk' (Subgroup.center K) x = 1 := θ.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hsec := TypeA.slHasSections_of_card (K := k) hd (by omega) (by omega) (by omega)
  obtain ⟨φ, hφs, hφ⟩ := TypeA.exists_sl_cover hsec ψ' hψs hker hK
  let π : LargeEvenSLGroup (Fin d) k →* K := φ.comp (TypeA.slKerEquiv d k).toMonoidHom
  have hcompat : ∀ h, θ (π h : K ⧸ Subgroup.center K) = LargeEvenProjMk _ h := by
    intro h
    apply (TypeA.recipeEquiv d k).injective
    rw [TypeA.recipeEquiv_mk]
    exact hφ _
  refine ⟨π, hφs.comp (TypeA.slKerEquiv d k).surjective, fun h hh => ?_, hcompat⟩
  apply projMk_ker_le h
  rw [MonoidHom.mem_ker, ← hcompat, MonoidHom.mem_ker.mp hh]
  simp

@[expose] noncomputable def semiSL (g : GL (Fin d) k) (σ : k ≃+* k) :
    LargeEvenSLGroup (Fin d) k →* LargeEvenSLGroup (Fin d) k where
  toFun h := ⟨semi g σ h, conj_mem_sl g (map_mem_sl σ h.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul])

theorem coe_semiSL (g : GL (Fin d) k) (σ : k ≃+* k) (h : LargeEvenSLGroup (Fin d) k) :
    ((semiSL g σ h : LargeEvenSLGroup (Fin d) k) : GL (Fin d) k) = semi g σ h := rfl

theorem semilinImpl_of_mod_center (hd : 3 ≤ d) {K : Type} [Group K]
    {π : LargeEvenSLGroup (Fin d) k →* K} {α : MulAut K} {g : GL (Fin d) k} {σ : k ≃+* k}
    (h : ∀ y : LargeEvenSLGroup (Fin d) k,
      ((α (π y))⁻¹ * π (semiSL g σ y)) ∈ Subgroup.center K) : SemilinImpl π α g σ := by
  haveI hperf : Group.IsPerfect (LargeEvenSLGroup (Fin d) k) :=
    (Subgroup.isPerfect_iff (H := LargeEvenSLGroup (Fin d) k)).mpr
      (LinearFieldFix.commutator_slGroup hd)
  let χ : LargeEvenSLGroup (Fin d) k →* K :=
    { toFun := fun y => (α (π y))⁻¹ * π (semiSL g σ y)
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_center_iff.mp (h a)
        simp only [map_mul, _root_.mul_inv_rev]
        calc (α (π b))⁻¹ * (α (π a))⁻¹ * (π (semiSL g σ a) * π (semiSL g σ b))
            = (α (π b))⁻¹ * ((α (π a))⁻¹ * π (semiSL g σ a)) * π (semiSL g σ b) := by group
          _ = (α (π b))⁻¹ * (α (π b) * ((α (π a))⁻¹ * π (semiSL g σ a))) *
                (α (π b))⁻¹ * π (semiSL g σ b) := by
              rw [hb (α (π b))]; group
          _ = (α (π a))⁻¹ * π (semiSL g σ a) * ((α (π b))⁻¹ * π (semiSL g σ b)) := by group }
  have hχ : ∀ y, χ y = 1 := by
    intro y
    have hy : y ∈ commutator (LargeEvenSLGroup (Fin d) k) := Group.IsPerfect.mem_commutator
    have hle : commutator (LargeEvenSLGroup (Fin d) k) ≤ χ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hca := Subgroup.mem_center_iff.mp (h a)
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hca (χ b)).symm
    exact hle hy
  intro y y' hy'
  have h1 : (α (π y))⁻¹ * π (semiSL g σ y) = 1 := hχ y
  have h2 : semiSL g σ y = y' := Subtype.ext (by rw [coe_semiSL, semi_apply, hy'])
  rw [h2] at h1
  exact (inv_mul_eq_one.mp h1)

theorem exists_implements_lift {K : Type} [Group K] {π : LargeEvenSLGroup (Fin d) k →* K}
    (hπ : Function.Surjective π)
    (hker : ∀ h ∈ π.ker, (h : GL (Fin d) k) ∈ LargeEvenScalars (Fin d) k) (A : GL (Fin d) k) :
    ∃ u : MulAut K, Implements π u A := by
  let c : LargeEvenSLGroup (Fin d) k ≃* LargeEvenSLGroup (Fin d) k :=
    { toFun := conjSL A
      invFun := conjSL A⁻¹
      left_inv := fun h => Subtype.ext (by simp only [coe_conjSL]; group)
      right_inv := fun h => Subtype.ext (by simp only [coe_conjSL]; group)
      map_mul' := (conjSL A).map_mul }
  have hfix : ∀ z ∈ π.ker, c z = z := by
    intro z hz
    apply Subtype.ext
    change A * (z : GL (Fin d) k) * A⁻¹ = z
    have hc := Subgroup.mem_center_iff.mp (scalar_mem_center (hker z hz))
    rw [hc A, mul_inv_cancel_right]
  have hN : π.ker.map (c : LargeEvenSLGroup (Fin d) k →* LargeEvenSLGroup (Fin d) k) = π.ker := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change c w ∈ π.ker
      rw [hfix w hw]; exact hw
    · intro hz
      exact ⟨z, hz, hfix z hz⟩
  let e₀ := QuotientGroup.quotientKerEquivOfSurjective π hπ
  let u : MulAut K := e₀.symm.trans ((QuotientGroup.congr π.ker π.ker c hN).trans e₀)
  refine ⟨u, fun h h' hh' => ?_⟩
  have he₀ : ∀ y, e₀ (QuotientGroup.mk y) = π y := fun y => rfl
  have h1 : e₀.symm (π h) = QuotientGroup.mk h := by rw [MulEquiv.symm_apply_eq, he₀]
  have h2 : c h = h' := Subtype.ext (by rw [hh']; rfl)
  change e₀ (QuotientGroup.congr π.ker π.ker c hN (e₀.symm (π h))) = π h'
  rw [h1, QuotientGroup.congr_mk, he₀, h2]

theorem exists_conjAut_fieldAut_pow (A : GL (Fin d) k) (σ : k ≃+* k) (n : ℕ) :
    ∃ B : GL (Fin d) k, (conjAut d k A * fieldAut d k σ) ^ n = conjAut d k B * fieldAut d k (σ ^ n) := by
  induction n with
  | zero => exact ⟨1, by rw [pow_zero, pow_zero, map_one, map_one, one_mul]⟩
  | succ n ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨B * GeneralLinearGroup.map ((σ ^ n : k ≃+* k) : k →+* k) A, ?_⟩
    rw [pow_succ, hB, pow_succ, map_mul, map_mul]
    calc conjAut d k B * fieldAut d k (σ ^ n) * (conjAut d k A * fieldAut d k σ)
        = conjAut d k B * (fieldAut d k (σ ^ n) * conjAut d k A) * fieldAut d k σ := by group
      _ = conjAut d k B * (conjAut d k (GeneralLinearGroup.map ((σ ^ n : k ≃+* k) : k →+* k) A) *
            fieldAut d k (σ ^ n)) * fieldAut d k σ := by rw [fieldAut_mul_conjAut]
      _ = _ := by group

theorem exists_semilin_of_pElt [Finite k] (hd : 3 ≤ d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) k))} (hα : GGL45IsPElt p α) :
    ∃ (g : GL (Fin d) k) (σ : k ≃+* k) (m : ℕ), σ ^ p ^ m = 1 ∧
      SemilinImpl (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) α g σ := by
  obtain ⟨a, ha⟩ := hα
  set E' := MulAut.congr (TypeA.recipeEquiv d k) with hE'
  set S' : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) k))) :=
    (semilinearAutGroup d k).comap E'.toMonoidHom with hS'
  have hJS : RecipeFieldLinear.recI d k ≤ S' := fun φ hφ => linearAutGroup_le_semilinearAutGroup hφ
  have hFS : LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) k)) ⊆ S' := by
    intro f hf
    obtain ⟨σ, hσ⟩ := RecipeFieldLinear.congr_field_eq hf
    change E' f ∈ semilinearAutGroup d k
    rw [hσ]
    exact fieldAut_mem_semilinearAutGroup σ
  have hodd : Odd (p ^ a) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨u, hu, f, hf, rfl⟩ := NbrGraphLinear.ggOddAutInnField_linear (K := k) (by omega) hodd _ ha
  have hmem : E' (u * f) ∈ semilinearAutGroup d k := by
    rw [← RecipeFieldLinear.coe_recI] at hu
    exact S'.mul_mem (hJS hu) ((Subgroup.closure_le S').mpr hFS hf)
  obtain ⟨A, σ, hAσ⟩ := mem_semilinearAutGroup_iff.mp hmem
  refine ⟨A, σ, a, ?_, fun h h' hh' => ?_⟩
  · obtain ⟨B, hB⟩ := exists_conjAut_fieldAut_pow A σ (p ^ a)
    have h1 : (conjAut d k A * fieldAut d k σ) ^ p ^ a = 1 := by
      rw [← hAσ, ← map_pow, ha, map_one]
    rw [hB] at h1
    exact (eq_one_of_conjAut_mul_fieldAut_eq_one hd B (σ ^ p ^ a) h1).1
  · apply (TypeA.recipeEquiv d k).injective
    have h1 : TypeA.recipeEquiv d k ((u * f) (LargeEvenProjMk _ h)) =
        E' (u * f) (TypeA.recipeEquiv d k (LargeEvenProjMk _ h)) := by
      rw [hE', MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulEquiv.trans_apply]
    rw [h1, hAσ, TypeA.recipeEquiv_mk, TypeA.recipeEquiv_mk, MulAut.mul_apply, fieldAut_proj,
      conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, TypeA.coe_slKerEquiv, hh']
    simp only [SpecialLinearGroup.map_apply_coe, TypeA.coe_slKerEquiv, semi_apply, Units.val_mul]
    rfl

end CFSG.StandardType.GGL45TA
