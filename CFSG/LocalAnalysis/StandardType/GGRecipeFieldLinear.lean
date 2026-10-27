module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  Matrix

namespace RecipeFieldLinear

variable {d : ℕ} {K : Type} [Field K]

theorem congr_field_eq {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) :
    ∃ σ : K ≃+* K, MulAut.congr (TypeA.recipeEquiv d K) φ = fieldAut d K σ := by
  obtain ⟨σ, hσ⟩ := hφ
  refine ⟨σ, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective d K x
  set h : LargeEvenSLGroup (Fin d) K := (TypeA.slKerEquiv d K).symm g with hh
  set h' : LargeEvenSLGroup (Fin d) K :=
    (TypeA.slKerEquiv d K).symm (SpecialLinearGroup.map σ.toRingHom g) with hh'
  have hrel : ((h' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((h : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map σ := by
    rw [← TypeA.coe_slKerEquiv, ← TypeA.coe_slKerEquiv, hh, hh', MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, SpecialLinearGroup.map_apply_coe]
    rfl
  have h1 := hσ h h' hrel
  have hg : proj d K g = TypeA.recipeEquiv d K (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h) := by
    rw [TypeA.recipeEquiv_mk, hh, MulEquiv.apply_symm_apply]
  have hL : MulAut.congr (TypeA.recipeEquiv d K) φ (proj d K g) =
      proj d K (SpecialLinearGroup.map σ.toRingHom g) := by
    rw [MulAut.congr_apply, hg, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.trans_apply, h1, TypeA.recipeEquiv_mk, hh', MulEquiv.apply_symm_apply]
  rw [hL, fieldAut_proj]

variable (d K) in
@[expose] noncomputable def recI : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :=
  (linearAutGroup d K).comap (MulAut.congr (TypeA.recipeEquiv d K)).toMonoidHom

theorem mem_recI_iff {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} :
    φ ∈ recI d K ↔ MulAut.congr (TypeA.recipeEquiv d K) φ ∈ linearAutGroup d K :=
  Iff.rfl

theorem coe_recI : (recI d K : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))) =
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ := by
  ext φ
  rw [SetLike.mem_coe, mem_recI_iff, mem_linearAutGroup_iff]
  constructor
  · rintro ⟨A, hA⟩
    have h := NbrGraphLinear.symm_congr_conjAut_mem (K := K) A
    rwa [hA, MulEquiv.symm_apply_apply] at h
  · intro hφ
    exact TypeA.congr_recipeEquiv_mem hφ

theorem conj_mem_recI (r : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    MulAut.conj r ∈ recI d K := by
  rw [mem_recI_iff, mulAut_congr_conj]
  obtain ⟨g, hg⟩ := proj_surjective d K (TypeA.recipeEquiv d K r)
  rw [← hg, ← conjAut_toGL]
  exact conjAut_mem_linearAutGroup _

open CFSG.ComponentClassification in
theorem eq_one_of_conjAut_mul_fieldAut_eq_one' [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hpar : 3 ≤ n ∨ 4 ≤ Nat.card K) (B : GL (Fin n) K) (τ : K ≃+* K)
    (h : conjAut n K B * fieldAut n K τ = 1) :
    τ = 1 ∧ ∃ c : Kˣ, GeneralLinearGroup.scalar (Fin n) c = B := by
  have hsl : ∀ g : SpecialLinearGroup (Fin n) K,
      proj n K (CatalogueBLinearSemilinear.slSemilinearAction n K B τ g) = proj n K g := by
    intro g
    have := congrArg (fun φ : MulAut (projectiveSL n K) => φ (proj n K g)) h
    simp only [MulAut.one_apply] at this
    rw [← this]
    rfl
  have hpsl : CatalogueBLinearSemilinear.semilinearAction n K B τ = 1 := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (SpecialLinearGroup (Fin n) K)) x
    rw [CatalogueBLinearSemilinear.semilinearAction_mk, MulAut.one_apply]
    have h1 := hsl g
    rw [proj_eq_proj_iff, scalars_eq_center] at h1
    exact QuotientGroup.eq.mpr h1
  exact (CatalogueBLinearSemilinear.semilinearAction_eq_one_iff n K hn hpar B τ).mp hpsl

theorem eq_one_of_mem_field_of_mem_conj [Finite K] (hd : 2 ≤ d) (hpar : 3 ≤ d ∨ 4 ≤ Nat.card K)
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)))
    (hfI : f ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) :
    f = 1 := by
  obtain ⟨σ, hσ⟩ := congr_field_eq hf
  obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hfI
  have h : conjAut d K A⁻¹ * fieldAut d K σ = 1 := by
    rw [map_inv, ← hσ, ← hA, inv_mul_cancel]
  obtain ⟨rfl, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one' hd hpar _ _ h
  apply (MulAut.congr (TypeA.recipeEquiv d K)).injective
  rw [hσ, map_one, map_one]

theorem ggRawInnField_linear [Finite K] (hd : 2 ≤ d) (hpar : 3 ≤ d ∨ 4 ≤ Nat.card K) {p : ℕ}
    (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) :=
  ggRawInnField_of_subgroup hp (recI d K) coe_recI conj_mem_recI
    fun _ hf hfI => eq_one_of_mem_field_of_mem_conj hd hpar hf hfI

theorem commutator_mem_linearAutGroup [Finite K] (hd : 3 ≤ d) (α β : MulAut (projectiveSL d K)) :
    α * β * α⁻¹ * β⁻¹ ∈ linearAutGroup d K :=
  OuterDerived.commutator_mem_linearAutGroup hd α β

theorem commutator_mem_recI [Finite K] (hd : 3 ≤ d)
    (α β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :
    α * β * α⁻¹ * β⁻¹ ∈ recI d K := by
  rw [mem_recI_iff, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutator_mem_linearAutGroup hd _ _

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo in
theorem commutator_mem_conjImage_two [Finite K]
    (α β : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 2) K))) :
    α * β * α⁻¹ * β⁻¹ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ := by
  set c := MulAut.congr (NbrGraphLinear.recipeEquivTwo K) with hc
  obtain ⟨x, hx⟩ := semilinearAction_surjective K (c α)
  obtain ⟨y, hy⟩ := semilinearAction_surjective K (c β)
  set z := x * y * x⁻¹ * y⁻¹ with hz
  have hzr : z.right = 1 := by
    change SemidirectProduct.rightHom z = 1
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv,
      ringEquiv_mul_comm_of_finite (SemidirectProduct.rightHom x)]
    group
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective z.left
  have hzA : semilinearAction K z = pglAction K (Matrix.ProjGenLinGroup.mk A) := by
    rw [← SemidirectProduct.inl_left_mul_inr_right z, hzr, map_one, mul_one, semilinearAction_inl,
      hA]
  have e : α * β * α⁻¹ * β⁻¹ = c.symm (pglAction K (Matrix.ProjGenLinGroup.mk A)) := by
    rw [← hzA, MulEquiv.eq_symm_apply, hz]
    simp only [map_mul, map_inv, hx, hy]
  rw [e]
  exact NbrGraphLinear.symm_congr_pglAction_mem A

theorem ggRawFieldCentral_linear [Finite K] (hd : 2 ≤ d) :
    GGRawFieldCentral (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl : d = 2 := by omega
    exact ggRawFieldCentral_of_commutator_mem commutator_mem_conjImage_two
  · rw [← coe_recI]
    exact ggRawFieldCentral_of_commutator_mem fun α β => commutator_mem_recI h α β

end RecipeFieldLinear

open RecipeFieldLinear

theorem three_le_or_four_le_of_typeA {l n : ℕ} (hl1 : 1 ≤ l) (hl2 : l = 1 → 2 ≤ n) {K : Type}
    (hK : Nat.card K = 2 ^ n) : 3 ≤ l + 1 ∨ 4 ≤ Nat.card K := by
  rcases Nat.lt_or_ge l 2 with h | h
  · right
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (hl2 (by omega))
  · left
    omega

theorem four_le_card_of_sq {n : ℕ} (hn : 1 ≤ n) {K : Type} (hK : Nat.card K = (2 ^ n) ^ 2) :
    4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = (2 ^ 1) ^ 2 := by norm_num
    _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hn) 2

theorem ggRawInnFieldOn_linear : GGRawInnFieldOn GGLinearRecipeLabel := by
  intro p hp _ lab hlab hS Q₀ h
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · obtain ⟨hl1, hl2⟩ : 1 ≤ l ∧ (l = 1 → 2 ≤ n) := hlab.2
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) h
    exact ggRawInnField_linear (by omega) (three_le_or_four_le_of_typeA hl1 hl2 hK) hp1
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ?_) h
    exact ggRawInnField_linear (by omega) (Or.inl (by omega)) hp1
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    refine NbrGraphLinear.recipeLinear_all (fun K _ _ hK => ?_) h
    exact ggRawInnField_linear le_rfl (Or.inr (four_le_card_of_sq hlab.1 hK)) hp1

theorem ggRawFieldCentralOn_linear : GGRawFieldCentralOn GGLinearRecipeLabel := by
  intro lab hlab hS Q₀ h
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · have hl1 : 1 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ggRawFieldCentral_linear (by omega)) h
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ggRawFieldCentral_linear (by omega)) h
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ggRawFieldCentral_linear le_rfl) h

end CFSG.StandardType

end
