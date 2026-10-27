module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAssembly3
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeHerm
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAlt
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs

public section

namespace CFSG.StandardType.A6Red

open Matrix LayerCores
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

private theorem mem_unitaryOf_gramAdj_iff_bilin {K : Type} [Field K] {W : Type} [AddCommGroup W]
    [Module K W] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K W)
    {B : BilinForm K W} {M : Matrix ι ι K} (hM : M = LinearMap.BilinForm.toMatrix b B)
    (hMd : IsUnit M.det) (hMt : Mᵀ = M) (g : W ≃ₗ[K] W) :
    LayerCores.matEquiv b g ∈ LayerCores.unitaryOf (LayerCores.isInvol_gramAdj hMd hMt) ↔
      ∀ x y, B (g x) (g y) = B x y := by
  rw [LayerCores.mem_unitaryOf]
  have hcomp : (LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
      (LayerCores.matEquiv b g : Matrix ι ι K) =
      LinearMap.BilinForm.toMatrix b
        (LinearMap.BilinForm.comp B (g : W →ₗ[K] W) (g : W →ₗ[K] W)) := by
    rw [hM, LayerCores.coe_matEquiv, LinearMap.BilinForm.toMatrix_comp b b]
  have h1 : LayerCores.gramAdj M (LayerCores.matEquiv b g : Matrix ι ι K) *
        (LayerCores.matEquiv b g : Matrix ι ι K) = 1 ↔
      (LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
        (LayerCores.matEquiv b g : Matrix ι ι K) = M := by
    rw [LayerCores.gramAdj]
    constructor
    · intro h
      have h' : M⁻¹ * ((LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
          (LayerCores.matEquiv b g : Matrix ι ι K)) = 1 := by
        rw [← h]
        simp only [Matrix.mul_assoc]
      calc (LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
            (LayerCores.matEquiv b g : Matrix ι ι K)
          = M * (M⁻¹ * ((LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
              (LayerCores.matEquiv b g : Matrix ι ι K))) := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv M hMd, Matrix.one_mul]
        _ = M := by rw [h', Matrix.mul_one]
    · intro h
      calc M⁻¹ * (LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
            (LayerCores.matEquiv b g : Matrix ι ι K)
          = M⁻¹ * ((LayerCores.matEquiv b g : Matrix ι ι K)ᵀ * M *
              (LayerCores.matEquiv b g : Matrix ι ι K)) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h, Matrix.nonsing_inv_mul M hMd]
  rw [h1, hcomp, hM, (LinearMap.BilinForm.toMatrix b).injective.eq_iff]
  constructor
  · intro h x y
    have := LinearMap.congr_fun₂ h x y
    simpa [LinearMap.BilinForm.comp_apply] using this
  · intro h
    refine LinearMap.ext₂ fun x y => ?_
    simpa [LinearMap.BilinForm.comp_apply] using h x y

theorem ggA6_sp_freeShape_abs {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [Finite F] [CharP F 2] [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) (hAB : A ≤ TauCeti.BilinForm.isometryGroup B) (hodd : Odd (Nat.card A))
    (hnil : Group.IsNilpotent ↥A) (hfree : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    {J : Subgroup (V ≃ₗ[F] V)}
    (hJ : IsComponentOf J (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (A : Set (V ≃ₗ[F] V)))) : GGA6CharTwoLie ↥J := by
  classical
  have := finite_linearEquiv (K := F) (V := V)
  have : Fintype A := Fintype.ofFinite A
  set b := Module.finBasis F V with hb
  set M := LinearMap.BilinForm.toMatrix b B with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, ← hB.neg_eq (b i) (b j), CharTwo.neg_eq]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply]
    exact hB.self_eq_zero (b i)
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff_bilin b hM hMd hMt
  set A' := A.map (matEquiv b).toMonoidHom with hA'
  have hA'U : A' ≤ unitaryOf hadj := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hU a).mpr (TauCeti.BilinForm.mem_isometryGroup_iff.mp (hAB ha))
  have hcard : (Nat.card A' : F) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective (matEquiv b).toMonoidHom
      (matEquiv b).injective).toEquiv.symm]
    exact natCast_card_ne_zero_of_odd hodd
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M) hA'U hcard hY₀
  have hAn' : Group.IsNilpotent ↥A' :=
    Group.nilpotent_of_mulEquiv
      ((A.equivMapOfInjective (matEquiv b).toMonoidHom (matEquiv b).injective).trans
        (MulEquiv.subgroupCongr hA'.symm))
  have hfree' : ∀ w : Fin (Module.finrank F V) → F,
      (∀ g ∈ A', (g : Matrix (Fin (Module.finrank F V)) (Fin (Module.finrank F V)) F).mulVec w = w) →
      w = 0 := by
    intro w hw
    set v : V := b.equivFun.symm w with hv
    have hvrepr : b.equivFun v = w := by rw [hv, LinearEquiv.apply_symm_apply]
    have hfix : ∀ a ∈ A, a v = v := by
      intro a ha
      change (a : V →ₗ[F] V) v = v
      have hmem : matEquiv b a ∈ A' := ⟨a, ha, rfl⟩
      have h1 := hw (matEquiv b a) hmem
      rw [coe_matEquiv] at h1
      have h2 := LinearMap.toMatrix_mulVec_repr b b (a : V →ₗ[F] V) v
      rw [← Module.Basis.equivFun_apply b v,
        ← Module.Basis.equivFun_apply b ((a : V →ₗ[F] V) v)] at h2
      rw [hvrepr, h1] at h2
      apply b.equivFun.injective
      rw [h2.symm, hvrepr]
    have h0 := hfree v hfix
    rw [h0, map_zero] at hvrepr
    exact hvrepr.symm
  obtain ⟨β, S, hS, hshape⟩ := CoreShape.exists_coreFamily_adjCent_lie
    CoreShape.hermCoreInputLie_holds CoreShape.altCoreInputLie_holds hcard hadj
    (fun X hX g hg => hadj.mul_comm_of_le_unitaryOf hA'U hX hg) ⟨Y, hYc, hY⟩
    (Or.inr ⟨hAn', hfree'⟩)
  have hcent : ∀ g : V ≃ₗ[F] V,
      ((matEquiv b).toMonoidHom g ∈
          Subgroup.centralizer (A' : Set (GL (Fin (Module.finrank F V)) F)) ↔
        g ∈ Subgroup.centralizer (A : Set (V ≃ₗ[F] V))) := by
    intro g
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h a ha
      exact (matEquiv b).injective (by
        rw [map_mul, map_mul]
        exact h _ ⟨a, ha, rfl⟩)
    · rintro h _ ⟨a, ha, rfl⟩
      show (matEquiv b) a * (matEquiv b) g = (matEquiv b) g * (matEquiv b) a
      rw [← map_mul, ← map_mul, h a ha]
  have hC : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      TauCeti.BilinForm.isometryGroup B ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := by
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf, hcent g]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨TauCeti.BilinForm.mem_isometryGroup_iff.mpr ((hU g).mp hgu), hgc⟩
    · rintro ⟨hgu, hgc⟩
      exact ⟨hgc, (hU g).mpr (TauCeti.BilinForm.mem_isometryGroup_iff.mp hgu)⟩
  have hrange : adjCent A' hadj ≤ (matEquiv b).toMonoidHom.range :=
    fun g _ => ⟨(matEquiv b).symm g, (matEquiv b).apply_symm_apply g⟩
  have hcomap : IsCoreFamily ((adjCent A' hadj).comap (matEquiv b).toMonoidHom)
      (fun c => (S c).comap (matEquiv b).toMonoidHom) :=
    hS.comap (matEquiv b).toMonoidHom (matEquiv b).injective hrange
  have hshape' : ∀ c, GGA6CharTwoLie ↥((S c).comap (matEquiv b).toMonoidHom) := by
    intro c
    have hmapS : ((S c).comap (matEquiv b).toMonoidHom).map (matEquiv b).toMonoidHom = S c :=
      Subgroup.map_comap_eq_self ((hS.1 c).trans hrange)
    exact GGA6CharTwoLie.of_mulEquiv
      (((((S c).comap (matEquiv b).toMonoidHom).equivMapOfInjective (matEquiv b).toMonoidHom
        (matEquiv b).injective).trans (MulEquiv.subgroupCongr hmapS))).symm (hshape c)
  exact GGA6CharTwoLie_of_isCoreFamily (hC ▸ hcomap) hshape' hJ

end CFSG.StandardType.A6Red

end
