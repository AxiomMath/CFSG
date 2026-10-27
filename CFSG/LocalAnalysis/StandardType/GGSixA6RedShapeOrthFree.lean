module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAssembly3
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeHerm
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedCoreShapeAlt
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaFree

public section

namespace CFSG.StandardType.A6Red

open Matrix QuadraticMap LayerCores
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ggA6_shape_orthFree {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate) (A : Subgroup (V ≃ₗ[K] V))
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hAodd : Odd (Nat.card A))
    (hAn : Group.IsNilpotent ↥A) (hfree : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    {J : Subgroup (V ≃ₗ[K] V)} (hJq : CFSG.Assembly.IsQuasisimple J)
    (hJs : CFSG.Assembly.IsSubnormal J (TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)))) :
    GGA6CharTwoLie ↥J := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  have : Fintype A := Fintype.ofFinite A
  have hA : (Fintype.card A : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_card_ne_zero_of_odd hAodd
  set b := Module.finBasis K V with hb
  set M := LinearMap.BilinForm.toMatrix b (polarBilin Q) with hM
  have hMt : Mᵀ = M := by
    ext i j
    rw [Matrix.transpose_apply, hM, LinearMap.BilinForm.toMatrix_apply,
      LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polarBilin_apply_apply,
      polar_comm]
  have hd : ∀ i, M i i = 0 := fun i => by
    rw [hM, LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_self, two_nsmul,
      CharTwo.add_self_eq_zero]
  have hMd : IsUnit M.det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ)
  have hadj := isInvol_gramAdj hMd hMt
  have hU := mem_unitaryOf_gramAdj_iff b hM hMd hMt
  set A' := A.map (matEquiv b).toMonoidHom with hA'
  have hA'U : A' ≤ unitaryOf hadj := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hU a).mpr (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hAO ha))
  have hcard : (Nat.card A' : K) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective (matEquiv b).toMonoidHom
      (matEquiv b).injective).toEquiv.symm]
    exact natCast_card_ne_zero_of_odd hAodd
  obtain ⟨Y₀, hY₀⟩ := exists_add_gramAdj_eq_one hMd hMt hd
  obtain ⟨Y, hYc, hY⟩ := exists_avg_add_eq_one hadj (gramAdj_smul M) hA'U hcard hY₀
  have hAn' : Group.IsNilpotent ↥A' :=
    Group.nilpotent_of_mulEquiv
      ((A.equivMapOfInjective (matEquiv b).toMonoidHom (matEquiv b).injective).trans
        (MulEquiv.subgroupCongr hA'.symm))
  have hfree' : ∀ w : Fin (Module.finrank K V) → K,
      (∀ g ∈ A', (g : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K).mulVec w = w) →
      w = 0 := by
    intro w hw
    set v : V := b.equivFun.symm w with hv
    have hvrepr : b.equivFun v = w := by rw [hv, LinearEquiv.apply_symm_apply]
    have hfix : ∀ a ∈ A, a v = v := by
      intro a ha
      change (a : V →ₗ[K] V) v = v
      have hmem : matEquiv b a ∈ A' := ⟨a, ha, rfl⟩
      have h1 := hw (matEquiv b a) hmem
      rw [coe_matEquiv] at h1
      have h2 := LinearMap.toMatrix_mulVec_repr b b (a : V →ₗ[K] V) v
      rw [← Module.Basis.equivFun_apply b v,
        ← Module.Basis.equivFun_apply b ((a : V →ₗ[K] V) v)] at h2
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
  have hcent : ∀ g : V ≃ₗ[K] V,
      ((matEquiv b).toMonoidHom g ∈
          Subgroup.centralizer (A' : Set (GL (Fin (Module.finrank K V)) K)) ↔
        g ∈ Subgroup.centralizer (A : Set (V ≃ₗ[K] V))) := by
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
  have hC' : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
    ext g
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_inf, hcent g]
    constructor
    · rintro ⟨hgc, hgu⟩
      exact ⟨hgc, isometry_of_polar hAO hA hfree hgc ((hU g).mp hgu)⟩
    · rintro ⟨hgc, hgO⟩
      exact ⟨hgc, (hU g).mpr (TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO)⟩
  have hC : (adjCent A' hadj).comap (matEquiv b).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q ⊓ Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) := by
    rw [hC', inf_comm]
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
  refine GGA6CharTwoLie_of_isCoreFamily (hC ▸ hcomap) hshape' ⟨?_, hJs, hJq⟩
  exact ggIsSubnormal_le hJs

end CFSG.StandardType.A6Red

end
