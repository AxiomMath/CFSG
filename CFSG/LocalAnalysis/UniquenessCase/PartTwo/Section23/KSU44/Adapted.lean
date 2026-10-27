module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.B4Models
public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.NatEquiv
import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin CFSG.Open

private lemma conj_matrix_S03 {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K)
    (x γ : ↥(hypSU hK 2 0)) :
    ((((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((MulAut.conj x γ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K)) =
      ((((γ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
  have hψ : ∀ a b : ↥(hypSU hK 2 0),
      (((a * b : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
        (((a : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
          ((b : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K)) := by
    intro a b
    rw [Subgroup.coe_mul, Units.val_mul]
  have hgrp : (x⁻¹ : ↥(hypSU hK 2 0)) * MulAut.conj x γ = γ * x⁻¹ := by
    rw [MulAut.conj_apply, mul_assoc x γ x⁻¹]
    exact inv_mul_cancel_left x (γ * x⁻¹)
  calc (((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
        (((MulAut.conj x γ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K)
      = ((((x⁻¹ : ↥(hypSU hK 2 0)) * MulAut.conj x γ : ↥(hypSU hK 2 0)) :
            GL (HypIndex 2 0) K) : Matrix _ _ K) := (hψ _ _).symm
    _ = (((γ * x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K) := by
          rw [hgrp]
    _ = (((γ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K) *
        (((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) : Matrix _ _ K) := hψ _ _

private noncomputable def coordAddEquiv_S03 {K : Type} [Field K]
    (hK : UnitaryFieldData 2 2 K) (x : ↥(hypSU hK 2 0)) :
    (HypIndex 2 0 → K) ≃+ (HypIndex 2 0 → K) := by
  let Mx : GL (HypIndex 2 0) K := (x : ↥(hypSU hK 2 0))
  let Mxi : GL (HypIndex 2 0) K := (x⁻¹ : ↥(hypSU hK 2 0))
  have hMxMxi : Mx * Mxi = 1 := by
    change (x : GL (HypIndex 2 0) K) *
      ((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) = 1
    rw [← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]
  have hMxiMx : Mxi * Mx = 1 := by
    change ((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) *
      (x : GL (HypIndex 2 0) K) = 1
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  have hmatMx : (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
    rw [← Units.val_mul, hMxMxi, Units.val_one]
  have hmatMxi : (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
    rw [← Units.val_mul, hMxiMx, Units.val_one]
  exact
    { toFun := fun v => (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v
      invFun := fun v => (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v
      left_inv := fun v => by
        change (Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          ((Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hmatMx, Matrix.one_mulVec]
      right_inv := fun v => by
        change (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
          ((Mx : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hmatMxi, Matrix.one_mulVec]
      map_add' := fun v w => by
        change (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (v + w) =
          (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v +
            (Mxi : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w
        rw [Matrix.mulVec_add] }

private lemma exists_adapted_coord_S03 {W : Type} [CommGroup W] {K : Type} [Field K]
    (hK : UnitaryFieldData 2 2 K) {H : Subgroup (MulAut W)}
    (π : ↥(hypSU hK 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K))
    (he : ∀ (γ : ↥(hypSU hK 2 0)) (w : W),
      Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL (HypIndex 2 0) K) : Matrix _ _ K) *ᵥ Multiplicative.toAdd (e w))
    (x : ↥(hypSU hK 2 0)) :
    ∃ e' : W ≃* Multiplicative (HypIndex 2 0 → K),
      ∀ (γ : ↥(hypSU hK 2 0)) (w : W),
        Multiplicative.toAdd (e' (((((MulAut.conj x).trans π) γ : ↥H) : MulAut W) w)) =
          ((γ : GL (HypIndex 2 0) K) : Matrix _ _ K) *ᵥ Multiplicative.toAdd (e' w) := by
  refine ⟨e.trans (coordAddEquiv_S03 hK x).toMultiplicative, ?_⟩
  have hE' : ∀ y : W,
      Multiplicative.toAdd ((e.trans (coordAddEquiv_S03 hK x).toMultiplicative) y) =
        (((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
          Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ Multiplicative.toAdd (e y) :=
    fun y => rfl
  intro γ w
  have hmat : (((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (((MulAut.conj x γ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
    (((γ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) *
      (((x⁻¹ : ↥(hypSU hK 2 0)) : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) :=
    conj_matrix_S03 hK x γ
  simp only [hE']
  rw [MulEquiv.trans_apply, he (MulAut.conj x γ) w]
  simp only [Matrix.mulVec_mulVec]
  rw [hmat]

theorem exists_adapted_equiv {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {K : Type} [Field K] (hK : UnitaryFieldData 2 2 K)
    (hreal : (FFModel.nat (StatedSU 4 (2 ^ 2) K)).Realizes H ⊤ ⊥) (S : Sylow 2 ↥H) :
    ∃ (Φ : ↥(hypSU hK 2 0) ≃* ↥H) (e : W ≃* Multiplicative (HypIndex 2 0 → K)),
      (∀ (γ : ↥(hypSU hK 2 0)) (w : W),
        Multiplicative.toAdd (e (((Φ γ : ↥H) : MulAut W) w)) =
          ((γ : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ
            Multiplicative.toAdd (e w)) ∧
      (S : Subgroup ↥H) = (hypUnitriangular hK 2 0).map Φ.toMonoidHom := by
  obtain ⟨π, e, he⟩ := exists_hypNatEquiv hK hreal
  haveI : Finite ↥(hypSU hK 2 0) := by
    haveI := hK.finite
    infer_instance
  haveI : Finite ↥H := Finite.of_injective π.symm.toEquiv π.symm.toEquiv.injective
  obtain ⟨S₀, hS₀⟩ :=
    (unitary_order_and_Sylow hK (r := 2) (ε := 0) (by norm_num) (by norm_num)).2.1
  haveI : Finite (Sylow 2 ↥(hypSU hK 2 0)) := Sylow.finite_of_finiteIndex S₀
  let S' : Sylow 2 ↥(hypSU hK 2 0) :=
    S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥(hypSU hK 2 0) S₀ S'
  obtain ⟨e', he'⟩ := exists_adapted_coord_S03 hK π e he x
  refine ⟨(MulAut.conj x).trans π, e', he', ?_⟩
  have hS'coe : (S' : Subgroup ↥(hypSU hK 2 0)) =
      (S : Subgroup ↥H).map π.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := π.symm.toMonoidHom) (hf := π.symm.surjective) (P := S)
  have hS'smul : (S' : Subgroup ↥(hypSU hK 2 0)) =
      (hypUnitriangular hK 2 0).map
        ((MulAut.conj x : MulAut ↥(hypSU hK 2 0)) : ↥(hypSU hK 2 0) →* ↥(hypSU hK 2 0)) := by
    rw [← hx, Sylow.coe_subgroup_smul, hS₀, Subgroup.pointwise_smul_def]
    rfl
  rw [MulEquiv.toMonoidHom_eq_coe, MulEquiv.toMonoidHom_trans, ← Subgroup.map_map,
    ← hS'smul, hS'coe, Subgroup.map_map, MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.toMonoidHom_comp_toMonoidHom_symm, Subgroup.map_id]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KSUE
