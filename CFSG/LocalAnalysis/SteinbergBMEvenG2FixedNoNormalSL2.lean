module

public import CFSG.Blueprint.Chevalley
public import CFSG.Foundations.Basic
public import CFSG.Blueprint.ChevalleyPinned
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2LongRoot
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore
import CFSG.LieType.Chevalley.RootLocalComponentFree
import CFSG.LieType.Chevalley.EvenRootCommutatorG2
import CFSG.LieType.Chevalley.NoncentralNormalSolvable
import CFSG.LieType.Chevalley.AdjointCenter
import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LocalAnalysis.SteinbergCDEvenClassicalOrderFour
public import Certificates.Certificate3951
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.SignKernelComponentPerfect

public section

namespace CFSG.LocalAnalysis.SteinbergBM

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

theorem exists_normal_simple_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (S : Subgroup X) (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    ∃ S' : Subgroup Y, S'.Normal ∧ IsSimpleGroup S' ∧ (∃ a b : S', a * b ≠ b * a) ∧
      Nonempty (S ≃* S') := by
  let eS : S ≃* S.map e.toMonoidHom := S.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨S.map e.toMonoidHom, hSn.map _ e.surjective, eS.symm.isSimpleGroup, ?_, ⟨eS⟩⟩
  obtain ⟨a, b, hab⟩ := hSnab
  exact ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩

theorem not_normal_simple_of_isCharacteristicP {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hH : CFSG.IsCharacteristicP p H) (S : Subgroup H) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) : False := by
  have hOn : (CFSG.pCore p H).Normal := CFSG.pCore_normal
  have hOp : IsPGroup p (CFSG.pCore p H) := CFSG.pCore_isPGroup
  have hN : ((CFSG.pCore p H).subgroupOf S).Normal := hOn.subgroupOf S
  obtain ⟨a, b, hab⟩ := hSnab
  rcases hN.eq_bot_or_eq_top with h | h
  ·
    have hcomm : ⁅S, CFSG.pCore p H⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine (commutator_le_inf S (CFSG.pCore p H)).trans fun x hx => ?_
      have hx' : (⟨x, hx.1⟩ : S) ∈ (CFSG.pCore p H).subgroupOf S := hx.2
      rw [h, mem_bot] at hx'
      exact mem_bot.mpr (congrArg Subtype.val hx')
    have hSO : S ≤ CFSG.pCore p H := (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hH
    have hone : ∀ x : S, x = 1 := fun x => by
      have hx : x ∈ (CFSG.pCore p H).subgroupOf S := mem_subgroupOf.mpr (hSO x.2)
      rwa [h, mem_bot] at hx
    exact hab (by rw [hone a, hone b])
  ·
    have hSO : S ≤ CFSG.pCore p H := fun x hx => by
      have hx' : (⟨x, hx⟩ : S) ∈ (CFSG.pCore p H).subgroupOf S := h ▸ mem_top _
      exact hx'
    have hSp : IsPGroup p S := hOp.to_le hSO
    have hZ : Nontrivial (center S) := hSp.center_nontrivial
    have hZtop : center S = ⊤ := by
      rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with h' | h'
      · exact absurd h' ((nontrivial_iff_ne_bot _).mp hZ)
      · exact h'
    exact hab (mem_center_iff.mp (hZtop ▸ mem_top b) a)

theorem map_eqLocus_mulAut_conj {X : Type*} [Group X] (ψ α : MulAut X) :
    (α.toMonoidHom.eqLocus (MonoidHom.id X)).map ψ.toMonoidHom =
      (ψ * α * ψ⁻¹).toMonoidHom.eqLocus (MonoidHom.id X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    change (ψ * α * ψ⁻¹) (ψ x) = ψ x
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hx']
  · intro hy
    have hy' : (ψ * α * ψ⁻¹) y = y := hy
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply] at hy'
    refine ⟨ψ.symm y, ?_, MulEquiv.apply_symm_apply ψ y⟩
    change α (ψ.symm y) = ψ.symm y
    apply ψ.injective
    rw [hy', MulEquiv.apply_symm_apply]

theorem map_eqLocus_mulAut_congr {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    (α : MulAut X) :
    (α.toMonoidHom.eqLocus (MonoidHom.id X)).map φ.toMonoidHom =
      (MulAut.congr φ α).toMonoidHom.eqLocus (MonoidHom.id Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : α x = x := hx
    change φ (α (φ.symm (φ x))) = φ x
    rw [MulEquiv.symm_apply_apply, hx']
  · intro hy
    have hy' : φ (α (φ.symm y)) = y := hy
    refine ⟨φ.symm y, ?_, MulEquiv.apply_symm_apply φ y⟩
    change α (φ.symm y) = φ.symm y
    rw [← MulEquiv.symm_apply_apply φ (α (φ.symm y)), hy']

end CFSG.LocalAnalysis.SteinbergBM
