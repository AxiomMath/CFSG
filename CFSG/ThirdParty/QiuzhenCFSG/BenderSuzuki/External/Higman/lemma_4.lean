module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic

import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 4
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped commutatorElement
open scoped IsMulCommutative

universe u v w

private def lemma4_iteratedCommutatorLift
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    higmanLowerCentralSeries H 1 :=
  ⟨⁅(x : H), (c : H)⁆, by
    apply (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 1 ≤ 2)
    have hcx : ⁅(c : H), (x : H)⁆ ∈ higmanLowerCentralSeries H 2 := by
      change ⁅(c : H), (x : H)⁆ ∈
        (⊤ : Subgroup H).lowerCentralSeries (1 + 1)
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(c : H), c.property, (x : H), trivial, rfl⟩
    have hinv := (higmanLowerCentralSeries H 2).inv_mem hcx
    simpa only [commutatorElement_inv] using hinv⟩

private theorem lemma4_iteratedCommutatorLift_mem_kernel
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    lemma4_iteratedCommutatorLift x c ∈ lowerCentralFactorKernel H 1 := by
  apply (show
    (higmanLowerCentralSeries H 2).subgroupOf (higmanLowerCentralSeries H 1) ≤
      lowerCentralFactorKernel H 1 by
    rw [lowerCentralFactorKernel]
    exact le_sup_right)
  change ⁅(x : H), (c : H)⁆ ∈ higmanLowerCentralSeries H 2
  have hcx : ⁅(c : H), (x : H)⁆ ∈ higmanLowerCentralSeries H 2 := by
    change ⁅(c : H), (x : H)⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries (1 + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure
      ⟨(c : H), c.property, (x : H), trivial, rfl⟩
  have hinv := (higmanLowerCentralSeries H 2).inv_mem hcx
  simpa only [commutatorElement_inv] using hinv

private theorem lemma4_quotient_conj_eq
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    QuotientGroup.mk' (lowerCentralFactorKernel H 1)
        (⟨(x : H) * (c : H) * (x : H)⁻¹,
          (inferInstance : (higmanLowerCentralSeries H 1).Normal).conj_mem
            (c : H) c.property (x : H)⟩ : higmanLowerCentralSeries H 1) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 1) c := by
  let q := QuotientGroup.mk' (lowerCentralFactorKernel H 1)
  have hfactor :
      (⟨(x : H) * (c : H) * (x : H)⁻¹,
        (inferInstance : (higmanLowerCentralSeries H 1).Normal).conj_mem
          (c : H) c.property (x : H)⟩ : higmanLowerCentralSeries H 1) =
        lemma4_iteratedCommutatorLift x c * c := by
    apply Subtype.ext
    change (x : H) * (c : H) * (x : H)⁻¹ =
      ((x : H) * (c : H) * (x : H)⁻¹ * (c : H)⁻¹) * (c : H)
    group
  rw [hfactor, map_mul]
  have hkernel : q (lemma4_iteratedCommutatorLift x c) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact lemma4_iteratedCommutatorLift_mem_kernel x c
  rw [hkernel, one_mul]

private def lemma4_commutatorLift
    {H : Type u} [Group H]
    (x y : higmanLowerCentralSeries H 0) : higmanLowerCentralSeries H 1 :=
  ⟨⁅(x : H), (y : H)⁆, by
    change ⁅(x : H), (y : H)⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries (0 + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure
      ⟨(x : H), x.property, (y : H), trivial, rfl⟩⟩

private def lemma4_commutatorRightHom
    {H : Type u} [Group H] (x : higmanLowerCentralSeries H 0) :
    higmanLowerCentralSeries H 0 →* LowerCentralFactor H 1 where
  toFun y :=
    QuotientGroup.mk' (lowerCentralFactorKernel H 1)
      (lemma4_commutatorLift x y)
  map_one' := by
    have hone : lemma4_commutatorLift x 1 = 1 := by
      apply Subtype.ext
      simp [lemma4_commutatorLift]
    rw [hone, map_one]
  map_mul' y z := by
    have hfactor :
        lemma4_commutatorLift x (y * z) =
          lemma4_commutatorLift x y *
            (⟨(y : H) * (lemma4_commutatorLift x z : H) * (y : H)⁻¹,
              (inferInstance : (higmanLowerCentralSeries H 1).Normal).conj_mem
                (lemma4_commutatorLift x z : H)
                (lemma4_commutatorLift x z).property (y : H)⟩ :
              higmanLowerCentralSeries H 1) := by
      apply Subtype.ext
      change ⁅(x : H), (y : H) * (z : H)⁆ =
        ⁅(x : H), (y : H)⁆ *
          ((y : H) * ⁅(x : H), (z : H)⁆ * (y : H)⁻¹)
      simp only [commutatorElement_def]
      group
    change QuotientGroup.mk' (lowerCentralFactorKernel H 1)
        (lemma4_commutatorLift x (y * z)) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma4_commutatorLift x y) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma4_commutatorLift x z)
    rw [hfactor, map_mul, lemma4_quotient_conj_eq]

private theorem lemma4_commutatorRightHom_kernel
    {H : Type u} [Group H] (x : higmanLowerCentralSeries H 0) :
    lowerCentralFactorKernel H 0 ≤ (lemma4_commutatorRightHom x).ker := by
  rw [lowerCentralFactorKernel]
  apply sup_le
  · rw [squaresSubgroup]
    rw [Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    change lemma4_commutatorRightHom x (y ^ 2) = 1
    rw [map_pow]
    exact lowerCentralFactor_sq_eq_one 1 _
  · intro c hc
    change lemma4_commutatorRightHom x c = 1
    change QuotientGroup.mk' (lowerCentralFactorKernel H 1)
      (lemma4_commutatorLift x c) = 1
    apply (QuotientGroup.eq_one_iff _).2
    let c' : higmanLowerCentralSeries H 1 := ⟨(c : H), hc⟩
    have heq :
        lemma4_commutatorLift x c =
          lemma4_iteratedCommutatorLift x c' := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact lemma4_iteratedCommutatorLift_mem_kernel x c'

private def lemma4_commutatorRightFactorHom
    {H : Type u} [Group H] (x : higmanLowerCentralSeries H 0) :
    LowerCentralFactor H 0 →* LowerCentralFactor H 1 :=
  QuotientGroup.lift (lowerCentralFactorKernel H 0)
    (lemma4_commutatorRightHom x) (lemma4_commutatorRightHom_kernel x)


private def lemma4_commutatorLeftHom
    {H : Type u} [Group H] :
    higmanLowerCentralSeries H 0 →*
      (LowerCentralFactor H 0 →* LowerCentralFactor H 1) where
  toFun x := lemma4_commutatorRightFactorHom x
  map_one' := by
    apply MonoidHom.ext
    intro yq
    refine Quotient.inductionOn' yq ?_
    intro y
    change QuotientGroup.mk' (lowerCentralFactorKernel H 1)
      (lemma4_commutatorLift 1 y) = 1
    have hone : lemma4_commutatorLift 1 y = 1 := by
      apply Subtype.ext
      simp [lemma4_commutatorLift]
    rw [hone, map_one]
  map_mul' x z := by
    apply MonoidHom.ext
    intro yq
    refine Quotient.inductionOn' yq ?_
    intro y
    have hfactor :
        lemma4_commutatorLift (x * z) y =
          (⟨(x : H) * (lemma4_commutatorLift z y : H) * (x : H)⁻¹,
            (inferInstance : (higmanLowerCentralSeries H 1).Normal).conj_mem
              (lemma4_commutatorLift z y : H)
              (lemma4_commutatorLift z y).property (x : H)⟩ :
            higmanLowerCentralSeries H 1) *
          lemma4_commutatorLift x y := by
      apply Subtype.ext
      change ⁅(x : H) * (z : H), (y : H)⁆ =
        ((x : H) * ⁅(z : H), (y : H)⁆ * (x : H)⁻¹) *
          ⁅(x : H), (y : H)⁆
      simp only [commutatorElement_def]
      group
    change QuotientGroup.mk' (lowerCentralFactorKernel H 1)
        (lemma4_commutatorLift (x * z) y) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma4_commutatorLift x y) *
        QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma4_commutatorLift z y)
    rw [hfactor, map_mul, lemma4_quotient_conj_eq]
    exact mul_comm _ _

private theorem lemma4_commutatorLeftHom_kernel
    {H : Type u} [Group H] :
    lowerCentralFactorKernel H 0 ≤
      (lemma4_commutatorLeftHom (H := H)).ker := by
  change
    (squaresSubgroup (higmanLowerCentralSeries H 0) ⊔
      (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0)) ≤ _
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change lemma4_commutatorLeftHom (H := H) (x ^ 2) = 1
    rw [map_pow]
    apply MonoidHom.ext
    intro y
    change (lemma4_commutatorLeftHom (H := H) x y) ^ 2 = 1
    exact lowerCentralFactor_sq_eq_one 1 _
  · intro c hc
    change lemma4_commutatorLeftHom (H := H) c = 1
    apply MonoidHom.ext
    intro yq
    refine Quotient.inductionOn' yq ?_
    intro y
    change QuotientGroup.mk' (lowerCentralFactorKernel H 1)
      (lemma4_commutatorLift c y) = 1
    apply (QuotientGroup.eq_one_iff _).2
    let c' : higmanLowerCentralSeries H 1 := ⟨(c : H), hc⟩
    have heq :
        lemma4_commutatorLift c y =
          (lemma4_iteratedCommutatorLift y c')⁻¹ := by
      apply Subtype.ext
      exact (commutatorElement_inv (y : H) (c : H)).symm
    rw [heq]
    exact (lowerCentralFactorKernel H 1).inv_mem
      (lemma4_iteratedCommutatorLift_mem_kernel y c')

private def lemma4_commutatorFactorHom
    {H : Type u} [Group H] :
    LowerCentralFactor H 0 →*
      (LowerCentralFactor H 0 →* LowerCentralFactor H 1) :=
  QuotientGroup.lift (lowerCentralFactorKernel H 0)
    (lemma4_commutatorLeftHom (H := H))
    (lemma4_commutatorLeftHom_kernel (H := H))


private noncomputable def lemma4_commutatorFactorAddHom
    {H : Type u} [Group H] :
    Additive (LowerCentralFactor H 0) →+
      (Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1)) where
  toFun x :=
    ((lemma4_commutatorFactorHom x.toMul).toAdditive).toZModLinearMap 2
  map_zero' := by
    apply LinearMap.ext
    intro y
    apply Additive.toMul.injective
    exact MonoidHom.map_one₂ (lemma4_commutatorFactorHom (H := H)) y.toMul
  map_add' x z := by
    apply LinearMap.ext
    intro y
    apply Additive.toMul.injective
    exact MonoidHom.map_mul₂ (lemma4_commutatorFactorHom (H := H))
      x.toMul z.toMul y.toMul

private noncomputable def lemma4_lowerCentralBracket
    {H : Type u} [Group H] :
    Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1) :=
  (lemma4_commutatorFactorAddHom (H := H)).toZModLinearMap 2

private theorem lemma4_lowerCentralBracket_mk_mk
    {H : Type u} [Group H]
    (x y : higmanLowerCentralSeries H 0) :
    lemma4_lowerCentralBracket
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma4_commutatorLift x y)) :=
  rfl

private theorem lemma4_commutatorLift_equivariant
    {H : Type u} [Group H] (theta : MulAut H)
    (x y : higmanLowerCentralSeries H 0) :
    lowerCentralSeriesMulAut theta 1 (lemma4_commutatorLift x y) =
      lemma4_commutatorLift
        (lowerCentralSeriesMulAut theta 0 x)
        (lowerCentralSeriesMulAut theta 0 y) := by
  apply Subtype.ext
  rw [BenderSuzuki.External.Higman.lowerCentralSeriesMulAut_apply]
  change theta ⁅(x : H), (y : H)⁆ = ⁅theta (x : H), theta (y : H)⁆
  exact map_commutatorElement theta (x : H) (y : H)

private theorem lemma4_lowerCentralBracket_class_mem_span
    {H : Type u} [Group H] (c : higmanLowerCentralSeries H 1) :
    Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c) ∈
      Submodule.span (ZMod 2)
        (Set.range fun p :
          Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 0) =>
          lemma4_lowerCentralBracket p.1 p.2) := by
  let W := Submodule.span (ZMod 2)
    (Set.range fun p :
      Additive (LowerCentralFactor H 0) ×
        Additive (LowerCentralFactor H 0) =>
      lemma4_lowerCentralBracket p.1 p.2)
  let q := QuotientGroup.mk' (lowerCentralFactorKernel H 1)
  change Additive.ofMul (q c) ∈ W
  have hc : (c : H) ∈ higmanLowerCentralSeries H 1 := c.property
  change (c : H) ∈ Subgroup.closure
    {z | ∃ x ∈ higmanLowerCentralSeries H 0, ∃ y ∈ (⊤ : Subgroup H),
      x * y * x⁻¹ * y⁻¹ = z} at hc
  refine Subgroup.closure_induction (p := fun z hz =>
    Additive.ofMul
      (q (⟨z, hz⟩ : higmanLowerCentralSeries H 1)) ∈ W) ?_ ?_ ?_ ?_ hc
  · intro z hz
    rcases hz with ⟨x, hx, y, _hy, rfl⟩
    let x' : higmanLowerCentralSeries H 0 := ⟨x, hx⟩
    let y' : higmanLowerCentralSeries H 0 := ⟨y, trivial⟩
    apply Submodule.subset_span
    refine ⟨(Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x'),
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y')), ?_⟩
    refine (lemma4_lowerCentralBracket_mk_mk x' y').trans ?_
    apply Additive.ofMul.injective
    apply congrArg q
    apply Subtype.ext
    rfl
  · change Additive.ofMul (q (1 : higmanLowerCentralSeries H 1)) ∈ W
    rw [map_one, ofMul_one]
    exact W.zero_mem
  · intro a b ha hb iha ihb
    change Additive.ofMul
      (q ((⟨a, ha⟩ : higmanLowerCentralSeries H 1) * ⟨b, hb⟩)) ∈ W
    rw [map_mul, ofMul_mul]
    exact W.add_mem iha ihb
  · intro a ha iha
    change Additive.ofMul
      (q (⟨a, ha⟩ : higmanLowerCentralSeries H 1)⁻¹) ∈ W
    rw [map_inv, ofMul_inv]
    exact W.neg_mem iha

private theorem lemma4_lowerCentralBracket_span
    {H : Type u} [Group H] :
    Submodule.span (ZMod 2)
        (Set.range fun p :
          Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 0) =>
          lemma4_lowerCentralBracket p.1 p.2) = ⊤ := by
  apply top_unique
  intro z _hz
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 1) z.toMul
  have hz :
      z = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 1) c) := by
    apply Additive.toMul.injective
    exact hc.symm
  rw [hz]
  exact lemma4_lowerCentralBracket_class_mem_span c

private theorem lemma4_lowerCentralBracket_equivariant
    {H : Type u} [Group H] (theta : MulAut H)
    (v w : Additive (LowerCentralFactor H 0)) :
    lemma4_lowerCentralBracket
        (lowerCentralFactorLinearAut theta 0 v)
        (lowerCentralFactorLinearAut theta 0 w) =
      lowerCentralFactorLinearAut theta 1
        (lemma4_lowerCentralBracket v w) := by
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
  obtain ⟨y, hy⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) w.toMul
  have hv :
      v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  have hw :
      w = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y) := by
    apply Additive.toMul.injective
    exact hy.symm
  rw [hv, hw, lowerCentralFactorLinearAut_ofMul_mk,
    lowerCentralFactorLinearAut_ofMul_mk,
    lemma4_lowerCentralBracket_mk_mk,
    lemma4_lowerCentralBracket_mk_mk,
    lowerCentralFactorLinearAut_ofMul_mk]
  apply Additive.ofMul.injective
  exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel H 1))
    (lemma4_commutatorLift_equivariant theta x y).symm

private theorem lemma4_lowerCentralBracket_self
    {H : Type u} [Group H]
    (v : Additive (LowerCentralFactor H 0)) :
    lemma4_lowerCentralBracket v v = 0 := by
  obtain ⟨x, hx⟩ :=
    QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
  have hv :
      v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  rw [hv, lemma4_lowerCentralBracket_mk_mk]
  have hone : lemma4_commutatorLift x x = 1 := by
    apply Subtype.ext
    simp [lemma4_commutatorLift]
  rw [hone, map_one, ofMul_one]
/-- The canonical lower-central commutator bracket, exposed with the interfaces
needed by later Higman lemmas. -/
public theorem lemma4_exists_lowerCentralBracket
    {H : Type u} [Group H] :
    ∃ bracket : Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
          Additive (LowerCentralFactor H 1),
      (∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩)) ∧
      (∀ theta : MulAut H,
        ∀ v w : Additive (LowerCentralFactor H 0),
          bracket (lowerCentralFactorLinearAut theta 0 v)
              (lowerCentralFactorLinearAut theta 0 w) =
            lowerCentralFactorLinearAut theta 1 (bracket v w)) ∧
      (∀ v : Additive (LowerCentralFactor H 0), bracket v v = 0) ∧
      Submodule.span (ZMod 2)
        (Set.range fun p :
          Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 0) => bracket p.1 p.2) = ⊤ := by
  refine ⟨lemma4_lowerCentralBracket, ?_, ?_, ?_,
    lemma4_lowerCentralBracket_span⟩
  · intro x y hcomm
    have hlift : lemma4_commutatorLift x y =
        (⟨⁅(x : H), (y : H)⁆, hcomm⟩ : higmanLowerCentralSeries H 1) :=
      Subtype.ext (by rfl)
    simpa [hlift] using lemma4_lowerCentralBracket_mk_mk x y
  · exact lemma4_lowerCentralBracket_equivariant
  · exact lemma4_lowerCentralBracket_self
public theorem lemma4_transitive_linearAut_order
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ x : V, x ≠ 0 → ∀ y : V, y ≠ 0 →
      ∃ k : ℕ, (T ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card V = 2 ^ n) :
    orderOf T = 2 ^ n - 1 := by
  classical
  have hcard_gt : 1 < Nat.card V := by
    rw [hcard]
    exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
  letI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp hcard_gt
  letI := Fintype.ofFinite V
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  let orbit :
      Subgroup.zpowers T → {v : V // v ≠ 0} :=
    fun g => ⟨(g : V ≃ₗ[ZMod 2] V) x,
      fun hzero => hx ((g : V ≃ₗ[ZMod 2] V).injective
        (by simpa using hzero))⟩
  have horbit_surjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := htrans x hx y hy
    refine ⟨⟨T ^ k, Subgroup.npow_mem_zpowers T k⟩, ?_⟩
    exact Subtype.ext hk
  have horbit_injective : Function.Injective orbit := by
    intro g h hgh
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    by_cases hy : y = 0
    · simp [hy]
    obtain ⟨k, hk⟩ := htrans x hx y hy
    have hghx :
        (g : V ≃ₗ[ZMod 2] V) x = (h : V ≃ₗ[ZMod 2] V) x :=
      congrArg Subtype.val hgh
    let p : Subgroup.zpowers T :=
      ⟨T ^ k, Subgroup.npow_mem_zpowers T k⟩
    have hcomm_g :
        (g : V ≃ₗ[ZMod 2] V) * T ^ k =
          T ^ k * (g : V ≃ₗ[ZMod 2] V) :=
      congrArg Subtype.val (mul_comm g p)
    have hcomm_h :
        (h : V ≃ₗ[ZMod 2] V) * T ^ k =
          T ^ k * (h : V ≃ₗ[ZMod 2] V) :=
      congrArg Subtype.val (mul_comm h p)
    rw [← hk, ← LinearEquiv.mul_apply, hcomm_g,
      LinearEquiv.mul_apply, hghx, ← LinearEquiv.mul_apply,
      ← hcomm_h, LinearEquiv.mul_apply]
  have horbit_card :
      Nat.card (Subgroup.zpowers T) = Nat.card {v : V // v ≠ 0} :=
    Nat.card_congr (Equiv.ofBijective orbit
      ⟨horbit_injective, horbit_surjective⟩)
  have hnonzero_card : Nat.card {v : V // v ≠ 0} = Nat.card V - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun v : V => v = 0)]
    simp
  rw [Nat.card_zpowers] at horbit_card
  rw [horbit_card, hnonzero_card, hcard]

private theorem lemma4_diagonal_alternating_span_forces_product
    {K : Type u} {W : Type v} {ι : Type w}
    [Field K] [AddCommGroup W] [Module K W]
    (T : W →ₗ[K] W)
    (basis : Module.Basis ι K W)
    (mu : ι → K)
    (hdiagonal : ∀ i : ι, T (basis i) = mu i • basis i)
    (B : W →ₗ[K] W →ₗ[K] W)
    (halternating : ∀ x : W, B x x = 0)
    (hequivariant : ∀ x y : W, B (T x) (T y) = T (B x y))
    (hspan :
      Submodule.span K
        (Set.range fun p : W × W => B p.1 p.2) = ⊤) :
    ∀ k : ι, ∃ i j : ι, i ≠ j ∧ mu k = mu i * mu j := by
  classical
  intro k
  by_contra hproduct
  push Not at hproduct
  have hcoord_T (z : W) :
      basis.coord k (T z) = mu k * basis.coord k z := by
    have hmaps :
        (basis.coord k).comp T = (mu k) • basis.coord k := by
      apply basis.ext
      intro i
      rw [LinearMap.comp_apply, hdiagonal, map_smul,
        LinearMap.smul_apply]
      by_cases hik : i = k
      · subst i
        simp
      · simp [Module.Basis.coord_apply, Module.Basis.repr_self, hik]
    exact LinearMap.congr_fun hmaps z
  let coordinatePairing : W →ₗ[K] W →ₗ[K] K :=
    { toFun := fun x => (basis.coord k).comp (B x)
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro c x
        ext z
        simp }
  have hcoordinatePairing : coordinatePairing = 0 := by
    apply basis.ext
    intro i
    apply basis.ext
    intro j
    change basis.coord k (B (basis i) (basis j)) = 0
    by_cases hij : i = j
    · subst j
      rw [halternating, map_zero]
    · have heigen :
          T (B (basis i) (basis j)) =
            (mu i * mu j) • B (basis i) (basis j) := by
        simpa [hdiagonal, smul_smul, mul_comm] using
          (hequivariant (basis i) (basis j)).symm
      have heq := congrArg (fun z => basis.coord k z) heigen
      change basis.coord k (T (B (basis i) (basis j))) =
        basis.coord k ((mu i * mu j) • B (basis i) (basis j)) at heq
      rw [hcoord_T, map_smul] at heq
      by_contra hcoord
      exact (hproduct i j hij) (mul_right_cancel₀ hcoord heq)
  have hcoordinate_zero (x y : W) :
      basis.coord k (B x y) = 0 := by
    change coordinatePairing x y = 0
    rw [hcoordinatePairing]
    rfl
  have hrange_le :
      Set.range (fun p : W × W => B p.1 p.2) ⊆
        (basis.coord k).ker := by
    rintro z ⟨⟨x, y⟩, rfl⟩
    exact (LinearMap.mem_ker).2 (hcoordinate_zero x y)
  have htop_le : (⊤ : Submodule K W) ≤ (basis.coord k).ker := by
    rw [← hspan]
    exact Submodule.span_le.2 hrange_le
  have hbasis_mem : basis k ∈ (basis.coord k).ker :=
    htop_le Submodule.mem_top
  have hzero := (LinearMap.mem_ker).1 hbasis_mem
  simp [Module.Basis.coord_apply, Module.Basis.repr_self] at hzero

section SingerScalarExtension

open scoped TensorProduct

local instance : Fact (Nat.Prime 2) where
  out := Nat.prime_two

private abbrev K := AlgebraicClosure (ZMod 2)

noncomputable local instance : Module (ZMod 2) K := Algebra.toModule

noncomputable local instance : Algebra K K := Algebra.id K

noncomputable local instance : Module K K := Algebra.toModule

private abbrev BC (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] :=
  TensorProduct (ZMod 2) K V
private theorem lemma4_singer_fixed_pow
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (T : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ x, x ≠ 0 → ∀ y, y ≠ 0 →
      ∃ k : ℕ, (T ^ k) x = y)
    (k : ℕ) (x : V) (hx : x ≠ 0) (hfix : (T ^ k) x = x) :
    T ^ k = 1 := by
  apply LinearEquiv.ext
  intro y
  by_cases hy : y = 0
  · simp [hy]
  obtain ⟨j, hj⟩ := htrans x hx y hy
  have hcomm : (T ^ k) * (T ^ j) = (T ^ j) * (T ^ k) := by
    rw [← pow_add, add_comm, pow_add]
  rw [← hj, ← LinearEquiv.mul_apply, hcomm,
    LinearEquiv.mul_apply, hfix, hj]
  simp

private theorem lemma4_singer_descend_fixed_vector
    {R A M : Type*}
    [Field R] [Field A] [Algebra R A]
    [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    (T : M ≃ₗ[R] M) (lambda : A) (d : ℕ)
    (h : Module.End.HasEigenvalue
      (T.baseChange R A M M).toLinearMap lambda)
    (hlambda : lambda ^ d = 1) :
    ∃ v : M, v ≠ 0 ∧ (T ^ d) v = v := by
  let eT : (A ⊗[R] M) ≃ₗ[A] (A ⊗[R] M) :=
    T.baseChange R A M M
  have hpow :
      Module.End.HasEigenvalue
        (eT.toLinearMap ^ d)
        (lambda ^ d) :=
    h.pow d
  have hmap :
      (eT ^ d).toLinearMap = eT.toLinearMap ^ d :=
    map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom eT d
  have hpow' :
      Module.End.HasEigenvalue
        ((((T ^ d).toLinearMap).baseChange A) :
          Module.End A (A ⊗[R] M))
        (1 : A) := by
    rw [← hlambda]
    rw [← LinearEquiv.coe_baseChange,
      LinearEquiv.baseChange_pow]
    rw [hmap]
    exact hpow
  have hrootA :
      (((T ^ d).toLinearMap).baseChange A).charpoly.IsRoot (1 : A) :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp hpow'
  rw [LinearMap.charpoly_baseChange] at hrootA
  have hrootR :
      (T ^ d).toLinearMap.charpoly.IsRoot (1 : R) := by
    exact (Polynomial.isRoot_map_iff
      (algebraMap R A).injective).mp (by simpa using hrootA)
  have heigR :
      Module.End.HasEigenvalue (T ^ d).toLinearMap (1 : R) :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hrootR
  obtain ⟨v, hv⟩ := heigR.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  simpa using hv.apply_eq_smul

set_option backward.isDefEq.respectTransparency false in
private theorem lemma4_singer_frobenius_eigenvalue
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V) (lambda : K)
    (hlambda : Module.End.HasEigenvalue (R := K)
      (M := TensorProduct (ZMod 2) K V)
      (T.toLinearMap.baseChange K) lambda)
    (i : ℕ) :
    Module.End.HasEigenvalue (R := K)
      (M := TensorProduct (ZMod 2) K V)
      (T.toLinearMap.baseChange K) (lambda ^ (2 ^ i)) := by
  classical
  letI := Fintype.ofFinite V
  letI : Module.Finite K (TensorProduct (ZMod 2) K V) :=
    Module.Finite.of_basis
      ((Module.Free.chooseBasis (ZMod 2) V).baseChange K)
  let f : Module.End K (BC V) := T.toLinearMap.baseChange K
  have hroot : f.charpoly.IsRoot lambda :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f lambda).mp
      (by simpa [f] using hlambda)
  dsimp [f] at hroot
  have hcharpoly :
      (T.toLinearMap.baseChange K).charpoly =
        T.toLinearMap.charpoly.map (algebraMap (ZMod 2) K) :=
    LinearMap.charpoly_baseChange T.toLinearMap K
  rw [hcharpoly] at hroot
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hmapped :=
    hroot.map (f := (sigma ^ i).toAlgHom.toRingHom)
  rw [Polynomial.map_map] at hmapped
  have hcomp :
      ((sigma ^ i).toAlgHom.toRingHom).comp
          (algebraMap (ZMod 2) K) =
        algebraMap (ZMod 2) K :=
    (sigma ^ i).toAlgHom.comp_algebraMap
  rw [hcomp] at hmapped
  have hsigma : (sigma ^ i) lambda = lambda ^ (2 ^ i) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have hsigma' :
      ((sigma ^ i).toAlgHom.toRingHom) lambda =
        lambda ^ (2 ^ i) := by
    simpa using hsigma
  have hroot' : f.charpoly.IsRoot (lambda ^ (2 ^ i)) := by
    dsimp [f]
    rw [hcharpoly]
    rwa [hsigma'] at hmapped
  exact (Module.End.hasEigenvalue_iff_isRoot_charpoly f
    (lambda ^ (2 ^ i))).mpr hroot'

private theorem lemma4_singer_primitive_root
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ x, x ≠ 0 → ∀ y, y ≠ 0 →
      ∃ k : ℕ, (T ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card V = 2 ^ n)
    (hT_order : orderOf T = 2 ^ n - 1) :
    ∃ lambda : K,
      Module.End.HasEigenvalue (R := K)
          (M := TensorProduct (ZMod 2) K V)
          (T.toLinearMap.baseChange K) lambda ∧
        lambda ≠ 0 ∧ orderOf lambda = 2 ^ n - 1 := by
  classical
  letI := Fintype.ofFinite V
  letI : Module.Finite K (TensorProduct (ZMod 2) K V) :=
    Module.Finite.of_basis
      ((Module.Free.chooseBasis (ZMod 2) V).baseChange K)
  have hfinrank : Module.finrank (ZMod 2) V = n := by
    have hpow :
        2 ^ Module.finrank (ZMod 2) V = 2 ^ n := by
      calc
        2 ^ Module.finrank (ZMod 2) V
            = Nat.card V := by
                simpa [Nat.card_zmod] using
                  (Module.natCard_eq_pow_finrank
                    (K := ZMod 2) (V := V)).symm
        _ = 2 ^ n := hcard
    exact Nat.pow_right_injective (by norm_num : 1 < 2) hpow
  let f : Module.End K (BC V) := T.toLinearMap.baseChange K
  have hfinrank_bc : Module.finrank K (BC V) = n := by
    exact (Module.finrank_baseChange
      (R := K) (S := ZMod 2) (M' := V)).trans hfinrank
  have hnatDegree : f.charpoly.natDegree = n := by
    rw [LinearMap.charpoly_natDegree, hfinrank_bc]
  have hdegree : f.charpoly.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree
      (LinearMap.charpoly_monic f).ne_zero, hnatDegree]
    exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨lambda, hlambda_root⟩ :=
    IsAlgClosed.exists_root f.charpoly hdegree
  have hlambda_eigen : Module.End.HasEigenvalue f lambda :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f lambda).2
      hlambda_root
  obtain ⟨v, hv⟩ := hlambda_eigen.exists_hasEigenvector
  have hTpow : T ^ (2 ^ n - 1) = 1 := by
    rw [← hT_order]
    exact pow_orderOf_eq_one T
  have heTpow :
      (T.baseChange (ZMod 2) K V V) ^ (2 ^ n - 1) = 1 := by
    rw [← LinearEquiv.baseChange_pow, hTpow,
      LinearEquiv.baseChange_one]
  have hf_eq :
      f = (T.baseChange (ZMod 2) K V V).toLinearMap := by
    simp [f]
  have hfpow : f ^ (2 ^ n - 1) = 1 := by
    let eT := T.baseChange (ZMod 2) K V V
    have hmap :
        (eT ^ (2 ^ n - 1)).toLinearMap =
          eT.toLinearMap ^ (2 ^ n - 1) :=
      map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom
        eT (2 ^ n - 1)
    calc
      f ^ (2 ^ n - 1) =
          eT.toLinearMap ^ (2 ^ n - 1) := by
            simpa [eT] using congrArg
              (fun g : Module.End K (BC V) => g ^ (2 ^ n - 1)) hf_eq
      _ = (eT ^ (2 ^ n - 1)).toLinearMap := hmap.symm
      _ = (1 : BC V ≃ₗ[K] BC V).toLinearMap := by
            exact congrArg (fun e : BC V ≃ₗ[K] BC V => e.toLinearMap)
              heTpow
      _ = 1 := rfl
  have hvpow := hv.pow_apply (2 ^ n - 1)
  rw [hfpow] at hvpow
  have hlambda_pow : lambda ^ (2 ^ n - 1) = 1 := by
    apply smul_left_injective K hv.2
    simpa using hvpow.symm
  refine ⟨lambda, hlambda_eigen, ?_, ?_⟩
  · intro hlambda
    subst lambda
    have hpositive : 0 < 2 ^ n - 1 := by
      have : 1 < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
      omega
    simp [Nat.ne_of_gt hpositive] at hlambda_pow
  · apply Nat.dvd_antisymm
    · exact orderOf_dvd_iff_pow_eq_one.mpr hlambda_pow
    · obtain ⟨x, hx, hfix⟩ :=
        lemma4_singer_descend_fixed_vector T lambda (orderOf lambda)
          (by simpa [f, LinearEquiv.coe_baseChange] using hlambda_eigen)
          (pow_orderOf_eq_one lambda)
      rw [← hT_order]
      exact orderOf_dvd_iff_pow_eq_one.mpr
        (lemma4_singer_fixed_pow T htrans (orderOf lambda) x hx hfix)

set_option backward.isDefEq.respectTransparency false in
private theorem lemma4_singer_eigenbasis
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ x, x ≠ 0 → ∀ y, y ≠ 0 →
      ∃ k : ℕ, (T ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card V = 2 ^ n)
    (hT_order : orderOf T = 2 ^ n - 1) :
    ∃ (lambda : K) (basis : Module.Basis (Fin n) K (BC V)),
      orderOf lambda = 2 ^ n - 1 ∧
        ∀ i : Fin n,
          (T.toLinearMap.baseChange K) (basis i) =
            lambda ^ (2 ^ (i : ℕ)) • basis i := by
  classical
  letI := Fintype.ofFinite V
  letI : Module.Finite K (BC V) :=
    Module.Finite.of_basis
      ((Module.Free.chooseBasis (ZMod 2) V).baseChange K)
  obtain ⟨lambda, hlambda_eigen, hlambda_ne, hlambda_order⟩ :=
    lemma4_singer_primitive_root T htrans n hn hcard hT_order
  let f : Module.End K (BC V) := T.toLinearMap.baseChange K
  let mu : Fin n → K := fun i => lambda ^ (2 ^ (i : ℕ))
  have hfinrank : Module.finrank (ZMod 2) V = n := by
    have hpow :
        2 ^ Module.finrank (ZMod 2) V = 2 ^ n := by
      calc
        2 ^ Module.finrank (ZMod 2) V
            = Nat.card V := by
                simpa [Nat.card_zmod] using
                  (Module.natCard_eq_pow_finrank
                    (K := ZMod 2) (V := V)).symm
        _ = 2 ^ n := hcard
    exact Nat.pow_right_injective (by norm_num : 1 < 2) hpow
  have hfinrank_bc : Module.finrank K (BC V) = n :=
    (Module.finrank_baseChange
      (R := K) (S := ZMod 2) (M' := V)).trans hfinrank
  have hpow_pred : 2 ^ (n - 1) < 2 ^ n - 1 := by
    have hn_pred : n = (n - 1) + 1 := by omega
    have hpow_n : 2 ^ n = 2 ^ (n - 1) * 2 :=
      (congrArg (fun e : ℕ => 2 ^ e) hn_pred).trans
        (pow_succ 2 (n - 1))
    have hlarge : 1 < 2 ^ (n - 1) :=
      Nat.one_lt_pow (by omega) (by norm_num)
    calc
      2 ^ (n - 1) < 2 ^ (n - 1) * 2 - 1 := by omega
      _ = 2 ^ n - 1 := by rw [hpow_n]
  have hexponent_lt (i : Fin n) :
      2 ^ (i : ℕ) < orderOf lambda := by
    rw [hlambda_order]
    exact lt_of_le_of_lt
      ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2
        (by omega : (i : ℕ) ≤ n - 1))
      hpow_pred
  have hmu_injective : Function.Injective mu := by
    intro i j hij
    have hexponent :
        2 ^ (i : ℕ) = 2 ^ (j : ℕ) :=
      pow_injOn_Iio_orderOf
        (hexponent_lt i) (hexponent_lt j) (by simpa [mu] using hij)
    apply Fin.ext
    exact Nat.pow_right_injective (by norm_num : 1 < 2) hexponent
  have heigen (i : Fin n) : f.HasEigenvalue (mu i) := by
    exact lemma4_singer_frobenius_eigenvalue T lambda
      (by simpa [f] using hlambda_eigen) i
  choose v hv using fun i => (heigen i).exists_hasEigenvector
  have hv_linearIndependent : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' f mu hmu_injective v hv
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let basis : Module.Basis (Fin n) K (BC V) :=
    basisOfLinearIndependentOfCardEqFinrank hv_linearIndependent
      (by simp [hfinrank_bc])
  refine ⟨lambda, basis, hlambda_order, ?_⟩
  intro i
  have hi := (hv i).apply_eq_smul
  simpa [f, mu, basis] using hi

private theorem lemma4_singer_alternating_isSymm
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V)
    (halternating : ∀ v : V, B v v = 0) :
    ∀ x y : V, B x y = B y x := by
  intro x y
  calc
    B x y = -B x y := (ZModModule.neg_eq_self _).symm
    _ = B y x := LinearMap.IsAlt.neg halternating x y

private theorem lemma4_singer_baseChange_alternating
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V)
    (halternating : ∀ v : V, B v v = 0) :
    ∀ x : BC V, LinearMap.BilinMap.baseChange K B x x = 0 := by
  let BK : BC V →ₗ[K] BC V →ₗ[K] BC V :=
    LinearMap.BilinMap.baseChange K B
  have hsym : ∀ x y : V, B x y = B y x :=
    lemma4_singer_alternating_isSymm B halternating
  have hsymK : ∀ x y : BC V, BK x y = BK y x := by
    intro x y
    exact LinearMap.BilinMap.baseChange_isSymm hsym x y
  intro x
  change BK x x = 0
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a v =>
      calc
        BK (a ⊗ₜ[ZMod 2] v) (a ⊗ₜ[ZMod 2] v) =
            (a * a) ⊗ₜ[ZMod 2] (B v v) := by
              exact LinearMap.BilinMap.baseChange_tmul B a v a v
        _ = 0 := by rw [halternating, TensorProduct.tmul_zero]
  | add x y hx hy =>
      calc
        BK (x + y) (x + y) =
            (BK x x + BK x y) + (BK y x + BK y y) := by
              rw [BK.map_add x y, LinearMap.add_apply, map_add, map_add]
        _ = BK x y + BK y x := by rw [hx, hy]; simp
        _ = BK x y + BK x y := by rw [hsymK y x]
        _ = 0 := ZModModule.add_self _
private theorem lemma4_singer_baseChange_equivariant
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (T : V →ₗ[ZMod 2] V)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V)
    (hequivariant : ∀ v w : V, B (T v) (T w) = T (B v w)) :
    ∀ x y : BC V,
      LinearMap.BilinMap.baseChange K B
          (T.baseChange K x) (T.baseChange K y) =
        T.baseChange K (LinearMap.BilinMap.baseChange K B x y) := by
  let TK : BC V →ₗ[K] BC V := T.baseChange K
  let BK : BC V →ₗ[K] BC V →ₗ[K] BC V :=
    LinearMap.BilinMap.baseChange K B
  change ∀ x y : BC V, BK (TK x) (TK y) = TK (BK x y)
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      intro y
      simp only [map_zero, LinearMap.zero_apply]
  | tmul a v =>
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b w =>
          have hT_tmul (c : K) (z : V) :
              TK (c ⊗ₜ[ZMod 2] z) = c ⊗ₜ[ZMod 2] T z := by
            exact LinearMap.baseChange_tmul T c z
          have hB_tmul (c d : K) (z q : V) :
              BK (c ⊗ₜ[ZMod 2] z) (d ⊗ₜ[ZMod 2] q) =
                (c * d) ⊗ₜ[ZMod 2] B z q := by
            exact LinearMap.BilinMap.baseChange_tmul B c z d q
          calc
            BK (TK (a ⊗ₜ[ZMod 2] v)) (TK (b ⊗ₜ[ZMod 2] w)) =
                BK (a ⊗ₜ[ZMod 2] T v) (b ⊗ₜ[ZMod 2] T w) := by
                  rw [hT_tmul, hT_tmul]
            _ = (a * b) ⊗ₜ[ZMod 2] B (T v) (T w) :=
              hB_tmul a b (T v) (T w)
            _ = (a * b) ⊗ₜ[ZMod 2] T (B v w) := by
              rw [hequivariant]
            _ = TK ((a * b) ⊗ₜ[ZMod 2] B v w) :=
              (hT_tmul (a * b) (B v w)).symm
            _ = TK (BK (a ⊗ₜ[ZMod 2] v) (b ⊗ₜ[ZMod 2] w)) := by
              rw [hB_tmul]
      | add y z hy hz =>
          simp only [map_add]
          rw [hy, hz]
  | add x z hx hz =>
      intro y
      simp only [map_add, LinearMap.add_apply]
      rw [hx y, hz y]

private theorem lemma4_singer_baseChange_span
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V)
    (hspan : Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2) = ⊤) :
    Submodule.span K
      (Set.range fun p : BC V × BC V =>
        LinearMap.BilinMap.baseChange K B p.1 p.2) = ⊤ := by
  let BK : BC V →ₗ[K] BC V →ₗ[K] BC V :=
    LinearMap.BilinMap.baseChange K B
  let S : Submodule K (BC V) :=
    Submodule.span K (Set.range fun p : BC V × BC V => BK p.1 p.2)
  change S = ⊤
  have hall : ∀ z : BC V, z ∈ S := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact S.zero_mem
    | add x y hx hy => exact S.add_mem hx hy
    | tmul a v =>
        have hv : v ∈ Submodule.span (ZMod 2)
            (Set.range fun p : V × V => B p.1 p.2) := by
          rw [hspan]
          exact Submodule.mem_top
        refine Submodule.span_induction
          (p := fun z _ => a ⊗ₜ[ZMod 2] z ∈ S) ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨⟨x, y⟩, rfl⟩
          apply Submodule.subset_span
          refine ⟨⟨a ⊗ₜ[ZMod 2] x, 1 ⊗ₜ[ZMod 2] y⟩, ?_⟩
          change BK (a ⊗ₜ[ZMod 2] x) (1 ⊗ₜ[ZMod 2] y) =
            a ⊗ₜ[ZMod 2] B x y
          calc
            BK (a ⊗ₜ[ZMod 2] x) (1 ⊗ₜ[ZMod 2] y) =
                (a * 1) ⊗ₜ[ZMod 2] B x y := by
                  exact LinearMap.BilinMap.baseChange_tmul B a x 1 y
            _ = a ⊗ₜ[ZMod 2] B x y := by rw [mul_one]
        · simpa only [TensorProduct.tmul_zero] using S.zero_mem
        · intro x y _ _ hx hy
          simpa only [TensorProduct.tmul_add] using S.add_mem hx hy
        · intro c x _ hx
          have h := S.smul_mem (algebraMap (ZMod 2) K c) hx
          simpa only [TensorProduct.tmul_smul, Algebra.smul_def,
            TensorProduct.smul_tmul', Algebra.algebraMap_self,
            RingHom.id_apply] using h
  apply top_unique
  intro z _
  exact hall z
private theorem lemma4_singer_distinct_binary_sum_bound
    (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    0 < 2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1 ∧
      2 ^ (i : ℕ) + 2 ^ (j : ℕ) - 1 < 2 ^ n - 1 := by
  have hsum_lt : 2 ^ (i : ℕ) + 2 ^ (j : ℕ) < 2 ^ n := by
    have hij_val : (i : ℕ) ≠ (j : ℕ) := by
      intro hval
      exact hij (Fin.ext hval)
    rcases lt_or_gt_of_ne hij_val with hij_lt | hji_lt
    · have hpow_lt : 2 ^ (i : ℕ) < 2 ^ (j : ℕ) :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 hij_lt
      have hnext :
          2 ^ (i : ℕ) + 2 ^ (j : ℕ) < 2 ^ ((j : ℕ) + 1) := by
        rw [pow_succ]
        omega
      have hle : 2 ^ ((j : ℕ) + 1) ≤ 2 ^ n :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 (by omega)
      exact lt_of_lt_of_le hnext hle
    · have hpow_lt : 2 ^ (j : ℕ) < 2 ^ (i : ℕ) :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 hji_lt
      have hnext :
          2 ^ (i : ℕ) + 2 ^ (j : ℕ) < 2 ^ ((i : ℕ) + 1) := by
        rw [pow_succ]
        omega
      have hle : 2 ^ ((i : ℕ) + 1) ≤ 2 ^ n :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 (by omega)
      exact lt_of_lt_of_le hnext hle
  have hi_pos : 0 < 2 ^ (i : ℕ) := pow_pos (by norm_num) _
  have hj_pos : 0 < 2 ^ (j : ℕ) := pow_pos (by norm_num) _
  have hn_pos : 0 < 2 ^ n := pow_pos (by norm_num) _
  constructor <;> omega

private theorem lemma4_singer_primitive_not_product
    (n : ℕ) (hn : 2 ≤ n) (lambda : K)
    (hlambda_order : orderOf lambda = 2 ^ n - 1) :
    ¬ ∃ i j : Fin n, i ≠ j ∧
      lambda = lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) := by
  rintro ⟨i, j, hij, hproduct⟩
  have horder_pos : 0 < 2 ^ n - 1 := by
    have hpow : 1 < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
    omega
  have hlambda_ne : lambda ≠ 0 := by
    intro hzero
    subst lambda
    simp at hlambda_order
    omega
  let s : ℕ := 2 ^ (i : ℕ) + 2 ^ (j : ℕ)
  have hs_bounds : 0 < s - 1 ∧ s - 1 < 2 ^ n - 1 := by
    simpa [s] using
      lemma4_singer_distinct_binary_sum_bound n i j hij
  have hproduct' : lambda = lambda ^ s := by
    simpa [s, ← pow_add] using hproduct
  have hs_decomp : s = (s - 1) + 1 := by omega
  have hcancel : lambda ^ (s - 1) * lambda = 1 * lambda := by
    calc
      lambda ^ (s - 1) * lambda = lambda ^ ((s - 1) + 1) :=
        (pow_succ lambda (s - 1)).symm
      _ = lambda ^ s := by rw [← hs_decomp]
      _ = lambda := hproduct'.symm
      _ = 1 * lambda := (one_mul lambda).symm
  have hpone : lambda ^ (s - 1) = 1 :=
    mul_right_cancel₀ hlambda_ne hcancel
  have hdvd : 2 ^ n - 1 ∣ s - 1 := by
    rw [← hlambda_order]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpone
  have hle : 2 ^ n - 1 ≤ s - 1 :=
    Nat.le_of_dvd hs_bounds.1 hdvd
  omega
private theorem lemma4_singer_no_alternating_surjection
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ x, x ≠ 0 → ∀ y, y ≠ 0 →
      ∃ k : ℕ, (T ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Nat.card V = 2 ^ n)
    (hT_order : orderOf T = 2 ^ n - 1)
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V)
    (halternating : ∀ v : V, B v v = 0)
    (hequivariant : ∀ v w : V, B (T v) (T w) = T (B v w)) :
    Submodule.span (ZMod 2)
      (Set.range fun p : V × V => B p.1 p.2) ≠ ⊤ := by
  intro hspan
  obtain ⟨lambda, basis, hlambda_order, hdiagonal⟩ :=
    lemma4_singer_eigenbasis T htrans n hn hcard hT_order
  let TK : Module.End K (BC V) := T.toLinearMap.baseChange K
  let BK : BC V →ₗ[K] BC V →ₗ[K] BC V :=
    LinearMap.BilinMap.baseChange K B
  have halternatingK : ∀ x : BC V, BK x x = 0 := by
    intro x
    simpa [BK] using lemma4_singer_baseChange_alternating B halternating x
  have hequivariant' :
      ∀ v w : V,
        B (T.toLinearMap v) (T.toLinearMap w) =
          T.toLinearMap (B v w) := by
    intro v w
    simpa using hequivariant v w
  have hequivariantK :
      ∀ x y : BC V, BK (TK x) (TK y) = TK (BK x y) := by
    intro x y
    simpa [TK, BK] using
      lemma4_singer_baseChange_equivariant T.toLinearMap B
        hequivariant' x y
  have hspanK :
      Submodule.span K
        (Set.range fun p : BC V × BC V => BK p.1 p.2) = ⊤ := by
    simpa [BK] using lemma4_singer_baseChange_span B hspan
  have hdiagonalK :
      ∀ i : Fin n,
        TK (basis i) = lambda ^ (2 ^ (i : ℕ)) • basis i := by
    intro i
    simpa [TK] using hdiagonal i
  let k0 : Fin n := ⟨0, by omega⟩
  obtain ⟨i, j, hij, hproduct⟩ :=
    lemma4_diagonal_alternating_span_forces_product
      TK basis (fun i : Fin n => lambda ^ (2 ^ (i : ℕ)))
      hdiagonalK BK halternatingK hequivariantK hspanK k0
  apply lemma4_singer_primitive_not_product n hn lambda hlambda_order
  refine ⟨i, j, hij, ?_⟩
  simpa [k0] using hproduct

end SingerScalarExtension

set_option linter.unusedVariables false in
/-- Higman Lemma 4 (Gorenstein--Thompson). The two spaces below are exactly
the source factors L₁ and L₂, with their canonical F₂-vector structures and
the actions induced by xi. -/
public theorem lemma4_gorenstein_thompson_nonisomorphic_factors
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n) :
    ¬ ∃ e : Additive (LowerCentralFactor H 0) ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1),
      ∀ v : Additive (LowerCentralFactor H 0),
        e (lowerCentralFactorLinearAut xi 0 v) =
          lowerCentralFactorLinearAut xi 1 (e v) := by
  rintro ⟨e, he⟩
  let V := Additive (LowerCentralFactor H 1)
  let T : V ≃ₗ[ZMod 2] V := lowerCentralFactorLinearAut xi 1
  let B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V :=
    { toFun := fun v =>
        (lemma4_lowerCentralBracket (e.symm v)).comp e.symm.toLinearMap
      map_add' := by
        intro v w
        ext z
        simp
      map_smul' := by
        intro c v
        ext z
        simp }
  have hV_card : Nat.card V = 2 ^ n :=
    (Nat.card_congr Additive.toMul).trans hL2_card
  have hT_order : orderOf T = 2 ^ n - 1 :=
    lemma4_transitive_linearAut_order T
      (by simpa [V, T] using hL2_transitive) n hn
      hV_card
  apply lemma4_singer_no_alternating_surjection T
    (by simpa [V, T] using hL2_transitive) n hn
    hV_card hT_order B
  · intro v
    simpa [B] using lemma4_lowerCentralBracket_self (e.symm v)
  · intro v w
    have hv :
        e.symm (T v) =
          lowerCentralFactorLinearAut xi 0 (e.symm v) := by
      apply e.injective
      simpa [T] using (he (e.symm v)).symm
    have hw :
        e.symm (T w) =
          lowerCentralFactorLinearAut xi 0 (e.symm w) := by
      apply e.injective
      simpa [T] using (he (e.symm w)).symm
    change lemma4_lowerCentralBracket (e.symm (T v)) (e.symm (T w)) =
      T (lemma4_lowerCentralBracket (e.symm v) (e.symm w))
    rw [hv, hw]
    exact lemma4_lowerCentralBracket_equivariant xi (e.symm v) (e.symm w)
  · have hrange :
        Set.range (fun p : V × V => B p.1 p.2) =
          Set.range (fun p :
            Additive (LowerCentralFactor H 0) ×
              Additive (LowerCentralFactor H 0) =>
            lemma4_lowerCentralBracket p.1 p.2) := by
      ext z
      constructor
      · rintro ⟨⟨v, w⟩, rfl⟩
        refine ⟨⟨e.symm v, e.symm w⟩, ?_⟩
        rfl
      · rintro ⟨⟨v, w⟩, rfl⟩
        refine ⟨⟨e v, e w⟩, ?_⟩
        simp [B]
    rw [hrange]
    exact lemma4_lowerCentralBracket_span

end Higman
end External
end CFSG.BenderSuzuki
