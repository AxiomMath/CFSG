module

public import CFSG.Sporadic.Schreier.RuElemAut
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.LinearAlgebra.Matrix.Action

public noncomputable section

open Matrix
open scoped MatrixGroups

namespace CFSG.GroupTheory.NormalizerLinearCoordinates

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local notation "F" => ZMod 5

local instance (priority := 2000) : AddCommGroup F :=
  (inferInstance : Field F).toAddCommGroup

local notation "V3" => Fin 3 → F

section Generic

variable {G : Type*} [Group G]
variable (E : Subgroup G)
variable (e : E ≃* Multiplicative V3)

@[expose] def rho : Subgroup.normalizer (E : Set G) →* GL (Fin 3) F :=
  (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 5) 3).toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp E.normalizerMonoidHom)

@[expose] def H : Subgroup (GL (Fin 3) F) := (rho E e).range

theorem rho_mulVec (n : Subgroup.normalizer (E : Set G)) (x : E) :
    ((rho E e n : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (e x).toAdd =
      (e (E.normalizerMonoidHom n x)).toAdd := by
  have hcoord (α : MulAut (Multiplicative V3)) (v : V3) :
      ((CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 5) 3 α :
          GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
        Multiplicative.toAdd (α (Multiplicative.ofAdd v)) := by
    have h := congrArg
      (fun L : LinearMap.GeneralLinearGroup (ZMod 5) (Fin 3 → ZMod 5) =>
        (L : (Fin 3 → ZMod 5) →ₗ[ZMod 5] (Fin 3 → ZMod 5)) v)
      (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 5) (Fin 3 → ZMod 5)).symm
          (CFSG.Sporadic.RuSchreier.ruAddAutEquivLinear (p := 5) (Fin 3 → ZMod 5)
            (MulAutMultiplicative (Fin 3 → ZMod 5) α))))
    simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply] at h
    exact h
  unfold rho
  change ((CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 5) 3
      ((MulAut.congr e) (E.normalizerMonoidHom n)) :
        GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (e x).toAdd =
    (e (E.normalizerMonoidHom n x)).toAdd
  rw [hcoord]
  simp [MulAut.congr_apply, MulEquiv.symm_apply_apply]

@[expose] def phi : MulAut E ≃* GL (Fin 3) F :=
  (MulAut.congr e).trans (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 5) 3)

theorem H_eq_map_range :
    H E e = (E.normalizerMonoidHom.range).map (phi E e).toMonoidHom := by
  unfold H rho phi
  simp only [MonoidHom.range_comp, Subgroup.map_map]
  rfl

@[expose] def rangeEquiv :
    E.normalizerMonoidHom.range ≃* H E e :=
  (MulEquiv.subgroupMap (phi E e) E.normalizerMonoidHom.range).trans
    (MulEquiv.subgroupCongr (H_eq_map_range E e).symm)

theorem isPerfect_normalizer_range_of_isPerfect_H
    (hH : Group.IsPerfect (H E e)) :
    Group.IsPerfect E.normalizerMonoidHom.range :=
  @Group.IsPerfect.ofSurjective (H E e) E.normalizerMonoidHom.range _ _
    (rangeEquiv E e).symm.toMonoidHom hH (rangeEquiv E e).symm.surjective

@[expose] def stdBasis (i : Fin 3) : V3 := Pi.single i 1

@[expose] def coordTarget (M : GL (Fin 3) F) (i : Fin 3) : E :=
  e.symm (Multiplicative.ofAdd (M *ᵥ stdBasis i))

theorem mem_normalizer_of_conj_generators
    (x : Fin 3 → E) (M : GL (Fin 3) F) (g : G)
    (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hconj : ∀ i, g * (x i : G) * g⁻¹ = ((coordTarget E e M i : E) : G)) :
    g ∈ Subgroup.normalizer (E : Set G) := by
  classical
  have hfin : Finite E :=
    @Finite.of_fintype E (Fintype.ofEquiv (Multiplicative V3) e.symm.toEquiv)
  have hgen_mem : ∀ z ∈ Set.range x, (MulAut.conj g) (z : G) ∈ E := by
    rintro z ⟨i, rfl⟩
    rw [MulAut.conj_apply, hconj i]
    exact (coordTarget E e M i).2
  have hclosure : ∀ y : E, (MulAut.conj g) (y : G) ∈ E := by
    intro y
    have hy : y ∈ Subgroup.closure (Set.range x) := by
      rw [hgen]
      exact Subgroup.mem_top y
    refine Subgroup.closure_induction'' (s := Set.range x)
      (p := fun z _ => (MulAut.conj g) (z : G) ∈ E) ?_ ?_ ?_ ?_ hy
    · exact hgen_mem
    · intro z hz
      have hzE : (MulAut.conj g) (z : G) ∈ E := hgen_mem z hz
      simpa [map_inv] using E.inv_mem hzE
    · simp
    · intro a b _ _ ha hb
      simpa [map_mul] using E.mul_mem ha hb
  have hmap_le : E.map (MulAut.conj g).toMonoidHom ≤ E := by
    rintro y ⟨z, hzE, rfl⟩
    exact hclosure ⟨z, hzE⟩
  have hmap_eq : E.map (MulAut.conj g).toMonoidHom = E := by
    refine @Subgroup.eq_of_le_of_card_ge G _
      (E.map (MulAut.conj g).toMonoidHom) E hfin hmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap_eq

theorem rho_eq_of_conj_generators
    (x : Fin 3 → E) (M : GL (Fin 3) F) (g : G)
    (hx : ∀ i, e (x i) = Multiplicative.ofAdd (stdBasis i))
    (hg : g ∈ Subgroup.normalizer (E : Set G))
    (hconj : ∀ i, g * (x i : G) * g⁻¹ = ((coordTarget E e M i : E) : G)) :
    rho E e ⟨g, hg⟩ = M := by
  classical
  let n : Subgroup.normalizer (E : Set G) := ⟨g, hg⟩
  have hnorm (i : Fin 3) : E.normalizerMonoidHom n (x i) = coordTarget E e M i := by
    apply Subtype.ext
    change g * (x i : G) * g⁻¹ = ((coordTarget E e M i : E) : G)
    exact hconj i
  have hcol (i : Fin 3) :
      ((rho E e n : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ stdBasis i =
        M *ᵥ stdBasis i := by
    have h := rho_mulVec E e n (x i)
    rw [hx i, hnorm i] at h
    simpa [coordTarget, stdBasis] using h
  ext i j
  have h := congrFun (hcol j) i
  simpa [stdBasis, Matrix.mulVec_single_one] using h

theorem exists_normalizer_rho_eq_of_conj_generators
    (x : Fin 3 → E) (M : GL (Fin 3) F) (g : G)
    (hx : ∀ i, e (x i) = Multiplicative.ofAdd (stdBasis i))
    (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hconj : ∀ i, g * (x i : G) * g⁻¹ = ((coordTarget E e M i : E) : G)) :
    ∃ hg : g ∈ Subgroup.normalizer (E : Set G),
      rho E e ⟨g, hg⟩ = M := by
  have hg := mem_normalizer_of_conj_generators E e x M g hgen hconj
  exact ⟨hg, rho_eq_of_conj_generators E e x M g hx hg hconj⟩

end Generic

end CFSG.GroupTheory.NormalizerLinearCoordinates
