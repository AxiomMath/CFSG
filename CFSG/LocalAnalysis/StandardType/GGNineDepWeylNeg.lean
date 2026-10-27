module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
import Mathlib.LinearAlgebra.Basis.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggNineDepWeylNegAux_piSingle_apply {n : ℕ} (j r : Fin n) :
    (Pi.single j 1 : Fin n → ZMod 3) r = if r = j then 1 else 0 := by
  by_cases h : r = j
  · rw [h, if_pos rfl, Pi.single_eq_same]
  · rw [if_neg h, Pi.single_eq_of_ne h]

private noncomputable def ggNineDepWeylNegAux_matE {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (ZMod 3)) (i : Fin n) :
    Matrix (Fin n) (Fin n) (ZMod 3) :=
  Matrix.of fun r c => if r = i then (if c = i then 1 else 0) - C i c
    else if r = c then 1 else 0

private noncomputable def ggNineDepWeylNegAux_matWord {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (ZMod 3)) : Matrix (Fin n) (Fin n) (ZMod 3) :=
  ((List.finRange n).map (ggNineDepWeylNegAux_matE C)).prod

private theorem ggNineDepWeylNegAux_matE_mulVec_single {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (ZMod 3)) (i j : Fin n) :
    ggNineDepWeylNegAux_matE C i *ᵥ (Pi.single j 1 : Fin n → ZMod 3) =
      Pi.single j 1 - (C i j) • (Pi.single i 1 : Fin n → ZMod 3) := by
  rw [Matrix.mulVec_single_one]
  funext r
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ggNineDepWeylNegAux_piSingle_apply j r, ggNineDepWeylNegAux_piSingle_apply i r]
  simp only [ggNineDepWeylNegAux_matE, Matrix.col_apply]
  split_ifs <;> simp_all [eq_comm]

private theorem ggNineDepWeylNegAux_list_prod_mem {G : Type*} [Group G] (S : Subgroup G)
    {L : List G} (h : ∀ g ∈ L, g ∈ S) : L.prod ∈ S := by
  induction L with
  | nil => exact S.one_mem
  | cons a L ih =>
      rw [List.prod_cons]
      exact S.mul_mem (h a (by simp)) (ih fun g hg => h g (by simp [hg]))

private theorem ggNineDepWeylNegAux_neg_mem {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {n : ℕ} (z : Fin n → U) (β : Fin n → Module.Dual (ZMod 3) U)
    (hz : LinearIndependent (ZMod 3) z)
    (hspan : Submodule.span (ZMod 3) (Set.range z) = ⊤)
    (C : Matrix (Fin n) (Fin n) (ZMod 3))
    (hC : ∀ i, C i i = 2)
    (hpair : ∀ i j, β i (z j) = C i j)
    (k : ℕ)
    (hmat : ggNineDepWeylNegAux_matWord C ^ k =
      (-1 : Matrix (Fin n) (Fin n) (ZMod 3))) :
    (LinearEquiv.neg (ZMod 3) : U ≃ₗ[ZMod 3] U) ∈ ggQ2WeylOf z β := by
  let b : Basis (Fin n) (ZMod 3) U := Basis.mk hz (by rw [hspan])
  let φ : U ≃ₗ[ZMod 3] (Fin n → ZMod 3) := b.equivFun
  let s : Fin n → U ≃ₗ[ZMod 3] U := fun i =>
    Module.reflection (x := z i) (f := β i) (by rw [hpair i i, hC i])
  have hbz : ∀ j, b j = z j := fun j => Basis.mk_apply hz _ j
  have hs_apply : ∀ i v, s i v = v - β i v • z i := fun i v => by
    rw [show s i = Module.reflection (x := z i) (f := β i) (by rw [hpair i i, hC i]) from rfl,
      Module.reflection_apply]
  have hs_mem : ∀ i, s i ∈ ggQ2WeylOf z β := fun i =>
    Subgroup.subset_closure ⟨i, fun v => hs_apply i v⟩
  have hφ_single : ∀ j, φ (z j) = (Pi.single j 1 : Fin n → ZMod 3) := fun j => by
    have h1 : φ (z j) = b.equivFun (b j) := by rw [hbz j]
    rw [h1]
    ext r
    rw [ggNineDepWeylNegAux_piSingle_apply j r, Basis.equivFun_self]
    by_cases h : j = r
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  have hφ_apply : ∀ i v, φ (s i v) = ggNineDepWeylNegAux_matE C i *ᵥ (φ v) := by
    intro i v
    have hlm : (φ : U →ₗ[ZMod 3] (Fin n → ZMod 3)).comp (s i : U →ₗ[ZMod 3] U) =
        (Matrix.mulVecLin (ggNineDepWeylNegAux_matE C i)).comp
          (φ : U →ₗ[ZMod 3] (Fin n → ZMod 3)) := by
      refine Basis.ext (b := b) fun j => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.mulVecLin_apply]
      change φ (s i (b j)) = ggNineDepWeylNegAux_matE C i *ᵥ (φ (b j))
      rw [hbz j, hs_apply, map_sub, map_smul, hpair i j, hφ_single i, hφ_single j,
        ggNineDepWeylNegAux_matE_mulVec_single]
    exact congrArg (fun f : U →ₗ[ZMod 3] (Fin n → ZMod 3) => f v) hlm
  let c : U ≃ₗ[ZMod 3] U := ((List.finRange n).map s).prod
  have hc_mem : c ∈ ggQ2WeylOf z β := by
    refine ggNineDepWeylNegAux_list_prod_mem _ (fun g hg => ?_)
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact hs_mem i
  have hbridge : ∀ L : List (Fin n), ∀ v,
      φ (((L.map s).prod) v) =
        ((L.map (ggNineDepWeylNegAux_matE C)).prod) *ᵥ (φ v) := by
    intro L
    induction L with
    | nil => intro v; simp [Matrix.one_mulVec]
    | cons a L ih =>
        intro v
        rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, hφ_apply, ih,
          Matrix.mulVec_mulVec, List.map_cons, List.prod_cons]
  have hc0 : ∀ v, φ (c v) = ggNineDepWeylNegAux_matWord C *ᵥ (φ v) := fun v => by
    rw [show c = ((List.finRange n).map s).prod from rfl, hbridge (List.finRange n) v,
      ← show ggNineDepWeylNegAux_matWord C =
        ((List.finRange n).map (ggNineDepWeylNegAux_matE C)).prod from rfl]
  have hcpow : ∀ m v,
      φ ((c ^ m) v) = (ggNineDepWeylNegAux_matWord C ^ m) *ᵥ (φ v) := by
    intro m
    induction m with
    | zero => intro v; simp [Matrix.one_mulVec]
    | succ m ih =>
        intro v
        rw [pow_succ, LinearEquiv.mul_apply, ih, hc0, Matrix.mulVec_mulVec, pow_succ]
  have hneg : c ^ k = (LinearEquiv.neg (ZMod 3) : U ≃ₗ[ZMod 3] U) := by
    apply LinearEquiv.ext
    intro v
    apply φ.injective
    have h := hcpow k v
    rw [hmat, Matrix.neg_mulVec, Matrix.one_mulVec] at h
    rw [LinearEquiv.neg_apply, map_neg, h]
  rw [← hneg]
  exact Subgroup.pow_mem (ggQ2WeylOf z β) hc_mem k

theorem ggQ2WeylOf_neg_mem_E7 {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (z : Fin 7 → U) (β : Fin 7 → Module.Dual (ZMod 3) U) (hz : LinearIndependent (ZMod 3) z)
    (hspan : Submodule.span (ZMod 3) (Set.range z) = ⊤)
    (hpair : ∀ i j, β i (z j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3)) :
    (LinearEquiv.neg (ZMod 3) : U ≃ₗ[ZMod 3] U) ∈ ggQ2WeylOf z β := by
  refine ggNineDepWeylNegAux_neg_mem z β hz hspan
    ((CartanMatrix.E 7).map (Int.castRingHom (ZMod 3))) (fun j => by simp) hpair 9 ?_
  decide +kernel

theorem ggQ2WeylOf_neg_mem_E8 {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (z : Fin 8 → U) (β : Fin 8 → Module.Dual (ZMod 3) U) (hz : LinearIndependent (ZMod 3) z)
    (hspan : Submodule.span (ZMod 3) (Set.range z) = ⊤)
    (hpair : ∀ i j, β i (z j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) :
    (LinearEquiv.neg (ZMod 3) : U ≃ₗ[ZMod 3] U) ∈ ggQ2WeylOf z β := by
  refine ggNineDepWeylNegAux_neg_mem z β hz hspan
    ((CartanMatrix.E 8).map (Int.castRingHom (ZMod 3))) (fun j => by simp) hpair 15 ?_
  decide +kernel

end CFSG.StandardType

end
