module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8Minus
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Matrix

@[expose] noncomputable def o8LinEquiv (K : Type) [Field K] (b c : K) :
    (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) ≃ₗ[K] T3V K :=
  (minusTailIsometry 4 K b c).symm.toLinearEquiv

@[expose] noncomputable def o8ModEquiv (K : Type) [Field K] (b c : K) :
    CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K ≃* Multiplicative (T3V K) :=
  (o8LinEquiv K b c).toAddEquiv.toMultiplicative

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

private theorem o8ModEquiv_symm_ofAdd_H12 (v : T3V K) :
    (o8ModEquiv K b c).symm (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd ((minusTailIsometry 4 K b c) v) :=
  rfl

private theorem matHom_ofAdd_eq_H12 (g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
    (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    CFSG.Quasithin.H.matHom g (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd
        ((g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ w) :=
  rfl

private theorem o8ModEquiv_ofAdd_H12 (w : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K) :
    o8ModEquiv K b c (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd ((minusTailIsometry 4 K b c).symm w) :=
  rfl

private theorem map_natImage_eq_of_hhom_H12
    (φ : ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))))
    (hhom : ∀ g : ↥(StatedOmega (StatedQuadMinus 4 K b c)),
      (CFSG.Quasithin.H.congrHom (o8ModEquiv K b c))
          (CFSG.Quasithin.H.matHom
            ((StatedOmega (StatedQuadMinus 4 K b c)).subtype g)) =
        linMulAut8 ((φ g).val)) :
    (CFSG.Quasithin.H.natImage
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))).map
        (CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)) = T3H K b c := by
  have hcomp : ((CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)).comp
        CFSG.Quasithin.H.matHom).comp (StatedOmega (StatedQuadMinus 4 K b c)).subtype =
      (linMulAut8.comp
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))).subtype).comp
        φ.toMonoidHom :=
    MonoidHom.ext fun g => hhom g
  have hF : (StatedOmega (StatedQuadMinus 4 K b c)).map
      ((CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)).comp CFSG.Quasithin.H.matHom) =
      ((((CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)).comp
        CFSG.Quasithin.H.matHom).comp (StatedOmega (StatedQuadMinus 4 K b c)).subtype).range) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hG : (((linMulAut8.comp
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))).subtype).comp
        φ.toMonoidHom).range) =
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c))).map linMulAut8 := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective φ.toMonoidHom (fun x => φ.surjective x),
      Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  calc
    (CFSG.Quasithin.H.natImage (StatedOmega (StatedQuadMinus 4 K b c))).map
        (CFSG.Quasithin.H.congrHom (o8ModEquiv K b c))
      = ((StatedOmega (StatedQuadMinus 4 K b c)).map CFSG.Quasithin.H.matHom).map
          (CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)) := by
        rw [CFSG.Quasithin.H.natImage_eq_map]
    _ = (StatedOmega (StatedQuadMinus 4 K b c)).map
          ((CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)).comp
            CFSG.Quasithin.H.matHom) := by
        rw [Subgroup.map_map]
    _ = ((((CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)).comp
          CFSG.Quasithin.H.matHom).comp
          (StatedOmega (StatedQuadMinus 4 K b c)).subtype).range) := hF
    _ = (((linMulAut8.comp
          (orthElementaryGroup (quadTail 3 (minusTailForm K b c))).subtype).comp
          φ.toMonoidHom).range) := by rw [hcomp]
    _ = (orthElementaryGroup (quadTail 3 (minusTailForm K b c))).map linMulAut8 := hG
    _ = T3H K b c := rfl

theorem map_natImage_o8ModEquiv (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (CFSG.Quasithin.H.natImage
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))).map
        (CFSG.Quasithin.H.congrHom (o8ModEquiv K b c)) = T3H K b c := by
  have hE := CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
    (n := 4) (b := b) (c := c) (by norm_num) hirr
  have hQ := CFSG.LieType.Universal.Spin.coe_quadMinus (n := 4) (K := K) b c
  let ψ := minusTailIsometry 4 K b c
  let φ : ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :=
    tailOmegaEquiv ψ hQ hE
  refine map_natImage_eq_of_hhom_H12 φ ?_
  intro g
  refine MulEquiv.ext fun x => ?_
  induction x using Multiplicative.rec with
  | ofAdd v =>
    rw [CFSG.Quasithin.H.congrHom_apply, o8ModEquiv_symm_ofAdd_H12, matHom_ofAdd_eq_H12,
      o8ModEquiv_ofAdd_H12, linMulAut8_apply_ofAdd]
    rw [show (φ g).val v = (minusTailIsometry 4 K b c).symm
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K
          ((StatedOmega (StatedQuadMinus 4 K b c)).subtype g)
          ((minusTailIsometry 4 K b c) v)) from
      tailOmegaEquiv_apply ψ hQ hE g v]
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]

theorem omegaMinus8Natural_of_t3H (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (h : OmegaMinus8Line (Multiplicative (T3V K)) (T3H K b c) m) :
    OmegaMinus8Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
      (CFSG.Quasithin.H.natImage
        (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) m :=
  omegaMinus8Line_of_map_congr
    (CFSG.Quasithin.H.natImage
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) (T3H K b c) m
    (o8ModEquiv K b c) (map_natImage_o8ModEquiv hirr).symm h

end CFSG.LocalAnalysis.UniquenessCase.UC22.O8Levi
