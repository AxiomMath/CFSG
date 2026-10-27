module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IOrd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutSeven
import CFSG.OddTranspositions.PartFour.ThirteenThreeRefl
import CFSG.OddTranspositions.PartFour.ThirteenListThreeRefl

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal Subgroup
open CFSG.OddStandard.SmallF3.Omega
open CFSG.ClassicalInvolution TauCeti CliffordAlgebra

theorem natCard_R3_seven_ge {f : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3)}
    (hf : IsF3Form f) : 4585351680 ≤ Nat.card (R3 f) := by
  let Q : QuadraticForm (ZMod 3) (Fin 7 → ZMod 3) := LinearMap.BilinMap.toQuadraticMap f
  have hpolar : Q.polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hf.nondeg v
      fun w => by
        have := hv w
        rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm w v, ← two_mul] at this
        exact (mul_eq_zero.mp this).resolve_left (by decide)
  have hQ : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hpolar
  have hdim : Module.finrank (ZMod 3) (Fin 7 → ZMod 3) = 7 := Module.finrank_fin_fun (ZMod 3)
  have hΩq : CFSG.IsQuasisimple (commutator (OGroup Q)) := by
    rw [← omegaGroup_eq_commutator hQ (by rw [hdim]; omega)]
    exact isQuasisimple_omegaGroup_seven hQ hdim
  have hle := f3ReflectionGroup_le_orthogonalGroup hf.symm (b := f)
  let R : Subgroup (OGroup Q) :=
    ((F3.reflGroup f).map (toLinEquiv (Fin 7) (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q)
  have hΩR : omegaGroup hQ ≤ R := by
    rw [omegaGroup_eq_commutator hQ (by rw [hdim]; omega)]
    exact commutator_orthogonalGroup_le_reflGroup hf (by decide) hΩq
  let e : F3.reflGroup f ≃* R :=
    ((F3.reflGroup f).equivMapOfInjective _ (toLinEquiv (Fin 7) (ZMod 3)).injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm
  let Φ : omegaGroup hQ →* F3.reflGroup f :=
    e.symm.toMonoidHom.comp (Subgroup.inclusion hΩR)
  have hΦ : Function.Injective Φ :=
    e.symm.injective.comp (Subgroup.inclusion_injective hΩR)
  have hΦcoe : ∀ g : omegaGroup hQ,
      toLinEquiv (Fin 7) (ZMod 3) (Φ g : GL (Fin 7) (ZMod 3)) =
        ((g : OGroup Q) : (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3)) := by
    intro g
    have h := e.apply_symm_apply (Subgroup.inclusion hΩR g)
    have hv := congrArg (fun x : R => ((x : OGroup Q) :
      (Fin 7 → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))) h
    change toLinEquiv (Fin 7) (ZMod 3)
      (e.symm (Subgroup.inclusion hΩR g) : GL (Fin 7) (ZMod 3)) = _ at hv
    exact hv
  have hne : ∀ g, (Φ g : GL (Fin 7) (ZMod 3)) ≠ -1 := by
    intro g hg
    have hpi : (g : OGroup Q) = piOrth Q := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      have h := congrArg (fun u => u x) (hΦcoe g)
      rw [hg, toLinEquiv_apply, ← F3.act_def, F3.act_neg_one] at h
      rw [coe_piOrth_apply]
      exact h.symm
    exact piOrth_not_mem_omegaGroup_seven hQ hdim (hpi ▸ g.2)
  have hinj := injective_mk_comp_reflGroup (by decide) hf hΦ hne
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [natCard_omegaGroup_seven hQ hdim] at hcard
  exact hcard

theorem toLinEquiv_refl_toQuadraticMap {n : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)} (hf : IsF3Form f)
    {v : Fin n → ZMod 3} (hv : f v v = 1) :
    toLinEquiv (Fin n) (ZMod 3) (F3.refl f v) =
      reflect (LinearMap.BilinMap.toQuadraticMap f) v := by
  refine LinearEquiv.ext fun x => ?_
  rw [toLinEquiv_apply, ← F3.act_def, F3.act_refl hv,
    reflect_apply (by simpa [LinearMap.BilinMap.toQuadraticMap_apply] using (by rw [hv]; decide : f v v ≠ 0)),
    LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.BilinMap.toQuadraticMap_apply, hv,
    hf.symm, div_one, ← two_mul]
  have htwo : (2 : ZMod 3) = -1 := by decide
  rw [htwo, neg_one_mul, neg_smul, sub_neg_eq_add]

theorem natCard_reflGroup_seven_le {f : LinearMap.BilinForm (ZMod 3) (Fin 7 → ZMod 3)}
    (hf : IsF3Form f) : Nat.card (F3.reflGroup f) ≤ 9170703360 := by
  classical
  let Q : QuadraticForm (ZMod 3) (Fin 7 → ZMod 3) := LinearMap.BilinMap.toQuadraticMap f
  have hpolar : Q.polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hf.nondeg v
      fun w => by
        have := hv w
        rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm w v, ← two_mul] at this
        exact (mul_eq_zero.mp this).resolve_left (by decide)
  have hQ : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hpolar
  have hdim : Module.finrank (ZMod 3) (Fin 7 → ZMod 3) = 7 := Module.finrank_fin_fun _
  have hle := f3ReflectionGroup_le_orthogonalGroup hf.symm (b := f)
  let R : Subgroup (OGroup Q) :=
    ((F3.reflGroup f).map (toLinEquiv (Fin 7) (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q)
  have hspin : R ≤ (orthogonalSpinorNorm Q hQ).ker := by
    have htarget : (F3.reflGroup f).map (toLinEquiv (Fin 7) (ZMod 3)).toMonoidHom ≤
        ((orthogonalSpinorNorm Q hQ).ker).map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      obtain ⟨v, hv, rfl⟩ := F3.mem_reflSet_iff.mp hg
      have hvQ : Q v = 1 := hv
      let : Invertible (Q v) := invertibleOfNonzero (by rw [hvQ]; exact one_ne_zero)
      refine ⟨TauCeti.QuadraticMap.reflectionOrthogonal Q v, ?_, ?_⟩
      · change orthogonalSpinorNorm Q hQ (TauCeti.QuadraticMap.reflectionOrthogonal Q v) = 1
        rw [orthogonalSpinorNorm_reflectionOrthogonal]
        have hu : unitOfInvertible (Q v) = (1 : (ZMod 3)ˣ) := Units.ext (by simp [hvQ])
        rw [hu, map_one]
      · change ((TauCeti.QuadraticMap.reflectionOrthogonal Q v) : _) =
          toLinEquiv (Fin 7) (ZMod 3) (F3.refl f v)
        rw [toLinEquiv_refl_toQuadraticMap hf hv, reflect_eq_reflection,
          QuadraticMap.coe_reflectionOrthogonal]
    intro r hr
    obtain ⟨u, hu, he⟩ := htarget hr
    have hur : u = r := Subtype.ext he
    exact hur ▸ hu
  have hproper : (orthogonalSpinorNorm Q hQ).ker ≠ ⊤ := by
    obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by decide) (by decide : (-1 : ZMod 3) ≠ 0)
    have hvQ : Q v = -1 := hv
    let : Invertible (Q v) := invertibleOfNonzero (by rw [hvQ]; decide)
    intro htop
    have hmem : TauCeti.QuadraticMap.reflectionOrthogonal Q v ∈ (orthogonalSpinorNorm Q hQ).ker :=
      htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, orthogonalSpinorNorm_reflectionOrthogonal] at hmem
    have hu : unitOfInvertible (Q v) = (-1 : (ZMod 3)ˣ) := Units.ext (by simp [hvQ])
    rw [hu, squareClassHom_apply] at hmem
    exact aux_squareClass_neg_one_ne_zero (congrArg Multiplicative.toAdd hmem)
  have hindex := Subgroup.one_lt_index_of_ne_top hproper
  have hcard := (orthogonalSpinorNorm Q hQ).ker.card_mul_index
  rw [natCard_oGroup_seven hQ hdim] at hcard
  let e : F3.reflGroup f ≃* R :=
    ((F3.reflGroup f).equivMapOfInjective _ (toLinEquiv (Fin 7) (ZMod 3)).injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm
  have hr := Subgroup.card_le_of_le hspin
  rw [Nat.card_congr e.toEquiv]
  nlinarith


end CFSG.OddTranspositions.PartFour
