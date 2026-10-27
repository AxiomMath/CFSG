module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeCover
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCenter
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
import CFSG.OddTranspositions.PartFour.ThirteenThreeRefl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal Subgroup
open CFSG.OddStandard.SmallF3.Omega

private theorem toLinEquiv_refl_six {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (hsym : ∀ x y, f x y = f y x) {v : Fin 6 → ZMod 3} (hv : f v v = 1)
    [Invertible (LinearMap.BilinMap.toQuadraticMap f v)] :
    toLinEquiv (Fin 6) (ZMod 3) (F3.refl f v) =
      (TauCeti.QuadraticMap.reflectionOrthogonal (LinearMap.BilinMap.toQuadraticMap f) v :
        (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) := by
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  ext y
  rw [toLinEquiv_apply, ← F3.act_def, F3.act_refl hv, TauCeti.QuadraticMap.reflection_apply,
    LinearMap.BilinMap.polar_toQuadraticMap]
  have hinv : ⅟(LinearMap.BilinMap.toQuadraticMap f v) = 1 := by
    rw [invOf_eq_inv, LinearMap.BilinMap.toQuadraticMap_apply, hv, inv_one]
  rw [hinv, one_mul, hsym v y]
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (f y v * v _) * h3

theorem natCard_R3_six_minus_ge {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (hf : IsF3Form f)
    (hT : ¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f x x = 0) :
    6531840 ≤ Nat.card (R3 f) := by
  classical
  let Q : QuadraticForm (ZMod 3) (Fin 6 → ZMod 3) := LinearMap.BilinMap.toQuadraticMap f
  have hpolar : Q.polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hf.nondeg v
      fun w => by
        have := hv w
        rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm w v, ← two_mul] at this
        exact (mul_eq_zero.mp this).resolve_left (by decide)
  have hQ : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hpolar
  have hdim : Module.finrank (ZMod 3) (Fin 6 → ZMod 3) = 6 := Module.finrank_fin_fun (ZMod 3)
  have hno : ¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, Q x = 0 := by
    rintro ⟨T, hT3, hTQ⟩
    refine hT ⟨T, hT3, fun x hx => ?_⟩
    have := hTQ x hx
    rwa [LinearMap.BilinMap.toQuadraticMap_apply] at this
  have hplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    rintro ⟨W, hW, hWQ⟩
    exact hno ⟨W, by omega, hWQ⟩
  have hs : quadSign Q = -1 := by
    rcases Int.units_eq_one_or (quadSign Q) with h | h
    · exact absurd ((isPlusType_iff_quadSign_eq_one hQ (d := 3) (by rw [hdim])).mpr h) hplus
    · exact h
  have hΩcard : Nat.card (omegaGroup hQ) = 6531840 := natCard_omegaGroup_six_minus hQ hdim hs
  have hΩq : CFSG.IsQuasisimple (commutator (OGroup Q)) := by
    obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived (K := ZMod 3)
        (by rw [Nat.card_zmod]; decide) Q hpolar hdim hno
    exact hq
  have hle := f3ReflectionGroup_le_orthogonalGroup hf.symm (b := f) (n := 6)
  let R : Subgroup (OGroup Q) :=
    ((F3.reflGroup f).map (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup Q)
  have hΩR : omegaGroup hQ ≤ R := by
    rw [omegaGroup_eq_commutator hQ (by rw [hdim]; omega)]
    exact commutator_orthogonalGroup_le_reflGroup hf (by decide) hΩq
  let e : F3.reflGroup f ≃* R :=
    ((F3.reflGroup f).equivMapOfInjective _ (toLinEquiv (Fin 6) (ZMod 3)).injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm
  let Φ : omegaGroup hQ →* F3.reflGroup f :=
    e.symm.toMonoidHom.comp (Subgroup.inclusion hΩR)
  have hΦ : Function.Injective Φ :=
    e.symm.injective.comp (Subgroup.inclusion_injective hΩR)
  have hΦcoe : ∀ g : omegaGroup hQ,
      toLinEquiv (Fin 6) (ZMod 3) (Φ g : GL (Fin 6) (ZMod 3)) =
        ((g : OGroup Q) : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) := by
    intro g
    have h := e.apply_symm_apply (Subgroup.inclusion hΩR g)
    have hv := congrArg (fun x : R => ((x : OGroup Q) :
      (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3))) h
    change toLinEquiv (Fin 6) (ZMod 3)
      (e.symm (Subgroup.inclusion hΩR g) : GL (Fin 6) (ZMod 3)) = _ at hv
    exact hv
  obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by norm_num) (one_ne_zero (α := ZMod 3))
  have hnot : reflElt f v ∉ Φ.range := by
    rintro ⟨g, hg⟩
    have hQv : Q v = 1 := by
      change LinearMap.BilinMap.toQuadraticMap f v = 1
      rw [LinearMap.BilinMap.toQuadraticMap_apply, hv]
    let : Invertible (Q v) := invertibleOfNonzero (by rw [hQv]; decide)
    have hsub : (g : OGroup Q) = TauCeti.QuadraticMap.reflectionOrthogonal Q v := by
      apply Subtype.ext
      rw [← hΦcoe g, hg, coe_reflElt]
      exact toLinEquiv_refl_six hf.symm hv
    have hmem := (mem_omegaGroup_iff hQ).mp g.2
    rw [hsub, CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal] at hmem
    have h1 := congrArg Prod.fst hmem
    simp only [Prod.fst_one] at h1
    exact absurd h1 (by decide)
  have hR : 2 * 6531840 ≤ Nat.card (F3.reflGroup f) := by
    have h1 : Nat.card Φ.range = 6531840 := by
      rw [← hΩcard]; exact Nat.card_range_of_injective hΦ
    have hidx : Φ.range.index ≠ 1 := fun h =>
      hnot (by rw [Subgroup.index_eq_one.mp h]; trivial)
    have hidx0 : Φ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := Φ.range.card_mul_index
    rw [h1] at this
    have h2 : 2 ≤ Φ.range.index := by omega
    calc 2 * 6531840 ≤ Φ.range.index * 6531840 := Nat.mul_le_mul_right _ h2
      _ = Nat.card (F3.reflGroup f) := by rw [← this, mul_comm]
  have hZ : Nat.card (Subgroup.center (F3.reflGroup f)) ≤ 2 := by
    let ι : Subgroup.center (F3.reflGroup f) → GL (Fin 6) (ZMod 3) := fun z => (z : F3.reflGroup f)
    have hinj : Function.Injective ι := fun a b h => Subtype.ext (Subtype.ext h)
    have hsub : Set.range ι ⊆ ({1, -1} : Set (GL (Fin 6) (ZMod 3))) := by
      rintro _ ⟨z, rfl⟩
      rcases F3.coe_eq_of_mem_center hf (by norm_num) z.2 with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Nat.card (Subgroup.center (F3.reflGroup f)) = Nat.card (Set.range ι) :=
          (Nat.card_range_of_injective hinj).symm
      _ ≤ Nat.card ({1, -1} : Set (GL (Fin 6) (ZMod 3))) := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
          rw [Nat.card_coe_set_eq]
          exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (F3.reflGroup f))
  change Nat.card (F3.reflGroup f) = Nat.card (R3 f) * _ at hcard
  nlinarith

end CFSG.OddTranspositions.PartFour
