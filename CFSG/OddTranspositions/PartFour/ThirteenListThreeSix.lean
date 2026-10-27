module

public import CFSG.Fischer.Classification.Orthogonal3.Refl
public import CFSG.Blueprint.Catalog
import CFSG.OddTranspositions.PartFour.ThirteenListThreeCenter
import CFSG.OddTranspositions.PartFour.ThirteenThreeRefl
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh
import CFSG.Timmesfeld.Bridge.Asc72YCount
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddTranspositions.PartFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Fischer.Classification CFSG.ClassicalGroups.Orthogonal

private theorem map_commutator_of_surjective {G H : Type*} [Group G] [Group H] {φ : G →* H}
    (hφ : Function.Surjective φ) : (commutator G).map φ = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ]

private theorem exists_ne_comm_of_isPerfect {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : Group.IsPerfect K) : ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hbot : commutator K = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  obtain ⟨a, b, hab⟩ := exists_pair_ne K
  have ha : a ∈ commutator K := by rw [hK.commutator_eq_top]; exact Subgroup.mem_top a
  have hb : b ∈ commutator K := by rw [hK.commutator_eq_top]; exact Subgroup.mem_top b
  rw [hbot, Subgroup.mem_bot] at ha hb
  exact hab (ha.trans hb.symm)

section Split

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}

theorem commutator_reflGroup_six_split (hf : IsF3Form f)
    (hT : ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f x x = 0) :
    CFSG.IsQuasisimple ↥(commutator ↥(F3.reflGroup f)) ∧
      CFSG.Blueprint.LieModel (↥(commutator ↥(F3.reflGroup f)) ⧸
        Subgroup.center ↥(commutator ↥(F3.reflGroup f))) .PSL 4 3 1 := by
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hQ : (LinearMap.BilinMap.toQuadraticMap f).polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hf.nondeg v
      fun w => by
        have := hv w
        rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm w v, ← two_mul] at this
        exact (mul_eq_zero.mp this).resolve_left h2
  obtain ⟨T, hT3, hTf⟩ := hT
  have hTQ : ∀ x ∈ T, LinearMap.BilinMap.toQuadraticMap f x = 0 := fun x hx => by
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    exact hTf x hx
  have hΩq : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f))) :=
    CFSG.ComponentClassification.CatalogueBOrthogonal.derived_quasisimple _ h2 hQ hT3.ge hTQ
  have hΩc : CFSG.IsComponent (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f))) :=
    ⟨hΩq, (inferInstance : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f))).Normal).isSubnormal⟩
  have hCM := CFSG.ComponentClassification.CatLeafProof.X10Lin.centralModel_orthogonal_split_six
    (k := ZMod 3) Nat.prime_three (by decide) le_rfl (by rw [Nat.card_zmod]; norm_num) _ hQ
    (by rw [Module.finrank_fin_fun]) ⟨T, hT3, hTQ⟩ hΩc
  have hle := f3ReflectionGroup_le_orthogonalGroup hf.symm (b := f) (n := 6)
  have hRn : (((F3.reflGroup f).map (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact conj_mem_f3ReflectionGroup hf.symm g.2 hx⟩
  have : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) :=
    Finite.of_injective (fun g => (toLinEquiv (Fin 6) (ZMod 3)).symm g.1)
      (fun a b h => Subtype.ext ((toLinEquiv (Fin 6) (ZMod 3)).symm.injective h))
  have hΩR : commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f)) ≤
      ((F3.reflGroup f).map (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) := by
    rcases CFSG.LocalCores.component_normal_subgroup hΩc hRn with h | h
    · exact h
    exfalso
    have hpm : ∀ x ∈ commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
        (LinearMap.BilinMap.toQuadraticMap f)),
        (toLinEquiv (Fin 6) (ZMod 3)).symm (x : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) = 1 ∨
          (toLinEquiv (Fin 6) (ZMod 3)).symm
            (x : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)) = -1 := by
      intro x hx
      set g := (toLinEquiv (Fin 6) (ZMod 3)).symm (x : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] _) with hg
      have hgx : toLinEquiv (Fin 6) (ZMod 3) g = x := MulEquiv.apply_symm_apply _ _
      have hiso : F3.IsIsom f g := fun a b => by
        rw [F3.act_def, F3.act_def, ← toLinEquiv_apply, ← toLinEquiv_apply, hgx]
        exact bilin_map_of_mem_orthogonalGroup_three hf.symm x.2 a b
      refine F3.eq_one_or_eq_neg_one hf (by norm_num) hiso fun v hv =>
        F3.act_eq_or_of_commute hiso hv ?_
      have hrO : toLinEquiv (Fin 6) (ZMod 3) (F3.refl f v) ∈
          TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f) :=
        hle ⟨F3.refl f v, F3.refl_mem_reflGroup v, rfl⟩
      have hrR : (⟨_, hrO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup
          (LinearMap.BilinMap.toQuadraticMap f))) ∈
          ((F3.reflGroup f).map (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
            (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) :=
        Subgroup.mem_subgroupOf.mpr ⟨F3.refl f v, F3.refl_mem_reflGroup v, rfl⟩
      have hc := Subgroup.commutator_mem_commutator hx hrR
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      have hc' := congrArg (fun y : ↥(TauCeti.QuadraticMap.orthogonalGroup
        (LinearMap.BilinMap.toQuadraticMap f)) => (toLinEquiv (Fin 6) (ZMod 3)).symm
          (y : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3))) hc
      simp only [Subgroup.coe_mul, map_mul, MulEquiv.symm_apply_apply] at hc'
      exact hc'.symm
    obtain ⟨a, b, hab⟩ := hΩq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    apply (toLinEquiv (Fin 6) (ZMod 3)).symm.injective
    have key : ∀ u w : GL (Fin 6) (ZMod 3), (u = 1 ∨ u = -1) → u * w = w * u := by
      rintro u w (rfl | rfl)
      · rw [one_mul, mul_one]
      · rw [neg_one_mul, mul_neg_one]
    simp only [Subgroup.coe_mul, map_mul]
    exact key _ _ (hpm a a.2)
  have hcomm : ⁅((F3.reflGroup f).map (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)),
      ((F3.reflGroup f).map (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f))⁆ =
      commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f)) := by
    refine le_antisymm ?_ ?_
    · rw [commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    · rw [← Subgroup.isPerfect_iff.mp hΩq.1]
      exact Subgroup.commutator_mono hΩR hΩR
  let ρ : ↥(F3.reflGroup f) ≃* ↥(((F3.reflGroup f).map
      (toLinEquiv (Fin 6) (ZMod 3)).toMonoidHom).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap f))) :=
    ((F3.reflGroup f).equivMapOfInjective _ (toLinEquiv (Fin 6) (ZMod 3)).injective).trans
      (Subgroup.subgroupOfEquivOfLe hle).symm
  let e : ↥(commutator ↥(F3.reflGroup f)) ≃* ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup
      (LinearMap.BilinMap.toQuadraticMap f))) :=
    (((commutator ↥(F3.reflGroup f)).equivMapOfInjective ρ.toMonoidHom ρ.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_of_surjective ρ.surjective))).trans
      (((commutator _).equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
        (MulEquiv.subgroupCongr ((Subgroup.map_subtype_commutator _).trans hcomm)))
  exact ⟨hΩq.of_mulEquiv e,
    (CFSG.ComponentClassification.CatLeafProof.X10Sp.CentralModel.of_mulEquiv e hCM).2⟩

end Split

section Center


theorem center_eq_bot_or_anisotropic_of_reflSix {X : Type} [Group X] [Finite X] {s : X}
    (hs : s * s = 1) (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hO2 : CFSG.pCore 2 X = ⊥)
    (hder : derivedSeries (X ⧸ Subgroup.center X) 1 = derivedSeries (X ⧸ Subgroup.center X) 2)
    (hS : IsSimpleGroup ↥(commutator (X ⧸ Subgroup.center X)))
    {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (hf : IsF3Form f)
    (φ : X ⧸ Subgroup.center X ≃* F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f)) :
    Subgroup.center X = ⊥ ∨ ¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3),
      Module.finrank (ZMod 3) T = 3 ∧ ∀ x ∈ T, f x x = 0 := by
  by_cases hT : ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f x x = 0
  swap
  · exact Or.inr hT
  left
  obtain ⟨hCq, hLie⟩ := commutator_reflGroup_six_split hf hT
  have hZ : Odd (Nat.card (Subgroup.center X)) :=
    CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hO2
  have hperf : Group.IsPerfect ↥(commutator (X ⧸ Subgroup.center X)) := by
    rw [Subgroup.isPerfect_iff, ← derivedSeries_one, ← derivedSeries_succ]
    exact hder.symm
  have := hS
  have hnc := exists_ne_comm_of_isPerfect hperf
  let κ : ↥(commutator (X ⧸ Subgroup.center X)) ≃*
      ↥(commutator (F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f))) :=
    ((commutator _).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_commutator_of_surjective φ.surjective))
  have hSR : IsSimpleGroup ↥(commutator (F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f))) :=
    MulEquiv.isSimpleGroup κ.symm
  have hncR : ∃ a b : ↥(commutator (F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f))),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨κ a, κ b, fun h => hab (κ.injective (by rw [map_mul, map_mul, h]))⟩
  obtain ⟨-, ⟨eR⟩⟩ := isQuasisimple_of_map_eq_commutator (N := Subgroup.center (F3.reflGroup f))
    le_rfl hCq.1 (map_commutator_of_surjective (QuotientGroup.mk'_surjective _)) hSR hncR
  obtain ⟨hYq, ⟨eY⟩⟩ := isQuasisimple_of_map_eq_commutator (N := Subgroup.center X) le_rfl
    (isPerfect_derivedSeries_two hder)
    (by rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _) 2, ← hder, derivedSeries_one])
    hS hnc
  have hLieY : CFSG.Blueprint.LieModel
      (↥(derivedSeries X 2) ⧸ Subgroup.center ↥(derivedSeries X 2)) .PSL 4 3 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eR.trans (κ.symm.trans eY.symm)) hLie
  have hP2 := CFSG.ComponentClassification.CatFactsL4U4.Cover82.multiplierL4U4
    ↥(derivedSeries X 2) hYq 3 1 Nat.prime_three (by decide) le_rfl (Or.inl hLieY)
  exact center_eq_bot_of_inf_derivedSeries_two hs hncl hZ hder
    (inf_center_eq_bot_of_isPGroup_two hZ hP2)

end Center

end CFSG.OddTranspositions.PartFour
