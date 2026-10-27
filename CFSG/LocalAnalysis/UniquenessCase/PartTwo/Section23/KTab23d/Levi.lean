module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.GroupTheory.PCoreSurjective

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

private theorem map_perfectResidual_eq_of_leviHom_D1 {G A : Type} [Group G] [Finite G] [Group A]
    (P : Subgroup G) (β : ↥P →* A) (S : Subgroup A)
    (hSR : S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ S) (hperf : ⁅S, S⁆ = S) :
    (CFSG.perfectResidual ↥P).map β = S := by
  haveI : Finite ↥β.range :=
    Finite.of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hA : (CFSG.perfectResidual ↥P).map β =
      (CFSG.perfectResidual ↥β.range).map β.range.subtype := by
    have hmap := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
      β.rangeRestrict β.rangeRestrict_surjective
    have hmap' := congrArg (Subgroup.map β.range.subtype) hmap
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at hmap'
    exact hmap'
  have hSB : (CFSG.perfectResidual ↥β.range).map β.range.subtype = S := by
    apply le_antisymm
    · calc (CFSG.perfectResidual ↥β.range).map β.range.subtype
          ≤ (derivedSeries ↥β.range 1).map β.range.subtype :=
            Subgroup.map_mono (iInf_le _ 1)
        _ = ⁅β.range, β.range⁆ := by
            rw [derivedSeries_one, commutator_def]
            simp only [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
        _ ≤ S := hcomm
    · exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf S β.range
        (Subgroup.isPerfect_iff.mpr hperf) hSR
  exact hA.trans hSB

private theorem nonempty_bar2_hinf_equiv_quotient_D1 {G A : Type} [Group G] [Finite G] [Group A]
    (P : Subgroup G) (β : ↥P →* A) (S : Subgroup A)
    (hDS : (CFSG.perfectResidual ↥P).map β = S) (hker : IsPGroup 2 ↥β.ker) :
    Nonempty (Bar2 (Hinf P) ≃* ↥S ⧸ CFSG.pCore 2 ↥S) := by
  classical
  let D : Subgroup ↥P := CFSG.perfectResidual ↥P
  have hmemD : ∀ d : D, β d.1 ∈ S := by
    intro d
    rw [← hDS]
    exact Subgroup.mem_map.mpr ⟨d.1, d.2, rfl⟩
  let φ : D →* ↥S := (β.comp D.subtype).codRestrict S hmemD
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨d, hd, hdy⟩ :=
      Subgroup.mem_map.mp (show y.1 ∈ (CFSG.perfectResidual ↥P).map β from by
        rw [hDS]; exact y.2)
    exact ⟨⟨d, hd⟩, Subtype.ext hdy⟩
  let e : D ≃* ↥(D.map P.subtype) :=
    Subgroup.equivMapOfInjective D P.subtype P.subtype_injective
  let ψ : ↥(D.map P.subtype) →* ↥S := φ.comp e.symm
  have hψsurj : Function.Surjective ψ := by
    have h : Function.Surjective (φ ∘ (e.symm : ↥(D.map P.subtype) → D)) :=
      hφsurj.comp e.symm.surjective
    exact h
  have hψker : IsPGroup 2 ↥ψ.ker := by
    let κ : ↥ψ.ker →* ↥β.ker :=
      { toFun := fun z => ⟨D.subtype (e.symm z.1),
          congrArg (fun w : ↥S => (w : A)) (MonoidHom.mem_ker.mp z.2)⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp) }
    refine hker.of_injective κ (fun a b hab => ?_)
    apply Subtype.ext
    exact e.symm.injective
      (D.subtype_injective (congrArg (fun w : ↥β.ker => (w.1 : ↥P)) hab))
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker ψ hψsurj hψker

theorem nonempty_bar2_hinf_equiv_of_leviHom {G A : Type} [Group G] [Finite G] [Group A]
    (P : Subgroup G) (β : ↥P →* A) (hker : IsPGroup 2 ↥β.ker) (S : Subgroup A)
    (hSR : S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ S) (hperf : ⁅S, S⁆ = S)
    (hO2 : CFSG.pCore 2 ↥S = ⊥) : Nonempty (Bar2 (Hinf P) ≃* ↥S) := by
  have hDS := map_perfectResidual_eq_of_leviHom_D1 P β S hSR hcomm hperf
  obtain ⟨e⟩ := nonempty_bar2_hinf_equiv_quotient_D1 P β S hDS hker
  exact ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot)⟩

theorem hinf_eq_bot_of_leviHom_solvable {G A : Type} [Group G] [Finite G] [Group A]
    (P : Subgroup G) (β : ↥P →* A) (hker : IsPGroup 2 ↥β.ker)
    (hA : Group.IsSolvable ↥β.range) : Hinf P = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable ↥β.range := hA
  haveI : Group.IsSolvable ↥β.ker := by
    have hnil := hker.isNilpotent
    infer_instance
  have hsolvP : Group.IsSolvable ↥P :=
    Group.isSolvable_of_ker_le_range β.ker.subtype β.rangeRestrict (by
      rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hbot : CFSG.perfectResidual ↥P = ⊥ :=
    (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable
      (G := ↥P)).mpr hsolvP
  show (CFSG.perfectResidual ↥P).map P.subtype = ⊥
  rw [hbot, Subgroup.map_bot]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
