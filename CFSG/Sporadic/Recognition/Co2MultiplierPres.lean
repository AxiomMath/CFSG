module

public import CFSG.Sporadic.Recognition.Co2MultiplierTables

public section

namespace CFSG.Sporadic.Recognition.Co2Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co2.Native (co2Data)
open CFSG.Sporadic.Recognition.McLMultiplier (mclRels)

@[expose] def co2IdWords : List (List (Fin 7 × Bool)) :=
  (List.finRange 7).map fun i => (i, false) :: co2CommWord i

@[expose] def co2RelsI : List (List (Fin 7 × Bool)) := co2Rels ++ co2IdWords

theorem mem_wordSet_co2RelsI {r : FreeGroup (Fin 7)} (hr : r ∈ wordSet co2Rels) :
    r ∈ wordSet co2RelsI := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  exact List.mem_map_of_mem (List.mem_append_left _ hv)

theorem inv_mul_co2CommW_mem (i : Fin 7) :
    (FreeGroup.of i)⁻¹ * co2CommW i ∈ wordSet co2RelsI :=
  List.mem_map_of_mem (f := FreeGroup.mk)
    (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i)))

theorem wordSet_co2Cover : wordSet co2Cover = coverRelators (wordSet co2Rels) co2CommW :=
  (coverRelators_wordSet co2Rels co2CommWord).symm

theorem lift_of_eq_mk {m : ℕ} (R : Set (FreeGroup (Fin m))) (x : FreeGroup (Fin m)) :
    FreeGroup.lift (fun i => (PresentedGroup.of i : PresentedGroup R)) x = PresentedGroup.mk R x :=
  (FreeGroup.lift_unique (PresentedGroup.mk R) fun _ => rfl).symm

theorem lift_co2Cover_co2RelsI :
    ∀ r ∈ wordSet co2Cover, FreeGroup.lift (fun i => (PresentedGroup.of i : PG 7 co2RelsI)) r = 1 := by
  intro r hr
  rw [wordSet_co2Cover] at hr
  rw [lift_of_eq_mk]
  rcases hr with ⟨i, r', hr', rfl⟩ | ⟨i, rfl⟩
  · rw [map_commutatorElement, PresentedGroup.one_of_mem (mem_wordSet_co2RelsI hr'),
      commutatorElement_one_right]
  · exact PresentedGroup.one_of_mem (inv_mul_co2CommW_mem i)

theorem card_PG_co2RelsI_le (hM : Finite (PG 6 mclRels) ∧ Nat.card (PG 6 mclRels) ≤ 898128000)
    (hI : (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104) :
    Finite (PG 7 co2RelsI) ∧ Nat.card (PG 7 co2RelsI) ≤ 42305421312000 := by
  have := hM.1
  set T := subsetOf 7 [0, 1, 2, 3, 4, 5] with hT
  let φ : PG 7 co2Cover →* PG 7 co2RelsI := PresentedGroup.toGroup lift_co2Cover_co2RelsI
  have hsurj : Function.Surjective φ := by
    refine MonoidHom.range_eq_top.1 (eq_top_iff.2 ?_)
    rw [← PresentedGroup.closure_range_of, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of lift_co2Cover_co2RelsI⟩
  have hmap : (genSub (wordSet co2Cover) T).map φ = genSub (wordSet co2RelsI) T := by
    rw [MonoidHom.map_closure, ← Set.image_comp]
    congr 1
  have hdvd := Subgroup.index_map_dvd (genSub (wordSet co2Cover) T) hsurj
  rw [hmap] at hdvd
  have hs0 : (genSub (wordSet co2Cover) T).index ≠ 0 := by
    have := hI.1
    exact Subgroup.FiniteIndex.index_ne_zero
  have hidx : (genSub (wordSet co2RelsI) T).index ≤ 47104 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hdvd).trans hI.2
  have hidx0 : (genSub (wordSet co2RelsI) T).index ≠ 0 := fun h0 =>
    hs0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  have hy : ∀ r ∈ wordSet mclRels,
      FreeGroup.lift (fun i : Fin 6 => (PresentedGroup.of i.castSucc : PG 7 co2RelsI)) r = 1 := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
    have he : FreeGroup.lift (fun i : Fin 6 => (PresentedGroup.of i.castSucc : PG 7 co2RelsI))
        (FreeGroup.mk v) =
          FreeGroup.lift (fun i => (PresentedGroup.of i : PG 7 co2RelsI))
            (FreeGroup.mk (co2Embed v)) := by
      simp [FreeGroup.lift_mk, co2Embed, List.map_map, Function.comp_def]
    rw [he, lift_of_eq_mk]
    exact PresentedGroup.one_of_mem (mem_wordSet_co2RelsI
      (List.mem_map_of_mem (List.mem_append_left _ (List.mem_map_of_mem hv))))
  let ψ : PG 6 mclRels →* PG 7 co2RelsI := PresentedGroup.toGroup hy
  have hle : genSub (wordSet co2RelsI) T ≤ ψ.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx6 : x.val < 6 := by
      simp only [hT, subsetOf, Set.mem_setOf_eq, List.mem_filter, List.contains_iff_mem] at hx
      have := hx.2
      simp at this
      omega
    exact ⟨PresentedGroup.of ⟨x.val, hx6⟩, PresentedGroup.toGroup.of hy⟩
  have hrs : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
  have : Finite ψ.range := Finite.of_surjective _ hrs
  have hcard : Nat.card (genSub (wordSet co2RelsI) T) ≤ 898128000 :=
    (Subgroup.card_le_of_le hle).trans ((Nat.card_le_card_of_surjective _ hrs).trans hM.2)
  have : Finite (genSub (wordSet co2RelsI) T) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hpos : 0 < Nat.card (genSub (wordSet co2RelsI) T) := Nat.card_pos
  have hmul := Subgroup.index_mul_card (genSub (wordSet co2RelsI) T)
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [← hmul]
    exact Nat.mul_ne_zero hidx0 hpos.ne'
  · rw [← hmul]
    exact (Nat.mul_le_mul hidx hcard).trans (by norm_num)

theorem lift_co2Gen_co2RelsI (hTab : co2TabCheck = true) :
    ∀ r ∈ wordSet co2RelsI, FreeGroup.lift co2Gen r = 1 := by
  intro r hr
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
  rcases List.mem_append.1 hv with hv | hv
  · exact lift_co2Gen_rels hTab _ (List.mem_map_of_mem hv)
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
    rw [show FreeGroup.mk ((i, false) :: co2CommWord i) =
        (FreeGroup.of i)⁻¹ * FreeGroup.mk (co2CommWord i) from rfl, map_mul, map_inv,
      FreeGroup.lift_apply_of, lift_co2CommWord hTab, inv_mul_cancel]

theorem isPresentation_co2GenI (hTab : co2TabCheck = true)
    (hM : Finite (PG 6 mclRels) ∧ Nat.card (PG 6 mclRels) ≤ 898128000)
    (hI : (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104) :
    IsPresentation co2Gen (wordSet co2RelsI) := by
  obtain ⟨hfin, hle⟩ := card_PG_co2RelsI_le hM hI
  have : Finite (PresentedGroup (wordSet co2RelsI)) := hfin
  exact IsPresentation.of_card_le (lift_co2Gen_co2RelsI hTab) (closure_co2Gen hTab) (by
    rw [card_J]
    exact hle)

theorem normalClosure_coverRelators_co2RelsI :
    Subgroup.normalClosure (coverRelators (wordSet co2RelsI) co2CommW) =
      Subgroup.normalClosure (wordSet co2Cover) := by
  refine le_antisymm (Subgroup.normalClosure_le_normal fun x hx => ?_)
    (Subgroup.normalClosure_le_normal fun x hx => ?_)
  · rcases hx with ⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
      rcases List.mem_append.1 hv with hv | hv
      · apply Subgroup.subset_normalClosure
        rw [wordSet_co2Cover]
        exact Set.mem_union_left _ ⟨i, _, List.mem_map_of_mem hv, rfl⟩
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hv
        have hn : FreeGroup.mk ((j, false) :: co2CommWord j) ∈
            Subgroup.normalClosure (wordSet co2Cover) := by
          apply Subgroup.subset_normalClosure
          rw [wordSet_co2Cover]
          exact Set.mem_union_right _ ⟨j, rfl⟩
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.normalClosure_normal.conj_mem _ hn _)
          (Subgroup.inv_mem _ hn)
    · apply Subgroup.subset_normalClosure
      rw [wordSet_co2Cover]
      exact Set.mem_union_right _ ⟨i, rfl⟩
  · rw [wordSet_co2Cover] at hx
    apply Subgroup.subset_normalClosure
    rcases hx with ⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩
    · exact Set.mem_union_left _ ⟨i, r, mem_wordSet_co2RelsI hr, rfl⟩
    · exact Set.mem_union_right _ ⟨i, rfl⟩

@[expose] noncomputable def coverEquivI : PresentedCover (wordSet co2RelsI) co2CommW ≃* PG 7 co2Cover :=
  QuotientGroup.quotientMulEquivOfEq normalClosure_coverRelators_co2RelsI

end CFSG.Sporadic.Recognition.Co2Multiplier

end
