module

public import CFSG.Sporadic.Recognition.Co2MultiplierPres
public import CFSG.Sporadic.Recognition.McLMultiplier
public import CFSG.Sporadic.Recognition.CoverIndex
public import CFSG.Sporadic.Recognition.McLMultiplierMatrix

public section

namespace CFSG.Sporadic.Recognition.Co2Multiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Co2.Native (co2Data)
open CFSG.Sporadic.Recognition.McLMultiplier (mclRels mclRels5 mclCover mclCover5 mclTabCheck
  mclMatCheck)

set_option maxRecDepth 100000 in
theorem restrict_co2Cover : co2Cover6 = mclCover := by decide

theorem lift_co2CommW (hTab : co2TabCheck = true) (i : Fin 7) :
    FreeGroup.lift co2Gen (co2CommW i) = co2Gen i :=
  lift_co2CommWord hTab i

theorem co2CommW_mem_commutator (i : Fin 7) : co2CommW i ∈ commutator (FreeGroup (Fin 7)) :=
  mk_commWords_mem_commutator _

theorem card_PG_mclCover
    (hP : IsPresentation McLMultiplier.mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift McLMultiplier.mclGen (McLMultiplier.mclCommW i) =
      McLMultiplier.mclGen i)
    (hcard : Finite McLMultiplier.MclCover ∧ Nat.card McLMultiplier.MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk McLMultiplier.mclR0) :
      McLMultiplier.MclCover)) :
    Finite (PG 6 mclCover) ∧ Nat.card (PG 6 mclCover) = 2694384000 := by
  have hc := card_presentedCover hP McLMultiplier.mclCommW_mem_commutator hwg
  rw [CFSG.Sporadic.McL.card_J, McLMultiplier.card_griessHopfMultiplier_J hP hwg hcard h3] at hc
  change Finite (PresentedGroup (wordSet mclCover)) ∧
    Nat.card (PresentedGroup (wordSet mclCover)) = 2694384000
  rw [← McLMultiplier.coverRelators_mclCommW]
  exact ⟨hcard.1, hc⟩

theorem lift_embed_eq (v : List (Fin 6 × Bool)) :
    FreeGroup.lift (fun i : Fin 6 => co2Gen i.castSucc) (FreeGroup.mk v) =
      FreeGroup.lift co2Gen (FreeGroup.mk (co2Embed v)) := by
  simp [FreeGroup.lift_mk, co2Embed, List.map_map, Function.comp_def]

section Multiplier

theorem card_griessHopfMultiplier_J_dvd_three (hTab : co2TabCheck = true)
    (hM : Finite (PG 6 mclRels) ∧ Nat.card (PG 6 mclRels) ≤ 898128000)
    (hMC : Finite (PG 6 mclCover) ∧ Nat.card (PG 6 mclCover) = 2694384000)
    (hI : (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104) :
    Nat.card (griessHopfMultiplier (J co2Data)) ∣ 3 := by
  have hP := isPresentation_co2GenI hTab hM hI
  have hw : ∀ i, co2CommW i ∈ commutator (FreeGroup (Fin 7)) := fun i =>
    co2CommW_mem_commutator i
  have hwg : ∀ i, FreeGroup.lift co2Gen (co2CommW i) = co2Gen i := fun i => lift_co2CommW hTab i
  have hcard := card_presentedCover hP hw hwg
  have hsurj := coverMap_surjective hP hwg
  have hK6 : Finite (PG 6 co2Cover6) ∧ Nat.card (PG 6 co2Cover6) = 2694384000 := by
    rw [restrict_co2Cover]
    exact hMC
  have : Finite (PG (subsetOf 7 [0, 1, 2, 3, 4, 5]).length
      (restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) co2Cover)) := hK6.1
  obtain ⟨ψ, hψ⟩ := CoverIndex.exists_hom_genSub co2Cover (subsetOf 7 [0, 1, 2, 3, 4, 5])
  set Hs := genSub (coverRelators (wordSet co2RelsI) co2CommW) (subsetOf 7 [0, 1, 2, 3, 4, 5])
    with hHs
  set π := coverMap hP hwg with hπ
  have hmapE : Hs.map coverEquivI.toMonoidHom =
      genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5]) := by
    rw [hHs, MonoidHom.map_closure, ← Set.image_comp]
    congr 1
  have hidxE : Hs.index = (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index := by
    rw [← hmapE, Subgroup.index_map_of_bijective coverEquivI.bijective]
  have hidx : Hs.index ≤ 47104 := hidxE ▸ hI.2
  have hidx0 : 0 < Hs.index := by
    have := hI.1
    rw [hidxE]
    exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hH₀ : Nat.card (Hs.map π) ≤ 898128000 := by
    let e : Fin 6 → J co2Data := fun i => co2Gen i.castSucc
    have hrel : ∀ r ∈ wordSet mclRels, FreeGroup.lift e r = 1 := by
      intro r hr
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
      rw [lift_embed_eq]
      exact lift_co2Gen_rels hTab _ (List.mem_map_of_mem (f := FreeGroup.mk)
        (List.mem_append_left _ (List.mem_map_of_mem hv)))
    have := hM.1
    have hle : Hs.map π ≤ Subgroup.closure (Set.range e) := by
      rw [Subgroup.map_le_iff_le_comap, hHs, genSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx6 : x.val < 6 := by
        simp only [subsetOf, Set.mem_ofPred_eq, List.mem_filter, List.contains_iff_mem] at hx
        have := hx.2
        simp at this
        omega
      rw [SetLike.mem_coe, Subgroup.mem_comap, hπ, coverMap_of]
      exact Subgroup.subset_closure ⟨⟨x.val, hx6⟩, rfl⟩
    exact (Subgroup.card_le_of_le hle).trans
      ((CoverIndex.card_closure_range_le_PG hrel).trans hM.2)
  have hdvd : (Hs.map π).index ∣ Hs.index := Subgroup.index_map_dvd Hs hsurj
  have hdiv : Nat.card Hs ∣ 898128000 * 3 := by
    have h := Subgroup.card_range_dvd ψ
    have hK6' : Nat.card (PG (subsetOf 7 [0, 1, 2, 3, 4, 5]).length
        (restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) co2Cover)) = 898128000 * 3 := hK6.2
    rw [hψ, ← hmapE, Subgroup.card_map_of_injective coverEquivI.injective, hK6'] at h
    exact h
  have h₁' : (Hs.map π).index * Nat.card (Hs.map π) = 47104 * 898128000 := by
    rw [Subgroup.index_mul_card]
    exact card_J
  have h₂' : Hs.index * Nat.card Hs =
      47104 * 898128000 * Nat.card (griessHopfMultiplier (J co2Data)) := by
    rw [Subgroup.index_mul_card, hcard, card_J]
  exact CoverIndex.dvd_of_counts (N := 47104) (m := 898128000) (c := 3) (by norm_num)
    (by norm_num) hidx hidx0 hdvd h₁' hH₀ h₂' hdiv

theorem card_center_dvd_three (hTab : co2TabCheck = true)
    (hM : Finite (PG 6 mclRels) ∧ Nat.card (PG 6 mclRels) ≤ 898128000)
    (hMC : Finite (PG 6 mclCover) ∧ Nat.card (PG 6 mclCover) = 2694384000)
    (hI : (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (genSub (wordSet co2Cover) (subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 47104)
    {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.Co2) :
    Nat.card (Subgroup.center Q) ∣ 3 :=
  (card_center_dvd_of_cover (p := Nat.card (griessHopfMultiplier (J co2Data)))
    (cw := co2CommWord) (isPresentation_co2GenI hTab hM hI)
    (fun i => co2CommW_mem_commutator i) (fun i => lift_co2CommW hTab i) rfl hQ
    (e.trans CFSG.Sporadic.Bridge.Co2.nativeEquiv)).trans
    (card_griessHopfMultiplier_J_dvd_three hTab hM hMC hI)

end Multiplier

end CFSG.Sporadic.Recognition.Co2Multiplier
