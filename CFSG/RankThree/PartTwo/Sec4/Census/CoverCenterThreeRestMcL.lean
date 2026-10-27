module

public import CFSG.Sporadic.McL.Simple
public import CFSG.Foundations.Basic
public import Certificates.Certificate8009

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

open Subgroup CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.CosetTable
open scoped commutatorElement

theorem McL_cover_witness :
    ∃ g : Fin 7 → NativeSporadic.McL,
      (∀ i, mclCoverE i ≠ 0 → g i ^ mclCoverE i = 1) ∧
      (∀ i, mclCoverE i = 0 → g i = ⁅evalW g (mclCoverCWf i).1, evalW g (mclCoverCWf i).2⁆) ∧
      (∀ w ∈ mclCoverRels, evalW g w = 1) ∧
      58320 ≤ Nat.card (Subgroup.closure (Set.range g)) :=
  Certificates.certificate8009.1

theorem mcl_pres_card :
    Finite (PG 7 mclPresWords) ∧ Nat.card (PG 7 mclPresWords) ≤ 14580 * 4 :=
  Certificates.certificate8009.2.1

theorem mcl_gamma_card :
    Finite (PG 7 mclGammaWords) ∧ Nat.card (PG 7 mclGammaWords) ≤ 87480 * 4 :=
  Certificates.certificate8009.2.2

theorem card_center_dvd_three_of_McL_witness {X : Type} [Group X] [Finite X]
    (hX : IsQuasisimple X) (hZ : IsPGroup 3 (center X))
    (hcard : Nat.card (X ⧸ center X) = 898128000) (g : Fin 7 → X ⧸ center X)
    (he : ∀ i, mclCoverE i ≠ 0 → g i ^ mclCoverE i = 1)
    (hc : ∀ i, mclCoverE i = 0 → g i = ⁅evalW g (mclCoverCWf i).1, evalW g (mclCoverCWf i).2⁆)
    (hrels : ∀ w ∈ mclCoverRels, evalW g w = 1)
    (hH : 58320 ≤ Nat.card (Subgroup.closure (Set.range g)))
    (hP : Finite (PG 7 mclPresWords) ∧ Nat.card (PG 7 mclPresWords) ≤ 14580 * 4)
    (hΓ : Finite (PG 7 mclGammaWords) ∧ Nat.card (PG 7 mclGammaWords) ≤ 87480 * 4) :
    Nat.card (center X) ∣ 3 := by
  have : Group.IsPerfect X := hX.1
  have hπk := QuotientGroup.ker_mk' (center X)
  set H := Subgroup.closure (Set.range g)
  have hpres : ∀ w ∈ mclPresWords, evalW g w = 1 := by
    intro w hw
    simp only [mclPresWords, List.mem_append, List.mem_singleton, List.mem_map,
      List.mem_finRange, true_and] at hw
    rcases hw with (hw | rfl) | ⟨i, rfl⟩
    · exact hrels w hw
    · have h0 := he 0 (by decide)
      have hpow : evalW g (List.replicate 4 (0, true)) = g 0 ^ 4 := by
        simp [evalW, List.replicate_succ, pow_succ, mul_assoc]
      rw [hpow]
      exact h0
    · have hi : mclCoverE i.succ = 0 := by
        unfold mclCoverE
        simp
      have h1 : evalW g [(i.succ, false)] = (g i.succ)⁻¹ := by simp [evalW]
      rw [evalW_append, evalW_commW, h1, ← hc i.succ hi, mul_inv_cancel]
  have hHle : Nat.card H ≤ 58320 :=
    (card_closure_le_of_rels g mclPresWords hpres hP.1).trans hP.2
  have hHcard : Nat.card H = 58320 := le_antisymm hHle hH
  have hidx : ¬ 3 ∣ H.index := by
    have h1 := H.index_mul_card
    rw [hHcard, hcard] at h1
    have : H.index = 15400 := by omega
    rw [this]
    decide
  have he' : ∀ i, mclCoverE i ≠ 0 → g i ^ mclCoverE i = 1 ∧ Nat.Coprime 3 (mclCoverE i) := by
    intro i hi
    refine ⟨he i hi, ?_⟩
    have : mclCoverE i = 4 := by
      unfold mclCoverE at hi ⊢
      split_ifs at hi ⊢ <;> simp_all
    rw [this]
    decide
  obtain ⟨hfin, hcardΓ⟩ := hΓ
  have hbound := card_closure_mul_card_ker_le (QuotientGroup.mk'_surjective (center X)) hπk.le
    (by rw [hπk]; exact hZ) g mclCoverE mclCoverCWf he' hc mclCoverRels hrels hidx hfin
  rw [hπk, hHcard] at hbound
  have h6 : Nat.card (center X) ≤ 6 := by
    have : 58320 * Nat.card (center X) ≤ 87480 * 4 := hbound.trans hcardΓ
    omega
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at h6 ⊢
  rcases k with _ | _ | k
  · exact one_dvd 3
  · exact dvd_rfl
  · have : 3 ^ 2 ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem card_center_dvd_three_of_McL
    {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : IsPGroup 3 (center X)) (e : X ⧸ center X ≃* NativeSporadic.McL) :
    Nat.card (center X) ∣ 3 := by
  obtain ⟨g, he, hc, hrels, hH⟩ := McL_cover_witness
  have hev : ∀ w, e.symm (evalW g w) = evalW (fun i => e.symm (g i)) w := fun w =>
    map_evalW e.symm g w
  refine card_center_dvd_three_of_McL_witness hX hZ
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.McL.card_McL) (fun i => e.symm (g i))
    (fun i hi => by rw [← map_pow, he i hi, map_one])
    (fun i hi => by rw [← hev, ← hev, ← map_commutatorElement, ← hc i hi])
    (fun w hw => by rw [← hev, hrels w hw, map_one]) ?_ mcl_pres_card mcl_gamma_card
  have h := Subgroup.card_map_of_injective (f := (e.symm : NativeSporadic.McL →* X ⧸ center X))
    (K := Subgroup.closure (Set.range g)) e.symm.injective
  rw [MonoidHom.map_closure, ← Set.range_comp] at h
  exact h.symm ▸ hH

end CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
