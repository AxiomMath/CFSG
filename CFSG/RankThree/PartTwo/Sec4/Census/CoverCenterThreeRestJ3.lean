module

public import CFSG.Sporadic.J3
public import CFSG.Foundations.Basic
public import Certificates.Certificate8008

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

open Subgroup CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.CosetTable
open scoped commutatorElement

theorem J3_cover_witness :
    ∃ g : Fin 6 → NativeSporadic.J3,
      (∀ i, j3CoverE i ≠ 0 → g i ^ j3CoverE i = 1) ∧
      (∀ i, j3CoverE i = 0 → g i = ⁅evalW g (j3CoverCWf i).1, evalW g (j3CoverCWf i).2⁆) ∧
      (∀ w ∈ j3CoverRels, evalW g w = 1) ∧
      Nat.card (Subgroup.closure ({g 0, g 1} : Set NativeSporadic.J3)) = 1944 :=
  Certificates.certificate8008.1

theorem j3_gamma_card :
    Finite (PG 6 j3GammaWords) ∧ Nat.card (PG 6 j3GammaWords) ≤ 729 * 8 :=
  Certificates.certificate8008.2

theorem card_center_dvd_three_of_J3_witness {X : Type} [Group X] [Finite X]
    (hX : IsQuasisimple X) (hZ : IsPGroup 3 (center X))
    (hcard : Nat.card (X ⧸ center X) = 50232960) (g : Fin 6 → X ⧸ center X)
    (he : ∀ i, j3CoverE i ≠ 0 → g i ^ j3CoverE i = 1)
    (hc : ∀ i, j3CoverE i = 0 → g i = ⁅evalW g (j3CoverCWf i).1, evalW g (j3CoverCWf i).2⁆)
    (hrels : ∀ w ∈ j3CoverRels, evalW g w = 1)
    (hN : Nat.card (Subgroup.closure ({g 0, g 1} : Set (X ⧸ center X))) = 1944)
    (hΓ : Finite (PG 6 j3GammaWords) ∧ Nat.card (PG 6 j3GammaWords) ≤ 729 * 8) :
    Nat.card (center X) ∣ 3 := by
  have : Group.IsPerfect X := hX.1
  have hπk := QuotientGroup.ker_mk' (center X)
  set H := closure (Set.range g)
  have hle : Subgroup.closure ({g 0, g 1} : Set (X ⧸ center X)) ≤ H := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact subset_closure ⟨0, rfl⟩
    · exact subset_closure ⟨1, rfl⟩
  have hNidx : (Subgroup.closure ({g 0, g 1} : Set (X ⧸ center X))).index = 25840 := by
    have h1 := (Subgroup.closure ({g 0, g 1} : Set (X ⧸ center X))).index_mul_card
    rw [hN, hcard] at h1
    omega
  have hidx : ¬ 3 ∣ H.index := by
    intro h3
    have := h3.trans (Subgroup.index_dvd_of_le hle)
    rw [hNidx] at this
    omega
  have hcardH : 1944 ≤ Nat.card H := by
    rw [← hN]
    exact Subgroup.card_le_of_le hle
  have he' : ∀ i, j3CoverE i ≠ 0 → g i ^ j3CoverE i = 1 ∧ Nat.Coprime 3 (j3CoverE i) := by
    intro i hi
    refine ⟨he i hi, ?_⟩
    have : j3CoverE i = 8 := by
      unfold j3CoverE at hi ⊢
      split_ifs at hi ⊢ <;> simp_all
    rw [this]
    decide
  obtain ⟨hfin, hcardΓ⟩ := hΓ
  have hbound := card_closure_mul_card_ker_le (QuotientGroup.mk'_surjective (center X)) hπk.le
    (by rw [hπk]; exact hZ) g j3CoverE j3CoverCWf he' hc j3CoverRels hrels hidx hfin
  rw [hπk] at hbound
  have h3 : Nat.card (center X) ≤ 3 := by
    have : Nat.card H * Nat.card (center X) ≤ 729 * 8 := hbound.trans hcardΓ
    nlinarith
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  rw [hk] at h3 ⊢
  rcases k with _ | _ | k
  · exact one_dvd 3
  · exact dvd_rfl
  · have : 3 ^ 2 ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem card_center_dvd_three_of_J3
    {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) (hZ : IsPGroup 3 (center X))
    (e : X ⧸ center X ≃* NativeSporadic.J3) : Nat.card (center X) ∣ 3 := by
  obtain ⟨g, he, hc, hrels, hN⟩ := J3_cover_witness
  have hev : ∀ w, e.symm (evalW g w) = evalW (fun i => e.symm (g i)) w := fun w =>
    map_evalW e.symm g w
  refine card_center_dvd_three_of_J3_witness hX hZ
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J3.card_J3) (fun i => e.symm (g i))
    (fun i hi => by rw [← map_pow, he i hi, map_one])
    (fun i hi => by rw [← hev, ← hev, ← map_commutatorElement, ← hc i hi])
    (fun w hw => by rw [← hev, hrels w hw, map_one]) ?_
    j3_gamma_card
  have h := Subgroup.card_map_of_injective (f := (e.symm : NativeSporadic.J3 →* X ⧸ center X))
    (K := Subgroup.closure ({g 0, g 1} : Set NativeSporadic.J3)) e.symm.injective
  rw [MonoidHom.map_closure, Set.image_pair] at h
  exact h.trans hN

end CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
