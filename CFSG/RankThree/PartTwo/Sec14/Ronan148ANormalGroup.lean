module

import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
import CFSG.RankThree.PartTwo.Sec14.Ronan148NCentTools
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.GH74.GLS

variable {Γ : Type} [Group Γ] [Finite Γ]

private theorem exists_orderOf_three_centralizer {D P : Subgroup Γ} (hP : IsPGroup 3 P)
    (hPD : P ≤ Subgroup.normalizer (D : Set Γ)) (h3 : 3 ∣ Nat.card D) :
    ∃ w : Γ, w ∈ D ∧ w ∈ Subgroup.centralizer (P : Set Γ) ∧ orderOf w = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Sec6.card_inf_centralizer_modEq hP hPD
  have h3C : 3 ∣ Nat.card ↥(D ⊓ Subgroup.centralizer (P : Set Γ)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr h3))
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3C
  refine ⟨(w : Γ), (Subgroup.mem_inf.mp w.2).1, (Subgroup.mem_inf.mp w.2).2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hw

private theorem mem_zpowers_of_orderOf_three {e w : Γ} (he3 : e ^ 3 = 1) (hw : orderOf w = 3)
    (hwe : w ∈ Subgroup.zpowers e) : e ∈ Subgroup.zpowers w := by
  have hle : Subgroup.zpowers w ≤ Subgroup.zpowers e := Subgroup.zpowers_le.mpr hwe
  have hcard : Nat.card (Subgroup.zpowers e) ≤ Nat.card (Subgroup.zpowers w) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hw]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one he3)
  rw [Subgroup.eq_of_le_of_card_ge hle hcard]
  exact Subgroup.mem_zpowers e

theorem mem_of_three_dvd_of_le_centralizer {J D A : Subgroup Γ} {e : Γ}
    (hDC : D ≤ Subgroup.centralizer (J : Set Γ)) (hA : IsPGroup 3 A)
    (hAD : A ≤ Subgroup.normalizer (D : Set Γ)) (h3 : 3 ∣ Nat.card D)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (A : Set Γ) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set Γ) ≤ Subgroup.zpowers e) (he3 : e ^ 3 = 1) :
    e ∈ D := by
  obtain ⟨w, hwD, hwC, hw⟩ := exists_orderOf_three_centralizer hA hAD h3
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwA : w ∈ A := hF3 w hwC hw3
  have hwe : w ∈ Subgroup.zpowers e := hAJ ⟨hwA, hDC hwD⟩
  have hWD : Subgroup.zpowers w ≤ D := Subgroup.zpowers_le.mpr hwD
  exact hWD (mem_zpowers_of_orderOf_three he3 hw hwe)

theorem map_conj_eq_of_not_mem_centralizer {J A F : Subgroup Γ} {e : Γ} (hJ : IsComponent J)
    (h3 : 3 ∣ Nat.card J) (he3 : e ^ 3 = 1) (heN : e ∈ Subgroup.normalizer (J : Set Γ))
    (heC : e ∉ Subgroup.centralizer (J : Set Γ)) (hFJ : F ≤ J)
    (hA : A = Subgroup.zpowers e ⊔ F)
    (hF3 : ∀ w : Γ, w ∈ Subgroup.centralizer (A : Set Γ) → w ^ 3 = 1 → w ∈ A)
    (hAJ : A ⊓ Subgroup.centralizer (J : Set Γ) ≤ Subgroup.zpowers e) (x : Γ) :
    J.map (MulAut.conj x).toMonoidHom = J := by
  by_contra hne
  have hJx : J ≠ J.map (MulAut.conj x).toMonoidHom := fun h => hne h.symm
  have hJxC : J.map (MulAut.conj x).toMonoidHom ≤ Subgroup.centralizer (J : Set Γ) :=
    fun y hy => Res2LBal.mem_centralizer_of_mem_of_ne hJ (Res2LBal.isComponent_conj hJ x) hJx hy
  have hcardJx : Nat.card (J.map (MulAut.conj x).toMonoidHom) = Nat.card J :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have h3Jx : 3 ∣ Nat.card (J.map (MulAut.conj x).toMonoidHom) := by
    rw [hcardJx]
    exact h3
  have h3C : 3 ∣ Nat.card ↥(Subgroup.centralizer (J : Set Γ)) :=
    h3Jx.trans (Subgroup.card_dvd_of_le hJxC)
  have hPC : Subgroup.zpowers e ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set Γ) : Set Γ) :=
    Subgroup.zpowers_le.mpr (Ronan148N.mem_normalizer_centralizer148 heN)
  obtain ⟨w, hwC, hweC, hw⟩ :=
    exists_orderOf_three_centralizer (Res2LBal.isPGroup_zpowers he3) hPC h3C
  have hwA : w ∈ Subgroup.centralizer (A : Set Γ) := by
    rw [hA, Subgroup.mem_centralizer_iff]
    intro a ha
    have hcl : Subgroup.zpowers e ⊔ F ≤ Subgroup.centralizer {w} := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hweC e (Subgroup.mem_zpowers e)
      · intro b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp hwC b (hFJ hb)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcl ha)
  have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwAA : w ∈ A := hF3 w hwA hw3
  have hwe : w ∈ Subgroup.zpowers e := hAJ ⟨hwAA, hwC⟩
  have heW : e ∈ Subgroup.zpowers w := mem_zpowers_of_orderOf_three he3 hw hwe
  have hWC : Subgroup.zpowers w ≤ Subgroup.centralizer (J : Set Γ) :=
    Subgroup.zpowers_le.mpr hwC
  exact heC (hWC heW)

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
