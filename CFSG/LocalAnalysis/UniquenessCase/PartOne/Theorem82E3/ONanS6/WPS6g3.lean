module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL11
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL8b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6f
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem card_inf_perfectCoreL_ge_nine'
    {A P : Subgroup G} {a : G}
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card ↥A = 27)
    (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hcomm : ⁅perfectCoreL c a, zSub P c.L⁆ ≤ CFSG.Open.pCoreOf 2 (perfectCoreL c a))
    (hgen : A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a) :
    9 ≤ Nat.card ↥(A ⊓ perfectCoreL c a) := by
  let I : Subgroup G := perfectCoreL c a
  let H : Subgroup G := Subgroup.closure ({a} : Set G)
  change 9 ≤ Nat.card ↥(A ⊓ I)
  have hIcent : I ≤ Subgroup.centralizer ({a} : Set G) :=
    (perfectCoreL_le c a).trans inf_le_right
  have ha_cent : a ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hIcent hh)
  have ha_norm : a ∈ Subgroup.normalizer (I : Set G) :=
    Subgroup.centralizer_le_normalizer (I : Set G) ha_cent
  have hHnorm : H ≤ Subgroup.normalizer (I : Set G) := by
    dsimp [H]
    rw [← Subgroup.zpowers_eq_closure]
    exact Subgroup.zpowers_le.mpr ha_norm
  have hAI_norm : A ≤ Subgroup.normalizer (I : Set G) :=
    hgen.trans (sup_le hHnorm (Subgroup.le_normalizer (H := I)))
  have ha1 : a ≠ 1 := by
    intro h
    apply haZ
    rw [h]
    exact (zSub P c.L).one_mem
  have ha3 : a ^ 3 = 1 := hA.2 a ha
  have hord : orderOf a = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime ha3 ha1
  have hHcard : Nat.card ↥H = 3 := by
    dsimp [H]
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, hord]
  haveI : (I.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hAI_norm
  haveI : (I.subgroupOf (A ⊔ I)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hAI_norm
  have hqA : Nat.card (↥A ⧸ I.subgroupOf A) =
      Nat.card (↥(A ⊔ I) ⧸ I.subgroupOf (A ⊔ I)) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient A I hAI_norm).toEquiv
  have hIrelA : I.relIndex A = I.relIndex (A ⊔ I) := by
    simpa only [Subgroup.relIndex, Subgroup.index_eq_card] using hqA
  have h1A : (A ⊓ I).relIndex A = I.relIndex A := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right I A
  haveI : (I.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  haveI : (I.subgroupOf (H ⊔ I)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hHnorm
  have hqH : Nat.card (↥H ⧸ I.subgroupOf H) =
      Nat.card (↥(H ⊔ I) ⧸ I.subgroupOf (H ⊔ I)) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient H I hHnorm).toEquiv
  have hIrelH : I.relIndex H = I.relIndex (H ⊔ I) := by
    simpa only [Subgroup.relIndex, Subgroup.index_eq_card] using hqH
  have h1H : (H ⊓ I).relIndex H = I.relIndex H := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right I H
  have hIrelH3 : I.relIndex (H ⊔ I) ≤ 3 := by
    rw [← hIrelH, ← h1H]
    have hdvd : (H ⊓ I).relIndex H ∣ Nat.card ↥H :=
      Subgroup.relIndex_dvd_card (H ⊓ I) H
    rw [hHcard] at hdvd
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hrel_eq : (A ⊓ I).relIndex A = I.relIndex (A ⊔ I) := h1A.trans hIrelA
  have hne : I.relIndex (H ⊔ I) ≠ 0 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hmono : I.relIndex (A ⊔ I) ≤ I.relIndex (H ⊔ I) :=
    Subgroup.relIndex_le_of_le_right (H := I) (K := A ⊔ I) (L := H ⊔ I)
      (sup_le hgen le_sup_right) hne
  have hrel_le : (A ⊓ I).relIndex A ≤ 3 := by
    rw [hrel_eq]
    exact hmono.trans hIrelH3
  have hBcard : (A ⊓ I).relIndex A * Nat.card ↥(A ⊓ I) = 27 := by
    have h := Subgroup.relIndex_mul_card (A ⊓ I) A
    rw [inf_eq_left.mpr inf_le_left, hA27] at h
    exact h
  have hle : 27 ≤ 3 * Nat.card ↥(A ⊓ I) := by
    calc 27 = (A ⊓ I).relIndex A * Nat.card ↥(A ⊓ I) := hBcard.symm
      _ ≤ 3 * Nat.card ↥(A ⊓ I) := Nat.mul_le_mul_right _ hrel_le
  omega

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
