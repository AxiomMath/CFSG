module

public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Inner
import CFSG.RankThree.PartTwo.Sec19.Hyp1921NotLeM
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.eq_zpowers_sup_inf_Q
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    A = Subgroup.zpowers c ⊔ (Q ⊓ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcmem : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hc]; exact Subgroup.mem_zpowers c
  have hc3 := h.orderOf_eq_three hc
  have hc1 : c ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hc3; omega
  obtain ⟨hE, -⟩ := h.isE27_inf_Q_sup_zpowers hQ hAQ hcmem hc1
  have hsub : A ≤ Subgroup.zpowers c ⊔ (Q ⊓ L) := by
    intro x hxA
    by_cases hxc : x ∈ Subgroup.zpowers c
    · exact Subgroup.mem_sup_left hxc
    have hxN : x ∈ Subgroup.normalizer (L : Set G) := h.le_normalizer (h.le_N hxA)
    have hx3 : x ^ 3 = 1 := by simpa using h.isE27.1.2 x hxA
    have hXA : Subgroup.zpowers c ⊔ Subgroup.zpowers x ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr hcmem.1) (Subgroup.zpowers_le.mpr hxA)
    have hcomm : x * c = c * x :=
      congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hxA⟩ ⟨c, hcmem.1⟩)
    have hxo : orderOf x = 3 := orderOf_eq_prime hx3 fun h1 => hxc (h1 ▸ Subgroup.one_mem _)
    obtain ⟨hXe, hXcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
      (X := Subgroup.zpowers c) (by rw [Nat.card_zpowers, hc3]) hxo hxc fun a ha => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact ((show Commute c x from hcomm.symm).zpow_left i).eq
    have hX2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) :=
      two_le_pRank_of_elemAbelian hXe ((by norm_num : (9 : ℕ) ≤ 3 ^ 2).trans hXcard.ge)
    have hXM : Subgroup.normalizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) :
        Set G) ≤ M := fun g hg => h.mem_scriptM.2 (normalizer_le_gamma hXA hX2 hg)
    exact h.mem_sup_of_inner hQ hAQ hc (hAQ hxA) hxN hx3
      (h.barAut_mem_range hET hQ hAQ hc (hAQ hxA) hxN hx3 hXM)
  refine Subgroup.eq_of_le_of_card_ge hsub ?_
  rw [sup_comm, hE.2, h.isE27.2]

theorem Hyp1921.inf_Q_eq_inf
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    Q ⊓ L = A ⊓ L := by
  have hEQ := h.eq_zpowers_sup_inf_Q hET hQ hAQ hc
  refine le_antisymm (fun x hx => ⟨?_, hx.2⟩) (inf_le_inf_right L hAQ)
  rw [hEQ]
  exact Subgroup.mem_sup_right hx

theorem Hyp1921.isSylowOf_inf
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    IsSylowOf 3 (A ⊓ L) L := by
  obtain ⟨Q, hQ, hAQ⟩ := h.exists_isSylowOf_ge
  have := h.isSylowOf_inf_Q hQ
  rwa [h.inf_Q_eq_inf hET hQ hAQ hc] at this

theorem Hyp1921.card_inf
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    Nat.card (A ⊓ L : Subgroup G) = 9 := by
  obtain ⟨Q, hQ, hAQ⟩ := h.exists_isSylowOf_ge
  have := h.card_inf_Q hQ
  rwa [h.inf_Q_eq_inf hET hQ hAQ hc] at this

theorem Hyp1921.eq_zpowers_sup_inf
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  obtain ⟨Q, hQ, hAQ⟩ := h.exists_isSylowOf_ge
  have := h.eq_zpowers_sup_inf_Q hET hQ hAQ hc
  rwa [h.inf_Q_eq_inf hET hQ hAQ hc] at this

theorem Hyp1921.normalizer_inf_le (h : Hyp1921 G A M N L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M := by
  have hBe : CFSG.Open.IsElemAbelian 3 (A ⊓ L : Subgroup G) :=
    isElemAbelian_of_le h.isE27.1 inf_le_left
  exact fun x hx => h.mem_scriptM.2
    (normalizer_le_gamma inf_le_left (two_le_pRank_of_elemAbelian hBe h9.ge) hx)

end CFSG.RankThree.PartTwo.Late
