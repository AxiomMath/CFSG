module

public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.RankThree.PartTwo.Sec18.Item186Three
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Inner
import CFSG.RankThree.PartTwo.Sec19.Hyp1921NotLeM
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Structure
public import CFSG.RankThree.PartTwo.Late.GammaZero

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

open scoped Pointwise in
theorem Hyp1921.omegaOneThree_eq
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G))
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) : Sec18.omegaOneThree Q = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEQ := h.eq_zpowers_sup_inf_Q hET hQ hAQ hc
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQ.le.trans h.le_normalizer
  have hcmem : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hc]; exact Subgroup.mem_zpowers c
  have hc3o := h.orderOf_eq_three hc
  have hc1 : c ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hc3o; omega
  have hc3 : c ^ 3 = 1 := by simpa using h.isE27.1.2 c hcmem.1
  have hcL : c ∉ L := h.not_mem_of_mem_sectionCentralizer hcmem hc1
  have hcQ : c ∈ Q := hAQ hcmem.1
  have hBA : (Q ⊓ L : Subgroup G) ≤ A := by rw [hEQ]; exact le_sup_right
  have key : ∀ q ∈ Q, q ^ 3 = 1 → q ∈ A := by
    intro q hqQ hq3
    by_contra hqA
    have hqN : q ∈ Subgroup.normalizer (L : Set G) := hQN hqQ
    have hcomm : q * c = c * q := h.mul_comm_of_mem hQ hAQ hc q hqQ
    have hqc : q ∉ Subgroup.zpowers c := fun hh =>
      hqA (Subgroup.zpowers_le.mpr hcmem.1 hh)
    have hq1 : q ≠ 1 := fun h1 => hqA (h1 ▸ A.one_mem)
    have hqo : orderOf q = 3 := orderOf_eq_prime hq3 hq1
    have hQnil : Group.IsNilpotent Q := hQ.isPGroup.isNilpotent
    have hBn : ((Q ⊓ L : Subgroup G).subgroupOf Q).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hQN hg⟩
    have hBne : (Q ⊓ L : Subgroup G).subgroupOf Q ≠ ⊥ := by
      intro hbot
      have h9 : Nat.card ((Q ⊓ L : Subgroup G).subgroupOf Q) = 9 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h.card_inf_Q hQ]
      rw [hbot, Subgroup.card_bot] at h9
      omega
    obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hBne)
    have hzB : ((z : Q) : G) ∈ (Q ⊓ L : Subgroup G) :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
    have hzC : (z : Q) ∈ Subgroup.center Q := (Subgroup.mem_inf.mp z.2).2
    have hz1 : ((z : Q) : G) ≠ 1 := fun h1 => hz (Subtype.ext (Subtype.ext h1))
    set b₀ : G := ((z : Q) : G) with hb₀
    have hb₀Z : ∀ g ∈ Q, g * b₀ = b₀ * g := fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC ⟨g, hg⟩)
    have hb₀3 : b₀ ^ 3 = 1 := (h.isElemAbelian_inf_Q hQ).2 b₀ hzB
    obtain ⟨hEe, hEcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute (r := 3)
      (X := Subgroup.zpowers c) (by rw [Nat.card_zpowers, hc3o]) hqo hqc fun a ha => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact ((show Commute c q from hcomm.symm).zpow_left i).eq
    have hEQ' : (Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) ≤ Q :=
      sup_le (Subgroup.zpowers_le.mpr hcQ) (Subgroup.zpowers_le.mpr hqQ)
    have hb₀E : b₀ ∉ (Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) := by
      intro hmem
      have hx' : b₀ ∈ ((Subgroup.zpowers c : Set G) * (Subgroup.zpowers q : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers c)
          (Subgroup.zpowers q) (zpowers_le_normalizer_zpowers_of_commute hcomm)]
        exact hmem
      obtain ⟨u, hu, v, hv, huv⟩ := hx'
      have hvA : v ∈ A := by
        have : v = u⁻¹ * b₀ := by rw [← huv]; group
        rw [this]
        exact A.mul_mem (A.inv_mem (Subgroup.zpowers_le.mpr hcmem.1 hu)) (hBA hzB)
      have hv1 : v = 1 := by
        by_contra hv1
        have hzq := Sec18.Item186Proof.zpowers_eq_of_mem' hqo hv hv1
        have hqv : q ∈ Subgroup.zpowers v := by rw [hzq]; exact Subgroup.mem_zpowers q
        exact hqA ((Subgroup.zpowers_le.mpr hvA) hqv)
      have huv' : u = b₀ := by simpa [hv1] using huv
      have hu1 : u = 1 := by
        by_contra hu1
        have hzc := Sec18.Item186Proof.zpowers_eq_of_mem' hc3o hu hu1
        have hcu : c ∈ Subgroup.zpowers u := by rw [hzc]; exact Subgroup.mem_zpowers c
        exact hcL ((Subgroup.zpowers_le.mpr (huv' ▸ hzB.2)) hcu)
      exact hz1 (huv' ▸ hu1)
    have hV : IsE27 ((Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) ⊔
        Subgroup.zpowers b₀) :=
      isE27_sup_zpowers hEe (hEcard.trans (by norm_num)) hb₀E hb₀3 fun e he =>
        hb₀Z e (hEQ' he)
    have hVQ : (Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) ⊔ Subgroup.zpowers b₀ ≤ Q :=
      sup_le hEQ' (Subgroup.zpowers_le.mpr hzB.1)
    have hQM : Q ≤ M := le_of_isPGroup_of_le h.hyp191 h.isE27 h.mem_scriptM hQ.isPGroup hAQ
    have hM' := mem_scriptM_gamma_of_le h.hyp191 hET h.isE27 h.mem_scriptM hV (hVQ.trans hQM)
    have hE2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) :=
      two_le_pRank_of_elemAbelian hEe ((by norm_num : (9 : ℕ) ≤ 3 ^ 2).trans hEcard.ge)
    have hqM : Subgroup.normalizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) :
        Set G) ≤ M := fun x hx => hM'.2 (normalizer_le_gamma le_sup_left hE2 hx)
    have hinn := h.barAut_mem_range hET hQ hAQ hc hqQ hqN hq3 hqM
    have hmem := h.mem_sup_of_inner hQ hAQ hc hqQ hqN hq3 hinn
    exact hqA (hEQ ▸ hmem)
  apply le_antisymm
  · exact (Subgroup.closure_le A).mpr fun x hx => key x hx.1 hx.2
  · intro a ha
    exact Subgroup.subset_closure ⟨hAQ ha, by simpa using h.isE27.1.2 a ha⟩

end CFSG.RankThree.PartTwo.Late
