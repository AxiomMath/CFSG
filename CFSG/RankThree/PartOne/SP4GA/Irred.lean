module

public import CFSG.RankThree.PartOne.K1214.XFrame
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartOne.SP4GA

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.K1214

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem exists_not_invariant (ctx : Fus12Ctx G p A c L E) {β β' : G} (hβ : β ∈ E ⊓ L)
    (hβ1 : β ≠ 1) (hβ' : β' ∈ E ⊓ L) (hβ'n : β' ∉ Subgroup.zpowers β) :
    ∃ w ∈ L, w ∈ Subgroup.normalizer (E : Set G) ∧ w * β * w⁻¹ ∉ Subgroup.zpowers β := by
  by_contra hcon
  push Not at hcon
  have hE : Subgroup.zpowers β ≤ E := Subgroup.zpowers_le.2 hβ.1
  have hinv : torusInvariant E L (Subgroup.zpowers β) := by
    intro w hw u hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    have h1 : w * β ^ j * w⁻¹ = (w * β * w⁻¹) ^ j := (conj_zpow).symm
    rw [h1]
    exact Subgroup.zpow_mem _ (hcon w (Subgroup.mem_inf.1 hw).1 (Subgroup.mem_inf.1 hw).2) j
  have hne1 : Subgroup.zpowers β ≠ ⊥ := by
    intro h
    apply hβ1
    have : β ∈ Subgroup.zpowers β := Subgroup.mem_zpowers β
    rw [h] at this
    exact (Subgroup.mem_bot).1 this
  have hcE : c ∈ E := c_mem_E ctx
  have hzL : Subgroup.zpowers β ≤ L := Subgroup.zpowers_le.2 hβ.2
  have hneE : Subgroup.zpowers β ≠ E := by
    intro h
    apply ctx.c_not_mem
    have : c ∈ Subgroup.zpowers β := h ▸ hcE
    exact hzL this
  rcases ctx.facts.four.1 _ hE hinv hne1 hneE with h | h
  · apply ctx.c_not_mem
    have : c ∈ Subgroup.zpowers β := h ▸ Subgroup.mem_zpowers c
    exact hzL this
  · have h2 : ⁅E, L ⊓ torusNormalizer E⁆ = E ⊓ L :=
      (pCoreFixed_eq_commutator_of_facts ctx.facts ctx.hyp ctx.core).symm.trans ctx.ten.1
    rw [h2] at h
    exact hβ'n (h ▸ hβ')

end CFSG.RankThree.PartOne.SP4GA
