module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)

namespace OneComp

variable {K : Type} [Group K] [Finite K] {J M X P : Subgroup K}

theorem sit (h : OneComp J M X P) : Sit ↥J := by
  obtain ⟨hsyl, helem, hcard⟩ := h.sylow_subgroupOf
  have hncard : 9 ∣ Nat.card ↥J := by
    rw [← h.card_eq]
    exact Subgroup.card_dvd_of_le h.sylow.le
  have hnonab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hnab
    have hcomm : ∀ a b : ↥J, a * b = b * a := by
      intro a b
      by_contra hab
      exact hnab ⟨a, b, hab⟩
    haveI : IsMulCommutative ↥J := IsMulCommutative.of_comm hcomm
    have hp : (Nat.card ↥J).Prime := (Group.is_simple_iff_prime_card (α := ↥J)).mp h.simple
    rcases hp.eq_one_or_self_of_dvd 9 hncard with h91 | h9p
    · norm_num at h91
    · rw [← h9p] at hp
      exact (by norm_num : ¬ Nat.Prime 9) hp
  have hKJ : CFSG.Open.IsKGroup ↥J := h.isKGroup.subgroup J
  haveI : IsSimpleGroup ↥J := h.simple
  have hcat : CFSG.Open.IsCatalogGroup ↥J :=
    CFSG.KCore.KGroupNonab.catalogue_self CFSG.Open.isCatalogGroup_isoInvariant hKJ hnonab
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) = 2 := by
    refine le_antisymm ?_ ?_
    · refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
      intro E _ hEelem
      have hEp : IsPGroup 3 E := fun x =>
        ⟨1, by
          rw [pow_one]
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          exact hEelem.2 (x : ↥J) x.2⟩
      obtain ⟨S, hES⟩ := hEp.exists_le_sylow
      have hSX : Nat.card (S : Subgroup ↥J) = Nat.card (X.subgroupOf J) := by
        rw [Sylow.card_eq_multiplicity, hsyl.card_eq, Subgroup.card_top]
      calc Nat.card E ≤ Nat.card (S : Subgroup ↥J) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hES)
        _ = Nat.card (X.subgroupOf J) := hSX
        _ = 3 ^ 2 := by rw [hcard]; norm_num
    · exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top helem
        (by rw [hcard]; norm_num)
  exact ⟨h.simple, hnonab, hcat, hrank, ⟨X.subgroupOf J, hsyl, helem, hcard⟩⟩

end OneComp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
