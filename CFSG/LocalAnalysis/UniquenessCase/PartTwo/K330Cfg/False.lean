module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.BridgeAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Index

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy)

namespace OneComp

variable {K : Type} [Group K] [Finite K] {J M X P : Subgroup K}

theorem false_of_excl (h : OneComp J M X P) (hE : Excl ↥J) : False := by
  obtain ⟨hX1, hX2, hX3⟩ := h.sylow_subgroupOf
  rcases hE with h27 | hArith | hAut | ⟨hRank, hStep⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc := hX1.card_eq
    rw [hX3, Subgroup.card_top] at hc
    have h3 : 3 ^ 3 ∣ Nat.card ↥J := by simpa [Big27] using h27
    have hle : 3 ≤ (Nat.card ↥J).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h3
    have hd : 3 ^ 3 ∣ 3 ^ (Nat.card ↥J).factorization 3 := pow_dvd_pow 3 hle
    rw [← hc] at hd
    norm_num at hd
  · obtain ⟨m, hm1, hm2, hm3, hm4⟩ := h.exists_index
    have := hArith m hm1 hm2 hm3
    omega
  · obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hc₁, hc₂, hne, hperm⟩ := h.pair_subgroupOf
    obtain ⟨n, hn, hnot⟩ := hAut _ hX1 hX2 hX3 Z₁ Z₂ hZ₁ hZ₂ hc₁ hc₂ hne
    exact hnot (hperm n hn)
  · by_cases h7 : 7 ∣ Nat.card J
    · obtain ⟨R, hR1, hR2, hR3, hR4⟩ := h.exists_cyclic_sylow_seven h7
      exact hRank _ _ hX1 hX2 hX3 hR1 hR2 hR3 hR4
    · obtain ⟨W, hW1, hW2, hW3⟩ := h.exists_automorphism_seven h7
      have htop := hStep h7 W _ hW1 hX1 hX2 hX3 hW2
      apply h.not_le
      have hle : normalizer (((X.subgroupOf J : Subgroup ↥J)) : Set ↥J) ⊔ fixedBy W ≤
          M.subgroupOf J :=
        sup_le (fun n hn => h.mem_of_mem_normalizer_subgroupOf n hn) (fun x hx => hW3 x hx)
      rw [htop, top_le_iff] at hle
      intro g hg
      have : (⟨g, hg⟩ : ↥J) ∈ M.subgroupOf J := by rw [hle]; exact mem_top _
      exact this

end OneComp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
