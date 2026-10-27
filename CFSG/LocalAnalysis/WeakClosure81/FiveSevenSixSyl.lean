module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem two_pow_factorization_dvd_card_inf {H L M : Subgroup G} (hMH : M ≤ H)
    (hodd : Odd (M.relIndex H)) (hLH : L ≤ H) (hL : (L.subgroupOf H).Normal) :
    2 ^ (Nat.card ↥L).factorization 2 ∣ Nat.card ↥(L ⊓ M) := by
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  have hPModd : Odd (P.relIndex M) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact (CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.2
  have hrel : P.relIndex M * M.relIndex H = P.relIndex H :=
    Subgroup.relIndex_mul_relIndex P M H hP.le hMH
  have hPHodd : Odd (P.relIndex H) := by
    rw [← hrel]
    exact Nat.odd_mul.mpr ⟨hPModd, hodd⟩
  have hPH : CFSG.ABGLocalTools.IsSylowOf 2 P H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hP.le.trans hMH, hP.isPGroup, ?_⟩
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hPHodd
  have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).1 hL
  have hPL : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ L) L := hPH.inf_of_le_normalizer hLH hHL
  rw [← hPL.card_eq]
  exact Subgroup.card_dvd_of_le (le_inf inf_le_right (inf_le_left.trans hP.le))

end CFSG.LocalAnalysis.WeakClosure81
