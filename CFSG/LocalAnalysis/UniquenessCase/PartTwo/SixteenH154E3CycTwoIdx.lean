module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16h_e3_CycTwoIdx_not_dvd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Ω : Type*} [Group Ω] [Finite Ω] {Mb N P : Subgroup Ω}
    (hPN : P ≤ N) (hNM : N ≤ Mb) (hidx : N.relIndex Mb = 2)
    (hall : ∀ n ∈ N, (∃ k : ℕ, orderOf n = q ^ k) → n ∈ P) : ¬ q ∣ P.relIndex Mb := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro hdiv
  let S : Sylow q ↥N := Classical.choice Sylow.nonempty
  have hSP : S.map N.subtype ≤ P := by
    rintro x ⟨s, hs, rfl⟩
    obtain ⟨k, hk⟩ := S.isPGroup'.exists_orderOf_eq_pow ⟨s, hs⟩
    refine hall (s : Ω) s.2 ⟨k, ?_⟩
    rw [Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe (⟨s, hs⟩ : ↥(S : Subgroup ↥N))).trans hk
  have hSle : S ≤ P.subgroupOf N := Subgroup.map_le_iff_le_comap.1 hSP
  have hnot : ¬ q ∣ P.relIndex N := fun h =>
    S.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hSle))
  have hmul : P.relIndex N * 2 = P.relIndex Mb := by
    rw [← hidx]
    exact Subgroup.relIndex_mul_relIndex (H := P) (K := N) (L := Mb) hPN hNM
  rw [← hmul] at hdiv
  rcases hq.dvd_mul.1 hdiv with h | h
  · exact hnot h
  · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
