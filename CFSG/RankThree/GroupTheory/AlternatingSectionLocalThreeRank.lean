module

public import CFSG.RankThree.Coprime.LocalPrimeSectionCover
public import CFSG.RankThree.GroupTheory.SteinbergCEAlternatingDegreeThirteen
public import CFSG.RankThree.PartOne.N143.AltTwoRank

public section

namespace CFSG.RankThree.GroupTheory

theorem four_le_twoLocalPrimeRank_three_of_section_alternating {G : Type} [Group G] [Finite G]
    {n : ℕ} (hn : 13 ≤ n) (H : Subgroup G) (π : H →* alternatingGroup (Fin n))
    (hπ : Function.Surjective π) : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 G := by
  by_contra hlt
  have h : CFSG.Open.twoLocalPrimeRank 3 G ≤ 3 := by omega
  have h5 : 5 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
  have hnc : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
    by_contra! hc
    have : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨hc⟩⟩
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp this
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  obtain ⟨U, hU, hUc⟩ :=
    CFSG.RankThree.PartOne.N143.exists_isElementaryAbelian_two_pow_five (n := n) (by omega)
  obtain ⟨Y, _, _, hYp, φ, hφ, hφZ, hYrank⟩ :=
    CFSG.RankThree.Coprime.exists_central_cover_of_twoLocalPrimeRank_le 3
      (r := 3) (by norm_num) h hsimple hnc ⟨U, hU, hUc⟩ H π hπ
  let π' : (⊤ : Subgroup Y) →* alternatingGroup (Fin n) :=
    φ.comp Subgroup.topEquiv.toMonoidHom
  have hπ' : Function.Surjective π' := hφ.comp Subgroup.topEquiv.surjective
  have hZ : π'.ker ≤ Subgroup.center (⊤ : Subgroup Y) := by
    intro w hw
    have hw' : (w : Y) ∈ φ.ker := hw
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hφZ hw') (g : Y)
  have h4 :=
    ((alternating_central_covers_degree_thirteen_force_two_local_three_rank_four
      π' hπ' hZ).2.1 hn).1
  have h4' : 4 ≤ CFSG.Open.twoLocalPrimeRank 3 Y := h4
  omega

end CFSG.RankThree.GroupTheory
