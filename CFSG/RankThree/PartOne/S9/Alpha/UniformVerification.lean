module

public import CFSG.RankThree.PartOne.S9.StatementsSylow
public import CFSG.RankThree.PartOne.S9.Alpha.VerificationReduction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory Subgroup

namespace AlphaTheory

theorem normalizer_zpowers_ne_top {G : Type} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {c : G} (hc : c ≠ 1) :
    normalizer (zpowers c : Set G) ≠ ⊤ := by
  intro htop
  have hnormal : (zpowers c).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers c) with h | h
  · exact hc (by simpa using h)
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ zpowers c := h ▸ Subgroup.mem_top a
    have hb : b ∈ zpowers c := h ▸ Subgroup.mem_top b
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hab (by rw [← zpow_add, ← zpow_add, add_comm])

end AlphaTheory

theorem sectionNineUniformAlphaVerification_of (hPSR : ProperSubgroupResidual)
    (hPCB : SectionNinePlaneCommutatorBound) : SectionNineUniformAlphaVerification := by
  intro G _ _ p hsec hgood A hA hAcard
  have : IsSimpleGroup G := hsec.simple
  have hp : p.Prime := hsec.prime
  have hp2 : p ≠ 2 := by have := hsec.three_lt; omega
  refine sectionNineAlphaVerificationReduction G p hp hp2 A hA hAcard ?_ ?_
  · intro c hc hc1 D hDA hDcard hcD
    exact hPCB G p hsec hgood A hA hAcard c hc hc1 D hDA hDcard hcD
  · intro c hc hc1 B hBA hBcard t htB ht1
    have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      SteinbergBY.mul_comm_of_isMulCommutative hx hy
    have hcord : orderOf c = p := SteinbergBY.orderOf_eq_of_isElementaryAbelian hp hc hc1
    have hAC : A ≤ normalizer (zpowers c : Set G) := fun x hx =>
      Subgroup.centralizer_le_normalizer _ (by
        rw [← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
          mem_centralizer_singleton_iff]
        exact (hcomm x hx c hc))
    have hBel : IsElementaryAbelian p B := AlphaTheory.isElementaryAbelian_of_le_alpha hA hBA
    exact hPSR G hsec.kProper (by rw [hsec.evenRank_eq]) p hp (by have := hsec.three_lt; omega) B
      hBel hBcard (normalizer (zpowers c : Set G)) (hBA.trans hAC)
      (AlphaTheory.normalizer_zpowers_ne_top hsec.nonabelian hc1) t htB ht1

end CFSG.RankThree.PartOne
