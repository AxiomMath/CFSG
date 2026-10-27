module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
public import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.Timmesfeld.Bridge.Asc72ZQuot

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_alpha_subset_Halpha_of_pCore_eq_bot (hC : HypothesisC D)
    (hQ : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) :
    ¬ hC.alpha ⊆ (Halpha D hC.alpha : Set G) := by
  intro hsub
  set d' : Halpha D hC.alpha := ⟨hC.d, hsub hC.d_mem_alpha⟩ with hd'
  have hcent : d' ∈ Subgroup.center (Halpha D hC.alpha) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC g.2)
  have hnorm : (Subgroup.zpowers d').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcent)
  have hdd : d' ^ 2 ^ 1 = 1 :=
    Subtype.ext (by simpa [pow_two] using hC.setup.oddT.mul_self_eq_one hC.hd)
  have hp : IsPGroup 2 (Subgroup.zpowers d') := CentralQuot.isPGroup_zpowers_of_pow hdd
  have hle : Subgroup.zpowers d' ≤ CFSG.pCore 2 (Halpha D hC.alpha) := le_sSup ⟨hnorm, hp⟩
  rw [hQ] at hle
  have h1 : d' = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers d'))
  exact hC.setup.oddT.ne_one hC.hd (congrArg Subtype.val h1)

theorem tenTwo_of_pCore_eq_bot
    (h : ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
      TenHyp hC f n → CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) : TenTwo :=
  fun G _ _ D hC f n hT =>
    ⟨h G D hC f n hT, not_alpha_subset_Halpha_of_pCore_eq_bot hC (h G D hC f n hT)⟩

end CFSG.OddTranspositions.PartThree

end
