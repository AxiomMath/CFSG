module

public import CFSG.OddTranspositions.PartThree.Statements
public import Certificates.Certificate43
public import Certificates.Certificate113
import CFSG.OddTranspositions.PartThree.EightNine.Tools
import CFSG.OddTranspositions.PartThree.EightNine.O4
import CFSG.OddTranspositions.FiveThreeQZ
import CFSG.OddTranspositions.SixTenPetersen
import CFSG.OddTranspositions.SixSevenLocalStep
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.BlockAction2
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.WidthOne
import CFSG.StronglyEmbedded.PSL2Facts

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

theorem lemma8_9_of_theorem8_7
    (h87 : Theorem8_7) : Lemma8_9 := by
  unfold Lemma8_9
  intro G _ _ D hC hrad hnw β hβ b hb x hx hxβ
  classical
  have hbH : b ∈ Halpha D hC.alpha := Subgroup.subset_closure ⟨β, hβ, hb⟩
  by_cases hO4 : O4PairData G D
  ·
    have hcen := pCore_two_le_center_Halpha_of_o4PairData hC hO4 hx
    have hxb := (Subgroup.mem_center_iff.mp hcen) ⟨b, hbH⟩
    have h' : (x : G) * b = b * (x : G) := (congrArg Subtype.val hxb).symm
    rw [h', mul_inv_cancel_right]
  by_contra hne
  set a := (x : G) * b * (x : G)⁻¹ with ha
  have hD := hC.setup.oddT
  have hblock := hC.isBlock_alpha
  have hβblock : IsBlock D β := isBlock_of_mem_blockClass hC.setup.normal hblock hβ.1
  have hbD : b ∈ D := hβ.2.1 hb
  have hb2 : b * b = 1 := hD.mul_self_eq_one hbD
  have habQ : a * b ∈ (CFSG.pCore 2 (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
    conj_mul_mem_map_pCore hx hbH hb2
  have hab1 : a * b ≠ 1 := fun h1 =>
    hne ((mul_eq_one_iff_eq_inv.mp h1).trans (inv_eq_of_mul_eq_one_right hb2))
  have hab : Commute a b := commute_of_mul_mem_of_isPGroup hD
    ((CFSG.pCore_isPGroup (p := 2) (G := Halpha D hC.alpha)).map _) (hC.setup.normal _ _ hbD)
    hbD habQ
  have hperp : ∀ γ ∈ perp D hC.alpha, (fun y => a * b * y * (a * b)⁻¹) '' γ = γ := by
    intro γ hγ
    by_cases hγβ : γ ∈ perp D β
    · exact image_mul_mem_of_mem_perp hβblock hγβ hxβ hb
    have hγD : γ ∈ Dalpha D hC.alpha := by
      rcases mem_perp_iff.mp hγ with hγD | rfl
      · exact hγD
      · exact absurd (mem_perp_iff.mpr (Or.inl (Dalpha_symm hβ hblock.subset))) hγβ
    obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hblock.nonempty hγD.1
    have hX := isSolvable_closure_of_mul_mem_map_pCore hbH
      (Subgroup.subset_closure ⟨γ, hγD, hc⟩) hb2 (hD.mul_self_eq_one (hγD.2.1 hc)) habQ
    have hmem := conj_mul_mem_of_mem_blockClass_of_isSolvable hC hβ.1
      ⟨mem_blockClass_of_mem_blockClass hβ.1 hγD.1, hγβ⟩ hxβ hb hab hne hc hX
    exact eq_of_mem_of_mem_blockClass hblock (conj_image_mem_blockClass hγD.1 _) hγD.1
      ⟨_, ⟨c, hc, rfl⟩, hmem⟩
  have htriv := actsTriviallyOnBlocks_of_perp_of_theorem8_7 h87 hC hrad hO4 hβ
    (by rintro y ⟨δ, hδ, hy⟩; exact commute_mul_of_mem_Dalpha hδ hxβ hb hy)
    (image_mul_mem_alpha hβblock hxβ hb) hperp
  exact hab1 ((QZ.sixSix_dichotomy_of_rad hC hrad).resolve_left hnw _ htriv)

end CFSG.OddTranspositions.PartThree

end
