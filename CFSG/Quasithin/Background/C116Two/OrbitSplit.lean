module

public import CFSG.Quasithin.Background.C116Two.Ctx
public import CFSG.Quasithin.Background.C116Two.OrbitConj
public import CFSG.Quasithin.Background.C1PackC19
public import CFSG.Quasithin.Background.C2Aux

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem orbitW_le_blockU_sup {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    orbitW A L ≤ blockU L ⊔ (orbitW A L ⊓ Subgroup.centralizer (L : Set G)) := by
  refine iSup₂_le fun a ha => ?_
  by_cases hLa : conjByElt a L = L
  · rw [hLa]
    exact le_sup_left
  · have haH : a ∈ H := h.sylow.1 (hAT ha)
    have hLb : IsBlock2 H (conjByElt a L) := IsBlock2.conjByElt_of_mem h.chi.1 haH
    have hne : L ≠ conjByElt a L := Ne.symm hLa
    have hcomm : ⁅L, conjByElt a L⁆ = ⊥ :=
      distinctBlocksCommuteStatement H L (conjByElt a L) h.charTwo h.chi.1 hLb hne
    have hc : L ≤ Subgroup.centralizer (conjByElt a L : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hcent : blockU (conjByElt a L) ≤ Subgroup.centralizer (L : Set G) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hgL : g ∈ conjByElt a L := blockU_le_left (conjByElt a L) hg
      exact ((Subgroup.mem_centralizer_iff.mp (hc hl)) g hgL).symm
    have hW : blockU (conjByElt a L) ≤ orbitW A L := le_iSup₂_of_le a ha le_rfl
    exact le_sup_of_le_right (le_inf hW hcent)

end CFSG.Quasithin.C116Two
