module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Swap
public import CFSG.Quasithin.EmptyFaithful.S153WBasic

public section

namespace CFSG.QuasithinUnique.AppCS2W

open CFSG.QuasithinUnique.AppCS2 CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.DoubleA3 Equiv Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

namespace WDbl

variable {t : G} (D : WDbl H S L t)
include D

theorem conjJoin_L₂ : conjJoin S (conjR L t) = conjJoin S L := conjJoin_conjR L D.ht

theorem swap_set : WSet H S (conjR L t) where
  sylow := D.hcs.sylow
  block := ⟨CFSG.Quasithin.IsBlock2.conjByElt_of_mem D.hcs.block.1
    (H.inv_mem (D.hcs.sylow.le D.ht)), Or.inr (Or.inr D.h5₂)⟩
  thompson := by
    have h1 : conjSubgroup (thompsonJ S) t = thompsonJ S := conjR_thompsonJ D.ht
    have h2 := C5.conjSubgroup_commutator L (thompsonJ S) t
    rw [h1, D.hcs.thompson] at h2
    exact h2.symm
  eq_join := by
    rw [D.conjJoin_L₂]
    exact D.hcs.eq_join

theorem swap : WDbl H S (conjR L t) t⁻¹ where
  hcs := D.swap_set
  h5 := D.h5₂
  ht := S.inv_mem D.ht
  hne := by rw [conjR_conjR_inv]; exact D.hne.symm
  hjoin := by rw [D.conjJoin_L₂, D.hjoin, conjR_conjR_inv, sup_comm]
  hcomm := by rw [conjR_conjR_inv, Subgroup.commutator_comm]; exact D.hcomm

theorem conjR_blockU_cases {g : G} (hg : g ∈ S) :
    conjR (blockU L) g = blockU L ∨ conjR (blockU L) g = blockU2 L t := by
  rcases D.conjR_cases hg with h | h
  · left; rw [← blockU_conjR, h]
  · right
    show conjR (blockU L) g = conjR (blockU L) t
    rw [← blockU_conjR, ← blockU_conjR, h]

theorem conjR_blockU_of_mem {g : G} (hg : g ∈ s2SI S L) :
    conjR (blockU L) g = blockU L ∧ conjR (blockU2 L t) g = blockU2 L t := by
  have h1 : conjR L g = L := mem_normalizer_iff_conjR.1 hg.2
  have h2 : conjR (conjR L t) g = conjR L t :=
    mem_normalizer_iff_conjR.1 (D.s2SI_le_normalizer_L₂ hg)
  refine ⟨?_, ?_⟩
  · rw [← blockU_conjR, h1]
  · show conjR (conjR (blockU L) t) g = conjR (blockU L) t
    rw [← blockU_conjR, ← blockU_conjR, h2]

theorem conjR_blockU_of_not_mem {g : G} (hg : g ∈ S) (hn : g ∉ normalizer (L : Set G)) :
    conjR (blockU L) g = blockU2 L t ∧ conjR (blockU2 L t) g = blockU L := by
  rcases D.conjR_L₂_cases hg with h | h
  · exact absurd (mem_normalizer_iff_conjR.2 h.1) hn
  · refine ⟨?_, ?_⟩
    · show conjR (blockU L) g = conjR (blockU L) t
      rw [← blockU_conjR, ← blockU_conjR, h.1]
    · show conjR (conjR (blockU L) t) g = blockU L
      rw [← blockU_conjR, ← blockU_conjR, h.2]

end WDbl

end CFSG.QuasithinUnique.AppCS2W
