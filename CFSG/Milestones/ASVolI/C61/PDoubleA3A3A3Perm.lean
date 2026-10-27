module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.Milestones.ASVolI.C61.PDoubleA3A3A3Basic

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.DoubleA3

open CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

namespace A3A3

theorem normalizer_conjR (h : A3A3 T M H S L s) {g : G} (hg : g ∈ S) :
    conjJoin S L ≤ normalizer (conjR L g : Set G) := by
  have hLN : conjJoin S L ≤ normalizer (L : Set G) := by
    rw [h.join]
    exact sup_le Subgroup.le_normalizer
      (C5.le_normalizer_of_commute (fun u hu a ha => (h.comm_elem a ha u hu).symm))
  have h1 := C5.conjSubgroup_mono hLN g
  rw [C5.conjSubgroup_normalizer, C5.conjSubgroup_eq_self (C56.S_le_normalizer_conjJoin L hg)] at h1
  exact h1

theorem conj_cases (h : A3A3 T M H S L s) (hU0 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    {g : G} (hg : g ∈ S) :
    (conjR (blockU L) g = blockU L ∧ conjR L g = L) ∨
      (conjR (blockU L) g = blockU2 L s ∧ conjR L g = conjR L s) := by
  have hA := h.isA4
  have hAs := h.isA4s
  have hAg : IsA4Block (conjR L g) (conjR (blockU L) g) := hA.conj g
  have hU0eq := h.blockU0_eq hU0
  have hL0N := h.normalizer_conjR hg
  have hLL0 : L ≤ conjJoin S L := by rw [h.join]; exact le_sup_left
  have hLsL0 : conjR L s ≤ conjJoin S L := by rw [h.join]; exact le_sup_right
  have hXle : conjR (blockU L) g ≤ blockU L ⊔ blockU2 L s := by
    rw [← hU0eq]; exact conjR_le_conjJoin' hg
  have hLX : L ≤ normalizer (conjR (blockU L) g : Set G) := by
    intro l hl
    have : l ∈ normalizer (blockU (conjR L g) : Set G) :=
      C1.mem_normalizer_blockU (hL0N (hLL0 hl))
    rwa [blockU_conjR] at this
  have hUU₂ : ∀ u ∈ blockU L, ∀ v ∈ blockU2 L s, u * v = v * u := fun u hu v hv =>
    h.comm_elem u (hA.le hu) v (hAs.le hv)
  have hLU₂ : ∀ l ∈ L, ∀ v ∈ blockU2 L s, l * v = v * l := fun l hl v hv =>
    h.comm_elem l hl v (hAs.le hv)
  have hMle : conjR L g ≤ L ⊔ conjR L s := by
    rw [← h.join]; exact conjR_le_conjJoin' hg
  rcases hA.eq_or_eq_of_le_sup hUU₂ hLU₂ hXle hAg.card_U hAs.card_U hLX with hX | hX
  · left
    refine ⟨hX, ?_⟩
    rw [hX] at hAg
    exact hA.eq_of_le_sup hAs hAg h.comm_elem h.inf_Ls hMle
      (fun l hl => hL0N (hLsL0 hl))
  · right
    refine ⟨hX, ?_⟩
    rw [hX] at hAg
    exact hAs.eq_of_le_sup hA hAg (fun a ha b hb => (h.comm_elem b hb a ha).symm)
      (by rw [inf_comm]; exact h.inf_Ls) (by rw [sup_comm]; exact hMle)
      (fun l hl => hL0N (hLL0 hl))

end A3A3

end CFSG.QuasithinUnique.burnsideC56_P.DoubleA3
