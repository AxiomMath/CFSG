module

public import CFSG.Quasithin.EmptyFaithful.S153YA3Perm
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.Quasithin.YG

open CFSG.QuasithinUnique
open CFSG.QuasithinUnique.DoubleA3
open CFSG.Quasithin.YG.DoubleA3
open CFSG.QuasithinUnique.C56

open CFSG.Open CFSG.Quasithin Subgroup CFSG.QuasithinUnique.DoubleA3

namespace C56

variable {G : Type} [Group G] [Finite G] {H S L : Subgroup G}

theorem blockU0_eq_pCoreOf {s : G} (h : A3A3 H S L s) :
    blockU0 S L = pCoreOf 2 (conjJoin S L) := by
  have hLs : IsShort2 L := h.isShort
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hU2 : IsPGroup 2 (blockU L) := C1.isPGroup_blockU hLs
  apply le_antisymm
  · refine iSup_le fun g => ?_
    have hg : (g : G)⁻¹ ∈ S := S.inv_mem g.2
    have hconj : (blockU L).map (MulAut.conj (g : G)).toMonoidHom =
        conjR (blockU L) (g : G)⁻¹ := by
      simp [conjR]
    rw [hconj]
    have hN : conjJoin S L ≤ normalizer ((conjR (blockU L) (g : G)⁻¹ : Subgroup G) : Set G) := by
      intro x hx
      have h1 := C1.mem_normalizer_blockU (h.normalizer_conjR hg hx)
      rwa [blockU_conjR] at h1
    have hle : conjR (blockU L) (g : G)⁻¹ ≤ conjJoin S L :=
      (C5.conjSubgroup_mono hUL _).trans (conjR_le_conjJoin' hg)
    exact le_pCoreOf_of_normalizes hle hN (E3.isPGroup_conjSubgroup hU2 _)
  · have hV := h.isSylowTwoOf_V
    have hle : pCoreOf 2 (conjJoin S L) ≤ blockU L ⊔ blockU2 L s :=
      hV.le_of_normalizes (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _)
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _)
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    refine hle.trans (sup_le ?_ ?_)
    · calc blockU L = conjR (blockU L) 1 := (conjSubgroup_one _).symm
        _ ≤ blockU0 S L := conjR_le_conjJoin' S.one_mem
    · exact conjR_le_conjJoin' h.s_mem

theorem baumann_double_A3 (hcs : WGen H S L) (h3 : IsAltType L 3)
    (hne : conjJoin S L ≠ L) :
    blockU L ≤ baum S ∧ baum S ≤ normalizer (L : Set G) ∧ IsSylowTwoOf (baum S) (L ⊔ baum S) := by
  classical
  obtain ⟨s, h⟩ := exists_A3A3 hcs h3 hne
  have hLs : IsShort2 L := hcs.block.1.1
  have hS2 : IsPGroup 2 S := hcs.sylow.isPGroup
  have hUL : blockU L ≤ L := (C1.blockU_le_blockQ hLs).trans (C1.blockQ_le L)
  have hLL0 : L ≤ conjJoin S L := by rw [h.join]; exact le_sup_left
  have hL0U : conjJoin S L ≤ normalizer (blockU L : Set G) := by
    rw [h.join]
    exact sup_le (C1.le_normalizer_blockU L)
      (C5.le_normalizer_of_commute (fun a ha u hu => (h.comm_elem u (hUL hu) a ha).symm))
  have hUP : blockU L ≤ pCoreOf 2 (conjJoin S L) :=
    le_pCoreOf_of_normalizes (hUL.trans hLL0) hL0U (C1.isPGroup_blockU hLs)
  have hL0H : conjJoin S L ≤ H := by rw [hcs.eq_join]; exact le_sup_left
  have hHNP : H ≤ normalizer ((pCoreOf 2 (conjJoin S L) : Subgroup G) : Set G) := by
    rw [hcs.eq_join]
    refine sup_le (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _) ?_
    intro g hg
    rw [← conjSubgroup_eq_iff_mem_normalizer, C5.conjSubgroup_pCoreOf,
      C5.conjSubgroup_eq_self (S_le_normalizer_conjJoin L hg)]
  have hUS : blockU L ≤ S := by
    have h1 : pCoreOf 2 (conjJoin S L) ≤ pCoreOf 2 H :=
      le_pCoreOf_of_normalizes
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans hL0H) hHNP
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    exact hUP.trans (h1.trans hcs.sylow.pCoreOf_le)
  obtain ⟨hUB, -⟩ := a3_blockU_le_baum hS2 hLs h3 hUS hcs.thompson
  have hU0 := blockU0_eq_pCoreOf h
  have hperm : ∀ g ∈ baum S, conjSubgroup L g = L ∨
      ∀ a ∈ L, ∀ b ∈ conjSubgroup L g, a * b = b * a := by
    intro g hg
    have hgS : g ∈ S := hg.1
    rcases h.conj_cases hU0 hgS with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact Or.inl h1
    · refine Or.inr fun a ha b hb => h.comm_elem a ha b ?_
      have hb' : b ∈ conjR L g := hb
      rw [h1] at hb'
      exact hb'
  have hBN : baum S ≤ normalizer (L : Set G) :=
    a3_baum_le_normalizer hS2 hLs h3 hUS hcs.thompson hperm
  exact ⟨hUB, hBN, a3_isSylowTwoOf_sup hLs h3 (hS2.to_le inf_le_left) hUB hBN⟩

end C56

end CFSG.Quasithin.YG
