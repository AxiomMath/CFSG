module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLFiveLocal
public import Certificates.Data.McLFivePairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbeddingD2 CFSG.RankThree.Native Certificates.McLFivePairs
open Certificates.MaxD2Heis (mclTabA mclTabB)

theorem closure_four_eq_sup {Q : Type*} [Group Q] (U V G : Q) :
    Subgroup.closure {x | x ∈ [U, V, G⁻¹ * U * G, G⁻¹ * V * G]} =
      Subgroup.closure {U, V} ⊔ (Subgroup.closure {U, V}).map (MulAut.conj G⁻¹).toMonoidHom := by
  have hset : {x | x ∈ [U, V, G⁻¹ * U * G, G⁻¹ * V * G]}
      = ({U, V} : Set Q) ∪ (MulAut.conj G⁻¹) '' ({U, V} : Set Q) := by
    ext x
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, MulAut.conj_apply, inv_inv]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨U, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨V, Or.inr rfl, rfl⟩
    · rintro ((hx | hx) | ⟨y, hy, hxy⟩)
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · rw [← hxy]
        rcases hy with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
  rw [hset, Subgroup.closure_union, MonoidHom.map_closure]
  rfl

theorem rep_append {n : ℕ} {b c : Array Tab} {L M : List (Equiv.Perm (Fin n))}
    (hb : ∀ j, TabRep (b.getD j (idTab n)) (L.getD j 1))
    (hc : ∀ j, TabRep (c.getD j (idTab n)) (M.getD j 1)) (hlen : b.size = L.length) :
    ∀ j, TabRep ((b ++ c).getD j (idTab n)) ((L ++ M).getD j 1) := by
  intro j
  rcases lt_or_ge j b.size with hj | hj
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append, if_pos hj,
      List.getD_append L M 1 j (by omega), ← Array.getD_eq_getD_getElem?]
    exact hb j
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_append, if_neg (by omega),
      List.getD_append_right L M 1 j (by omega), ← Array.getD_eq_getD_getElem?, hlen]
    exact hc (j - L.length)

theorem rep_invTab_of_hasInv {g : Tab} {G : Equiv.Perm (Fin 275)} (hg : TabRep g G)
    (h : hasInv g = true) : TabRep (invTab 275 g) G⁻¹ := by
  simp only [hasInv, Bool.and_eq_true, beq_iff_eq] at h
  exact hg.inv h.1 h.2

theorem rep_conjBy {g x : Tab} {G X : Equiv.Perm (Fin 275)} (hg : TabRep g G)
    (h : hasInv g = true) (hx : TabRep x X) : TabRep (conjBy g x) (G⁻¹ * X * G) := by
  have hi := rep_invTab_of_hasInv hg h
  unfold conjBy
  exact (hi.comp hx).comp hg

theorem rep_wordIn {gs : Array Tab} {L : List (Equiv.Perm (Fin 275))}
    (hgs : ∀ j, TabRep (gs.getD j (idTab 275)) (L.getD j 1)) (h : gensOK gs = true)
    (w : List ℤ) : TabRep (wordIn gs w) (wordVal L w) := by
  have hgi : ∀ j, TabRep ((gs.map (invTab 275)).getD j (idTab 275)) (L.getD j 1)⁻¹ := by
    have h' := h
    simp only [gensOK, invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at h'
    exact CFSG.AGLEmbedding.MaxD2.inv_rep_of_check hgs h'.1 h'.2
  unfold wordIn
  exact wordT_rep L gs (gs.map (invTab 275)) hgs hgi w

theorem mem_closure_of_wordIn {gs : Array Tab} {L : List (Equiv.Perm (Fin 275))}
    (hgs : ∀ j, TabRep (gs.getD j (idTab 275)) (L.getD j 1)) (h : gensOK gs = true)
    {w : List ℤ} {t : Tab} {x : Equiv.Perm (Fin 275)} (ht : TabRep t x)
    (hw : wordIn gs w = t) : x ∈ Subgroup.closure {g | g ∈ L} := by
  have hw' := rep_wordIn hgs h w
  rw [hw] at hw'
  rw [ht.perm_eq hw']
  exact wordVal_mem L _ (fun g hg => Subgroup.subset_closure hg) w

theorem mcl_le_closure_of_words
    {gs : Array Tab} {L : List (Equiv.Perm (Fin 275))}
    (hgs : ∀ j, TabRep (gs.getD j (idTab 275)) (L.getD j 1)) (h : gensOK gs = true)
    {wa wb : List ℤ} (ha : wordIn gs wa = mclTabA) (hb : wordIn gs wb = mclTabB) :
    mcl275P ≤ Subgroup.closure {g | g ∈ L} := by
  rw [← mclP_closure_eq, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact mem_closure_of_wordIn hgs h mcl_tab_a ha
  · exact mem_closure_of_wordIn hgs h mcl_tab_b hb

theorem rep_pairGens {u v r : Tab} {U V G : Equiv.Perm (Fin 275)} (hu : TabRep u U)
    (hv : TabRep v V) (hr : TabRep r G) (h : hasInv r = true) :
    ∀ j, TabRep ((pairGens u v r).getD j (idTab 275))
      ([U, V, G⁻¹ * U * G, G⁻¹ * V * G].getD j 1) := by
  intro j
  by_cases hj : j < 4
  · interval_cases j
    · simpa [pairGens] using hu
    · simpa [pairGens] using hv
    · simpa [pairGens] using rep_conjBy hr h hu
    · simpa [pairGens] using rep_conjBy hr h hv
  · have h1 : (pairGens u v r).getD j (idTab 275) = idTab 275 := by
      unfold pairGens
      have hge : ¬ j < (#[u, v, conjBy r u, conjBy r v] : Array Tab).size := by
        simp
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dif_neg hge]
    have h2 : ([U, V, G⁻¹ * U * G, G⁻¹ * V * G].getD j 1) = 1 := by
      have hge : [U, V, G⁻¹ * U * G, G⁻¹ * V * G].length ≤ j := by
        simp
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
    rw [h1, h2]
    exact TabRep.idTab

theorem rep_blockGens {b : Array Tab} {L : List (Equiv.Perm (Fin 275))}
    (hb : ∀ j, TabRep (b.getD j (idTab 275)) (L.getD j 1)) (hlen : b.size = L.length)
    {h : Tab} {H : Equiv.Perm (Fin 275)} (hh : TabRep h H) (hinv : hasInv h = true) :
    ∀ j, TabRep ((blockGens b h).getD j (idTab 275)) ((L.map fun x => H⁻¹ * x * H).getD j 1) := by
  intro j
  unfold blockGens
  by_cases hj : j < b.size
  · have hb' : (b.map (conjBy h)).getD j (idTab 275) = conjBy h (b.getD j (idTab 275)) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    have hL' : (L.map fun x => H⁻¹ * x * H).getD j 1 = H⁻¹ * (L.getD j 1) * H := by
      simpa using (List.getD_map (l := L) (d := 1) (n := j) (f := fun x => H⁻¹ * x * H))
    rw [hb', hL']
    exact rep_conjBy hh hinv (hb j)
  · have hb' : (b.map (conjBy h)).getD j (idTab 275) = idTab 275 := by
      have hge : ¬ j < (b.map (conjBy h)).size := by
        rw [Array.size_map]
        omega
      rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dif_neg hge]
    have hL' : (L.map fun x => H⁻¹ * x * H).getD j 1 = 1 := by
      have hge : (L.map fun x => H⁻¹ * x * H).length ≤ j := by
        rw [List.length_map]
        omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, Option.getD_none]
    rw [hb', hL']
    exact TabRep.idTab

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.McLPairs
