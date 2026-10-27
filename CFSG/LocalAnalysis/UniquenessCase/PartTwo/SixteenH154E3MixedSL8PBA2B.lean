module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_mbar_maps_imgTil_inf_conj (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {d : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)}
    (hd : d ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian) :
    ∀ z ∈ imgTil ⊥ V h.hyp151.isElemAbelian
        (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
          conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x),
      d z ∈ imgTil ⊥ V h.hyp151.isElemAbelian
        (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
          conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x) := by
  have hV := h.hyp151.isElemAbelian
  set W : Subgroup G := wSub (⊥ : Subgroup G) V hV L with hWdef
  set Wx : Subgroup G := conjSubgroup W x with hWxdef
  set U : Subgroup G := W ⊓ Wx with hUdef
  have hWmem : W ∈ wConj D.M (⊥ : Subgroup G) V hV L := by
    refine ⟨1, D.M.one_mem, ?_⟩
    rw [hWdef, conjSubgroup_one]
  have hWxmem : Wx ∈ wConj D.M (⊥ : Subgroup G) V hV L := by
    refine ⟨x, hxM, ?_⟩
    rw [hWxdef, hWdef]
  have hcard : (wConj D.M (⊥ : Subgroup G) V hV L).ncard = 2 := by
    rw [ncard_wConj D h.hyp151 hV]
    exact hs2
  have hWxne : W ≠ Wx := by
    intro heq
    have hconj : conjSubgroup W x = W := by
      rw [← hWxdef]
      exact heq.symm
    have hmem : x ∈ D.M ⊓ normalizer (W : Set G) :=
      ⟨hxM, conjSubgroup_eq_iff_mem_normalizer.1 hconj⟩
    rw [hWdef, inf_normalizer_wSub_eq_nBar D h.hyp151 hV] at hmem
    exact hxn hmem
  have hpair : ({W, Wx} : Set (Subgroup G)) = wConj D.M (⊥ : Subgroup G) V hV L := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro Y (rfl | rfl)
      · exact hWmem
      · exact hWxmem
    · rw [hcard, Set.ncard_pair hWxne]
  obtain ⟨g, hgM, hgd⟩ := (mem_barSub (⊥ : Subgroup G) V hV D.M d).1 hd
  have hgW : conjSubgroup W (g : G) = W ∨ conjSubgroup W (g : G) = Wx := by
    have hmem : conjSubgroup W (g : G) ∈ wConj D.M (⊥ : Subgroup G) V hV L := by
      refine ⟨(g : G), hgM, ?_⟩
      rw [hWdef]
    rw [← hpair] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hxgM : x * (g : G) ∈ D.M := D.M.mul_mem hxM hgM
  have hxgW : conjSubgroup W (x * (g : G)) = W ∨
      conjSubgroup W (x * (g : G)) = Wx := by
    have hmem : conjSubgroup W (x * (g : G)) ∈ wConj D.M (⊥ : Subgroup G) V hV L := by
      refine ⟨x * (g : G), hxgM, ?_⟩
      rw [hWdef]
    rw [← hpair] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hAB : conjSubgroup W (g : G) ≠ conjSubgroup W (x * (g : G)) := by
    intro heq
    apply hWxne
    have h2 := congrArg (fun Z : Subgroup G => conjSubgroup Z (g : G)⁻¹) heq
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup] at h2
    have h3 : W = conjSubgroup W x := by
      simpa [conjSubgroup_one, mul_assoc] using h2
    rw [hWxdef]
    exact h3
  have hconjU : conjSubgroup U (g : G) = U := by
    have h1 : conjSubgroup U (g : G) =
        conjSubgroup W (g : G) ⊓ conjSubgroup W (x * (g : G)) := by
      rw [hUdef, E3.conjSubgroup_inf, hWxdef, conjSubgroup_conjSubgroup]
    rcases hgW with hgW1 | hgW1 <;> rcases hxgW with hxgW1 | hxgW1
    · exact absurd (by rw [hgW1, hxgW1]) hAB
    · rw [h1, hgW1, hxgW1, hUdef]
    · rw [h1, hgW1, hxgW1, hUdef, inf_comm]
    · exact absurd (by rw [hgW1, hxgW1]) hAB
  intro z hz
  obtain ⟨y, hy, hyq⟩ := (mem_imgTil (⊥ : Subgroup G) V hV U z).1 hz
  rw [← hgd]
  refine (mem_imgTil (⊥ : Subgroup G) V hV U (actTil (⊥ : Subgroup G) V hV g z)).2
    ⟨actStab (⊥ : Subgroup G) V hV g y, ?_, ?_⟩
  · rw [actStab_apply_val]
    have hy' : y.val ∈ conjSubgroup U (g : G) := by
      rw [hconjU]
      exact hy
    exact (mem_conjSubgroup_iff).1 hy'
  · rw [← hyq, actTil_mk]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
