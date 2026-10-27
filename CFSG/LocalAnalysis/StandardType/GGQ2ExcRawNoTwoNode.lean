module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawE7Sound
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafExcVacuous

public section

namespace CFSG.StandardType.GGQ2Frame

open Module CFSG.Assembly CFSG.Decide.F3
open ExcRaw

private theorem le_cent_of_occurs {m : Fin 6} {U : Submodule (ZMod 3) (V m)}
    {c : Finset (Root m)} (hocc : occurs m U c) : U ≤ cent m c := by
  intro u hu
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i hi
  exact hocc.2.1 i hi u hu

private theorem cent_eq_of_occurs {m : Fin 6} {U : Submodule (ZMod 3) (V m)}
    {c : Finset (Root m)} (hocc : occurs m U c) (h : cent m c ≤ U) : cent m c = U :=
  le_antisymm h (le_cent_of_occurs hocc)

private theorem root_eq_zero_iff_of_vecOfList {m : Fin 6} {l : List ℕ} {v : V m}
    (h : vecOfList (dim m) l = v ∨ vecOfList (dim m) l = 2 • v) (i : Root m) :
    root m i (vecOfList (dim m) l) = 0 ↔ root m i v = 0 := by
  rcases h with h | h
  · rw [h]
  · rw [h, map_nsmul]
    constructor
    · intro h0
      rw [nsmul_eq_mul] at h0
      exact (mul_eq_zero.mp h0).resolve_left (by decide)
    · intro h0
      rw [h0, smul_zero]

private theorem eq_filter_of_occurs_span {m : Fin 6} {v : V m} {k : Finset (Root m)}
    (hocc : occurs m (Submodule.span (ZMod 3) {v}) k)
    (hcent : cent m k = Submodule.span (ZMod 3) {v}) {l : List ℕ}
    (hl : vecOfList (dim m) l = v ∨ vecOfList (dim m) l = 2 • v) :
    k = Finset.univ.filter fun i => root m i (vecOfList (dim m) l) = 0 := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_iff_vanish_of_occurs hocc hcent, vanish_span_singleton_iff,
    root_eq_zero_iff_of_vecOfList hl i]

private theorem eq_filter_of_occurs_cent_eq_plane {v w : V 4}
    {U : Submodule (ZMod 3) (V 4)} {j : Finset (Root 4)}
    (hocc : occurs 4 U j) (hcent : cent 4 j = U)
    (hspan : Submodule.span (ZMod 3) ({v, w} : Set (V 4)) = U) :
    j = Finset.univ.filter fun i => root 4 i v = 0 ∧ root 4 i w = 0 := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_iff_vanish_of_occurs hocc hcent, ← hspan, vanish_span_pair]

namespace ExcRaw

theorem exists_mem_e6Lines4_of_not_noInternalAt {v : V 4} (hv : v ≠ 0)
    (h : ¬ NoInternalAt 4 v) :
    ∃ l ∈ Check.e6Lines4, vecOfList (dim 4) l = v ∨ vecOfList (dim 4) l = 2 • v := by
  obtain ⟨l, hl, hvl⟩ := exists_mem_repVecs (d := dim 4) (v := v) hv
  refine ⟨l, ?_, hvl⟩
  by_contra hmem
  have hls : l ∈ Check.ls4 := by
    rw [Check.ls4, List.mem_filter]
    exact ⟨hl, by simp [hmem]⟩
  have hni : NoInternalAt 4 (vecOfList (dim 4) l) :=
    Check.noInternalAt_of_run (Check.natAbs_pairing_le Check.boundOK_mode4) Check.run_mode4 l hls
  rcases hvl with hvl | hvl
  · rw [hvl] at hni
    exact h hni
  · rw [hvl, ← Nat.cast_smul_eq_nsmul (R := ZMod 3) 2 v] at hni
    exact h ((noInternalAt_smul_iff (v := v) (a := (↑(2 : ℕ) : ZMod 3)) (by decide)).mp hni)

end ExcRaw

private theorem exists_plane_pair {v : V 4} (hv : v ≠ 0)
    {U : Submodule (ZMod 3) (V 4)} (hU : finrank (ZMod 3) U = 2) (hvU : v ∈ U) :
    ∃ w, w ≠ 0 ∧ Submodule.span (ZMod 3) ({v, w} : Set (V 4)) = U := by
  have hspan1 : finrank (ZMod 3) (Submodule.span (ZMod 3) {v}) = 1 :=
    finrank_span_singleton hv
  have hnotle : ¬ U ≤ Submodule.span (ZMod 3) {v} := by
    intro hle
    have hfin := Submodule.finrank_mono (R := ZMod 3) hle
    omega
  have hnotsub : ¬ (U : Set (V 4)) ⊆ (Submodule.span (ZMod 3) {v} : Set (V 4)) := hnotle
  obtain ⟨w, hwU, hwspan⟩ := Set.not_subset.mp hnotsub
  refine ⟨w, ?_, ?_⟩
  · intro hw0
    exact hwspan (hw0 ▸ Submodule.zero_mem (Submodule.span (ZMod 3) {v}))
  · have hli : LinearIndependent (ZMod 3) ![v, w] := by
      refine (LinearIndependent.pair_iff' hv).mpr ?_
      intro a ha
      exact hwspan (by rw [← ha]; exact Submodule.smul_mem _ a (Submodule.subset_span (by simp)))
    have hspan_le : Submodule.span (ZMod 3) ({v, w} : Set (V 4)) ≤ U := by
      rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact hvU
      · exact hwU
    have hspan_fin : finrank (ZMod 3) (Submodule.span (ZMod 3) ({v, w} : Set (V 4))) = 2 := by
      have hrange : (Set.range ![v, w] : Set (V 4)) = {v, w} := by
        ext x
        simp [or_comm]
      rw [← hrange, finrank_span_eq_card hli]
      simp
    exact Submodule.eq_of_le_of_finrank_eq hspan_le (hspan_fin.trans hU.symm)

private theorem card_eq_twelve_or_twenty_one {v : V 4} {l : List ℕ} (hl : l ∈ Check.e6Lines4)
    (hvl : vecOfList (dim 4) l = v ∨ vecOfList (dim 4) l = 2 • v) {k j : Finset (Root 4)}
    (hocc_k : occurs 4 (Submodule.span (ZMod 3) {v}) k)
    (hcent_k : cent 4 k = Submodule.span (ZMod 3) {v})
    {labK labJ : LargeEvenLabel}
    (hlabK : GGLabelIso (label 4 k) labK)
    (hlabJ : GGLabelIso (label 4 j) labJ)
    (htwo : TwoNodeLabels 3 labK labJ) :
    j.card = 12 ∨ j.card = 21 := by
  have hkcard : k.card = 36 := by
    rw [eq_filter_of_occurs_span hocc_k hcent_k hvl, Check.card_vanish_e6Lines4 hl]
  have hlabK' : GGLabelIso (labelSL 36 (orthCount 4 k)) labK := by
    have hlab : label 4 k = labelSL k.card (orthCount 4 k) := rfl
    simpa [hlab, hkcard] using hlabK
  have hlabJ' : GGLabelIso (labelSL j.card (orthCount 4 j)) labJ := by
    have hlab : label 4 j = labelSL j.card (orthCount 4 j) := rfl
    simpa [hlab] using hlabJ
  exact card_eq_of_twoNodeLabels_labelSL (o := orthCount 4 k) (o' := orthCount 4 j)
    hlabK' hlabJ' htwo

private theorem false_of_card_twelve_or_twenty_one {j : Finset (Root 4)} {l lw : List ℕ}
    (hl : l ∈ Check.e6Lines4) (hlw : lw ∈ repVecs (dim 4))
    (hj : ∀ i : Root 4, i ∈ j ↔
      root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0)
    (hjcard : j.card = 12 ∨ j.card = 21)
    {U : Submodule (ZMod 3) (V 4)} (hcent : cent 4 j = U)
    (hU : finrank (ZMod 3) U = 2) : False := by
  let S : Finset (Root 4) := Finset.univ.filter fun i =>
    root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0
  have hjS : j = S := by
    ext i
    rw [hj i]
    simp [S]
  have hcardS : S.card = j.card := by rw [← hjS]
  have hpair := Check.card_vanish_e6Lines4_pair hl hlw
  have hcard21 : j.card ≠ 21 := by
    intro h21
    exact hpair.1 (by rw [hcardS, h21])
  have hcard12 : j.card = 12 := hjcard.resolve_right hcard21
  obtain ⟨t, ht1, ht2⟩ := hpair.2 (by rw [hcardS, hcard12])
  have hthree : 3 ≤ finrank (ZMod 3) (cent 4 j) := by
    refine three_le_finrank_cent_of_orth t ?_ ht2
    intro i hi a
    exact ht1 i ((hj i).mp hi).1 ((hj i).mp hi).2 a
  rw [hcent] at hthree
  have hfin : finrank (ZMod 3) U = 2 := hU
  omega

private theorem rawNoInternalTwoNode_of_noInternalAt {m : Fin 6}
    (h : ∀ v : V m, v ≠ 0 → NoInternalAt m v) : RawNoInternalTwoNode (excRaw m) := by
  change ∀ v : V m, v ≠ 0 →
    ∀ U : Submodule (ZMod 3) (V m), finrank (ZMod 3) U = 2 → v ∈ U →
      ∀ k j : Finset (Root m), admissible m k → admissible m j →
        occurs m (Submodule.span (ZMod 3) {v}) k → occurs m U j →
          cent m k = Submodule.span (ZMod 3) {v} → cent m j ≤ U → v ∈ inside m k →
            ∀ labK ∈ equivLabels m k, ∀ labJ ∈ equivLabels m j,
              ¬ TwoNodeLabels 3 labK labJ
  intro v hv _ _ _ k _ _ _ hocc_k _ hcent_k _ hin
  exact (h v hv k hocc_k hcent_k hin).elim

theorem rawNoInternalTwoNode_excRaw_four : RawNoInternalTwoNode (excRaw 4) := by
  change ∀ v : V 4, v ≠ 0 →
    ∀ U : Submodule (ZMod 3) (V 4), finrank (ZMod 3) U = 2 → v ∈ U →
      ∀ k j : Finset (Root 4), admissible 4 k → admissible 4 j →
        occurs 4 (Submodule.span (ZMod 3) {v}) k → occurs 4 U j →
          cent 4 k = Submodule.span (ZMod 3) {v} → cent 4 j ≤ U → v ∈ inside 4 k →
            ∀ labK ∈ equivLabels 4 k, ∀ labJ ∈ equivLabels 4 j,
              ¬ TwoNodeLabels 3 labK labJ
  intro v hv U hU hvU k j _ _ hocc_k hocc_j hcent_k hcent_j hin labK hlabK labJ hlabJ htwo
  obtain ⟨l, hl, hvl⟩ :=
    ExcRaw.exists_mem_e6Lines4_of_not_noInternalAt hv fun h => h k hocc_k hcent_k hin
  have hjcard : j.card = 12 ∨ j.card = 21 :=
    card_eq_twelve_or_twenty_one hl hvl hocc_k hcent_k hlabK hlabJ htwo
  obtain ⟨w, hw0, hspan_eq⟩ := exists_plane_pair hv hU hvU
  have hcentj : cent 4 j = U := cent_eq_of_occurs hocc_j hcent_j
  have hjfilter : j = Finset.univ.filter fun i => root 4 i v = 0 ∧ root 4 i w = 0 :=
    eq_filter_of_occurs_cent_eq_plane hocc_j hcentj hspan_eq
  obtain ⟨lw, hlw, hwv⟩ := exists_mem_repVecs (d := dim 4) (v := w) hw0
  have hj : ∀ i : Root 4, i ∈ j ↔
      root 4 i (vecOfList (dim 4) l) = 0 ∧ root 4 i (vecOfList (dim 4) lw) = 0 := by
    intro i
    rw [hjfilter]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← root_eq_zero_iff_of_vecOfList hvl i, ← root_eq_zero_iff_of_vecOfList hwv i]
  exact false_of_card_twelve_or_twenty_one hl hlw hj hjcard hcentj hU

theorem rawNoInternalTwoNode_excRaw (m : Fin 6) : RawNoInternalTwoNode (excRaw m) := by
  by_cases hm : m = 4
  · subst hm
    exact rawNoInternalTwoNode_excRaw_four
  · exact rawNoInternalTwoNode_of_noInternalAt fun v hv => ExcRaw.noInternalAt_excRaw m hm hv

end CFSG.StandardType.GGQ2Frame
