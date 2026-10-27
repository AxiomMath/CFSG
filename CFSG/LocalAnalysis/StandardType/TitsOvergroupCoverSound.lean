module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupSound

public section

namespace CFSG.StandardType.TitsOvergroup

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbedding.MaxD2 (dcoset conjStab)
open Certificates.MaxD2Perm (fpTab fpOK memFp)

theorem fp3_eq {n : ℕ} {pts : List ℕ} (hpts : ∀ x ∈ pts, x < n) {a b c : Tab}
    {α β γ : Equiv.Perm (Fin n)} (ha : TabRep a α) (hb : TabRep b β) (hc : TabRep c γ) :
    fp3 pts a b c = fpTab pts (comp n (comp n a b) c) := by
  unfold fp3 fpTab
  apply congrArg List.toArray
  apply List.map_congr_left
  intro x hx
  have hx' : x < n := hpts x hx
  have hcx : getElem! c x < n := by
    rw [hc.2 ⟨x, hx'⟩]
    exact (γ ⟨x, hx'⟩).isLt
  rw [TabRep.comp_getElem! (comp n a b) c ⟨x, hx'⟩,
    TabRep.comp_getElem! a b ⟨getElem! c x, hcx⟩]

theorem memFp3_iff {n : ℕ} {pts : List ℕ} (hpts : ∀ x ∈ pts, x < n) {T : Array Tab}
    (hfp : fpOK pts T = true) {a b c : Tab} {α β γ : Equiv.Perm (Fin n)} (ha : TabRep a α)
    (hb : TabRep b β) (hc : TabRep c γ) :
    memFp3 n pts (indexOf (T.map (fpTab pts))) (T.map (fpTab pts)) T a b c = true ↔
      comp n (comp n a b) c ∈ T.toList := by
  unfold memFp3
  rw [fp3_eq hpts ha hb hc]
  exact CFSG.AGLEmbedding.MaxD2.memFp_iff hfp (comp n (comp n a b) c)

variable {D : PairData} {S : List (Equiv.Perm (Fin D.n))}

theorem conjCount3_eq (hS : Sound D S) (hN : checkN D = true)
    (hpts : ∀ x ∈ D.fpPts, x < D.n) (hfp : fpOK D.fpPts (nEnum D).tabs = true) {i : ℕ}
    (hi : i < (repT D).size) (hinvs : invsOK D.n (repT D) (repI D) = true) :
    conjCount3 D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repI D)[i]! (repT D)[i]! =
      Nat.card (conjStab (pairN D S) ((pairReps D S).getD i 1)) := by
  have hN' := enum_pairN hS hN
  have hx : TabRep (repT D)[i]! ((pairReps D S).getD i 1) := by
    have := repT_rep (D := D) (S := S) hS i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hi]] at this
  have hxi : TabRep (repI D)[i]! ((pairReps D S).getD i 1)⁻¹ := by
    have := repI_rep (D := D) (S := S) hS hinvs i
    have hi' : i < (repI D).size := by simpa [repI] using hi
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hi']] at this
  set g := (pairReps D S).getD i 1 with hg
  unfold conjCount3
  rw [CFSG.AGLEmbedding.MaxD2.countBelow_getElem! (nEnum D).tabs (fun t => memFp3 D.n D.fpPts
    (indexOf ((nEnum D).tabs.map (fpTab D.fpPts))) ((nEnum D).tabs.map (fpTab D.fpPts))
    (nEnum D).tabs (repI D)[i]! t (repT D)[i]!)]
  have hfilter := hN'.filter (K := (pairN D S).comap (MulAut.conj g⁻¹).toMonoidHom)
    (fun t => memFp3 D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repI D)[i]! t (repT D)[i]!) (by
    intro t a ht
    rw [memFp3_iff hpts hfp (ha := hxi) (hb := ht) (hc := hx)]
    rw [CFSG.AGLEmbedding.MaxD2.mem_enum_iff hN' ((hxi.comp ht).comp hx)]
    simp [Subgroup.mem_comap])
  rw [← Enumerates.card hfilter, conjStab, inf_comm]

theorem sum_eq3 (hS : Sound D S) (hN : checkN D = true) (hpts : ∀ x ∈ D.fpPts, x < D.n)
    (hfp : fpOK D.fpPts (nEnum D).tabs = true) (hinvs : invsOK D.n (repT D) (repI D) = true)
    (hsum : dcSum3 D.n D.nOrder D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = D.gOrder) :
    ∑ i ∈ Finset.range (D.repW.length + 1), Nat.card (pairN D S) * Nat.card (pairN D S) /
      Nat.card (conjStab (pairN D S) ((pairReps D S).getD i 1)) = D.gOrder := by
  rw [← hsum, dcSum3, CFSG.AGLEmbedding.MaxD2.foldl_range_add]
  have hsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  rw [hsz, card_pairN hS hN]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [conjCount3_eq hS hN hpts hfp (by omega) hinvs]

theorem exists_dcoset_pair (hS : Sound D S) (hN : checkN D = true) (hCover : checkCover D = true) :
    ∀ y ∈ pairG D S, ∃ i ≤ D.repW.length,
      y ∈ dcoset (pairN D S) ((pairReps D S).getD i 1) := by
  have hN' := enum_pairN hS hN
  simp only [checkCover, Bool.and_eq_true, beq_iff_eq] at hCover
  obtain ⟨⟨⟨⟨hfpPts, hfp⟩, hinvs⟩, hsum⟩, hdisj⟩ := hCover
  have hpts : ∀ x ∈ D.fpPts, x < D.n := by
    intro x hx
    simpa using (List.all_eq_true.1 hfpPts) x hx
  simp only [dcDisjoint3, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdisj
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hrepT := repT_rep (D := D) (S := S) hS
  have hrepI := repI_rep (D := D) (S := S) hS hinvs
  have hxT : ∀ i, i < D.repW.length + 1 → TabRep (repT D)[i]! ((pairReps D S).getD i 1) := by
    intro i hi
    have := hrepT i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxI : ∀ i, i < D.repW.length + 1 → TabRep (repI D)[i]! ((pairReps D S).getD i 1)⁻¹ := by
    intro i hi
    have := hrepI i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  refine CFSG.AGLEmbedding.MaxD2.exists_dcoset_of_sum (pairN_le_pairG (D := D) (S := S))
    (fun i => (pairReps D S).getD i 1) D.repW.length ?_ ?_ ?_
  · intro i hi
    exact pairReps_mem (CFSG.AGLEmbedding.MaxD2.getD_mem_of_lt (i := i) (L := pairReps D S)
      (by simp [pairReps]; omega) 1)
  · rw [sum_eq3 hS hN hpts hfp hinvs hsum, hS.card]
  · intro i hi j hj hij a ha hmem
    obtain ⟨k, hk, hka⟩ := hN'.exists_pos ha
    rcases hdisj i (by omega) j (by omega) with h | h
    · exact h hij
    · have hy := ((hxI i (by omega)).comp hka).comp (hxT j (by omega))
      have hmemT := (CFSG.AGLEmbedding.MaxD2.mem_enum_iff hN' hy).2 hmem
      have h3 := (memFp3_iff hpts hfp (ha := hxI i (by omega)) (hb := hka)
        (hc := hxT j (by omega))).2 hmemT
      rw [h k hk] at h3
      exact Bool.noConfusion h3

end CFSG.StandardType.TitsOvergroup

