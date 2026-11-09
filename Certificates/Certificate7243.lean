module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C7243OrbGlue
public import CFSG.Quasithin.Background.HFCode24Orb
import CFSG.Certificates.Kernel.HMathieu.MatSearch
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu CertificateChecks.KernelHMathieu.C7243Orb

namespace Certificates

theorem predHF24_eq_K (l : List T24s2.Elem) (hl : ∀ y ∈ l, y ∈ inv24s2) (hind : IndepList l) :
    predHF24 l = predHF24K T24.E T24.P (l.map inv24s2.idxOf) ((subprods l).map inv24s2.idxOf)
      (fixSt 11 (l.map fun x => T24.Md.getD (inv24s2.idxOf x) [])) := by
  have hci := isCommInvol_of_indepList hind
  have hn := normalChainB_eq T24.packed T24.invData T24.idOK hci hl
  have hmap : fixMasks 11 codeAct24 l =
      fixMasks 11 actM (l.map fun x => T24.Md.getD (inv24s2.idxOf x) []) := by
    unfold fixMasks
    refine List.filter_congr fun m _ => ?_
    simp only [List.all_map, Function.comp_def]
    exact all_congr_mem fun s hs => by rw [T24.codeAct_mem (hl s hs)]
  unfold predHF24 predHF24K fixSt
  rw [T24.codeFixMasks_eq hci.1, hmap, List.length_map]
  have hR : inv24s2 = T24s2.invols := rfl
  rw [hn]
  simp only [hR]

theorem map_idxOf_memsE {i : Nat} (hi : i < 752) :
    (memsE i).map inv24s2.idxOf = mems (repRank i) i := by
  unfold memsE
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (mems (repRank i) i)]
  exact List.map_congr_left fun y hy => idxOf_el' ((struct_sound i hi).1 y hy).le

theorem memsE_mem {i : Nat} (hi : i < 752) : ∀ y ∈ memsE i, y ∈ inv24s2 := by
  intro y hy
  obtain ⟨yp, hyp, rfl⟩ := List.mem_map.1 hy
  exact el_mem_inv24 ((struct_sound i hi).1 yp hyp)

theorem predHF24_memsE {i : Nat} (hi : i < 752) : predHF24 (memsE i) = true := by
  obtain ⟨hpos, hind, _, _⟩ := struct_sound i hi
  have h := predOK_all i hi
  simp only [predOK, Bool.and_eq_true] at h
  have hM : ((memsE i).map fun x => T24.Md.getD (inv24s2.idxOf x) []) =
      (mems (repRank i) i).map (T24.Md.getD · []) := by
    rw [← map_idxOf_memsE hi, List.map_map]
    rfl
  have hS : (subprods (memsE i)).map inv24s2.idxOf = spanL (mems (repRank i) i) :=
    map_subprods_eq_spanL _ hpos hind
  have hlen : (fixSt 11 ((mems (repRank i) i).map (T24.Md.getD · []))).2.length =
      2 ^ expOf (fixL (repRank i) i).length := by
    unfold fixSt
    rw [← fixL_eq_fixMasks]
    exact (Nat.eq_of_beq_eq_true h.1).symm
  rw [predHF24_eq_K _ (memsE_mem hi) hind, map_idxOf_memsE hi, hM, hS,
    predHF24K_eq_predD _ _ _ _ _ hlen]
  exact h.2

@[expose] noncomputable def reps7243 (j : Nat) : List (List T24s2.Elem) :=
  ((List.range 752).filter fun i => repRank i == j).map memsE

theorem mem_reps7243 {j : Nat} {r : List T24s2.Elem} :
    r ∈ reps7243 j ↔ ∃ i < 752, repRank i = j ∧ memsE i = r := by
  simp [reps7243,List.mem_filter, List.mem_range, and_assoc]

open CFSG.Quasithin.H.Mathieu in
theorem certificate7243 :
    forallGreedyAll pos24s2 inv24s2 predHF24 6 [] = true := by
  have hR : ∀ x ∈ inv24s2, x * x = 1 ∧ x ≠ 1 := fun x hx =>
    ⟨(T24.gtabs.invol x hx).2, (T24.gtabs.invol x hx).1⟩
  have hr0 : repRank 0 = 0 := by
    have hs := structOK_all (i := 0) (by omega)
    simp only [structOK, Nat.beq_refl, Bool.cond_true, Bool.and_eq_true] at hs
    exact Nat.eq_of_beq_eq_true hs.1
  refine forallGreedyAll_of_reps_mem pos24s2_eq hR (fun g x hx => ?_) predHF24_span predHF24_conj
    reps7243 (mem_reps7243.2 ⟨0, by omega, hr0, by unfold memsE; rw [hr0]; rfl⟩) ?_ ?_ ?_
  · obtain ⟨h1, h2⟩ := hR x hx
    refine T24.gtabs.all _ (fun e => h2 ?_) ?_
    · exact (MulAut.conj g).injective (e.trans (map_one _).symm)
    · rw [← map_mul, h1, map_one]
  · intro j r hr
    obtain ⟨i, _, rfl, rfl⟩ := mem_reps7243.1 hr
    unfold memsE
    rw [List.length_map, length_mems]
  · intro j hj r hr x hx hxr
    obtain ⟨i, hi, rfl, rfl⟩ := mem_reps7243.1 hr
    obtain ⟨g, t, ht, hrt, hm⟩ := ext_of_rep hi (by omega) hx hxr
    exact ⟨g, memsE t, mem_reps7243.2 ⟨t, ht, hrt, rfl⟩, (struct_sound t ht).2.1, hm⟩
  · intro j _ r hr
    obtain ⟨i, hi, rfl, rfl⟩ := mem_reps7243.1 hr
    exact predHF24_memsE hi

end Certificates
