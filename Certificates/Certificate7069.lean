
module

import Certificates.Kernel.HMathieu.T22Glue
import Certificates.Kernel.HMathieu.C7069
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.PickESound
public import CFSG.Quasithin.Background.HMathieuSyl22Base

public section

open CFSG.Quasithin.H.Mathieu
open CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu in
theorem certificate7069 :
    ∀ k ∈ [1, 2, 3, 4, 5, 6],
      forallGreedyP pos22s2 inv22s2 (pred22 k) k [] = true := by
  have hMc : T22.Mc.length = 72 := by rw [T22.mcOK, List.length_map, T22.lenP]
  have hFs : ∀ y < inv22s2.length,
      FixTab22.F22.getD y [] = fixMasks 10 actM [T22.Mc.getD y []] := by
    intro y hy
    rw [T22.len] at hy
    rw [fixTab_get FixTab22.tab y (by simp [hMc]; omega)]
    simp [fixMasks, List.getD_eq_getElem?_getD, List.getElem?_take, hy]
  have hA := forallGreedyAll_fixT T22.gtabs (by rw [T22.len]; exact T22.lenOK.2) pos22s2_eq
    T22.Mc FixTab22.F22 10 hFs _
    (fun L S st => pred22E 9 T22.Mc FixTab22.F22 71 L S st && predOffK T22.P L S st)
    (fun _ _ _ => rfl) 6 (by rw [T22.len]; exact C7069.search)
  have hB := forallGreedyAll_mono_of (I := fun l => (∀ y ∈ l, y ∈ inv22s2) ∧ IndepList l)
    (q := fun l => l.isEmpty || pred22 l.length l)
    (fun l x hl hx => indep_step T22.gtabs l x hl hx) (fun l hl hp => ?_) 6 []
    ⟨by simp, IndepList.nil⟩ hA
  · intro k hk
    have hb : 1 ≤ k ∧ k ≤ 6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact forallGreedyP_of_all hB k hb.1 hb.2
  obtain ⟨hR, hind⟩ := hl
  have hci := isCommInvol_of_indepList hind
  have hfix : fixMasks 10 act22s2 l =
      fixMasks 10 actM (l.map fun x => T22.Mc.getD (inv22s2.idxOf x) []) :=
    fixMasks_map 10 _ fun x hx => T22.act_mem (hR x hx)
  have hF : ∀ s ∈ inv22s2, FixTab22.F22.getD (inv22s2.idxOf s) [] = fixMasks 10 act22s2 [s] := by
    intro s hs
    rw [hFs _ (List.idxOf_lt_length_iff.2 hs)]
    have e := fixMasks_map 10 (act := act22s2) (act' := actM)
      (fun x => T22.Mc.getD (inv22s2.idxOf x) []) (l := [s]) fun x hx => by
        rw [List.mem_singleton.1 hx]
        exact T22.act_mem hs
    simp only [List.map_cons, List.map_nil] at e
    exact e.symm
  have hxi := xiCands_eq T22.gtabs hci hF
  have hpair := pairCands_eq T22.gtabs hci hF fun t ht => T22.act_mem ht
  rw [T22.len] at hxi hpair
  rw [Bool.and_eq_true] at hp
  replace hp := hp.1
  unfold pred22E fixSt at hp
  unfold pred22
  rw [← hxi, ← hpair, ← hfix] at hp
  simp only [List.length_map, List.isEmpty_map] at hp ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hp ⊢
  rcases hp with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
  · exact Or.inl h
  · refine Or.inr ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · convert h1 using 12
    · convert h2 using 12
    · convert h3 using 12
    · convert h4.imp_right xiCheck_of_testE using 12
    · convert h5.imp_right (And.imp xiCheck_of_testE pairCheck_of_testE) using 12

end Certificates
