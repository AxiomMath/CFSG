module

public import CFSG.Quasithin.H13.A5M12SylBase
import Certificates.Kernel.HMathieu.T12Glue
import Certificates.Kernel.HMathieu.C7113
import CFSG.Certificates.Kernel.HMathieu.FixTabSound
import CFSG.Certificates.Kernel.HMathieu.GreedyPSound
import CFSG.Certificates.Kernel.HMathieu.PredSound
public import CFSG.Certificates.Kernel.HMathieu.GreedySound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
open CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 in
theorem certificate7113 :
    ∀ k ∈ [1, 2, 3, 4, 5],
      forallGreedyP pos12s2 inv12s2 (pred12 k) k [] = true := by
  have hMc : T12.Mc.length = 36 := by rw [T12.mcOK, List.length_map, T12.lenP]
  have hFs : ∀ y < inv12s2.length,
      FixTab12.F12.getD y [] = fixMasks 10 actM [T12.Mc.getD y []] := by
    intro y hy
    rw [T12.len] at hy
    rw [fixTab_get FixTab12.tab y (by simp [hMc]; omega)]
    simp [fixMasks, List.getD_eq_getElem?_getD, List.getElem?_take, hy]
  have hmem : ∀ x ∈ inv12s2, act12s2 x = actM (T12.Mc.getD (inv12s2.idxOf x) []) := by
    intro x hx
    rw [← T12.act_el (by rw [← T12.len]; exact idxOf_le x), el_idxOf (Or.inl hx)]
  have hA := forallGreedyAll_fixT T12.gtabs (by rw [T12.len]; exact T12.lenOK.2) pos12s2_eq
    T12.Mc FixTab12.F12 10 hFs _ (predXiK 10 8 3 FixTab12.F12 35) (fun _ _ _ => rfl) 5
    (by rw [T12.len]; exact C7113.search)
  have hB := forallGreedyAll_mono_of (I := fun l => (∀ y ∈ l, y ∈ inv12s2) ∧ IndepList l)
    (q := fun l => l.isEmpty || pred12 l.length l)
    (fun l x hl hx => indep_step T12.gtabs l x hl hx) (fun l hl hp => ?_) 5 []
    ⟨by simp, IndepList.nil⟩ hA
  · intro k hk
    have hb : 1 ≤ k ∧ k ≤ 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact forallGreedyP_of_all hB k hb.1 hb.2
  obtain ⟨hR, hind⟩ := hl
  have hci := isCommInvol_of_indepList hind
  have hfix : fixMasks 10 act12s2 l =
      fixMasks 10 actM (l.map fun x => T12.Mc.getD (inv12s2.idxOf x) []) :=
    fixMasks_map 10 _ fun x hx => hmem x (hR x hx)
  have hF : ∀ s ∈ inv12s2, FixTab12.F12.getD (inv12s2.idxOf s) [] = fixMasks 10 act12s2 [s] := by
    intro s hs
    rw [hFs _ (List.idxOf_lt_length_iff.2 hs)]
    have e := fixMasks_map 10 (act := act12s2) (act' := actM)
      (fun x => T12.Mc.getD (inv12s2.idxOf x) []) (l := [s]) fun x hx => by
        rw [List.mem_singleton.1 hx]
        exact hmem s hs
    simp only [List.map_cons, List.map_nil] at e
    exact e.symm
  have hxi := xiCands_eq T12.gtabs hci hF
  rw [T12.len] at hxi
  unfold predXiK fixSt at hp
  unfold pred12 xiCheck
  rw [hfix, hxi]
  simp only [List.length_map, List.isEmpty_map] at hp ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hp ⊢
  rcases hp with h | ⟨h12, h3 | ⟨h4, h5⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨h12, Or.inl h3⟩
  · have h6 := indepCheck_of_indepK h5
    refine Or.inr ⟨h12, Or.inr ⟨?_, h6⟩⟩
    simp only [decide_eq_true_eq] at h4 ⊢
    norm_num at h4 ⊢
    exact h4

end Certificates
