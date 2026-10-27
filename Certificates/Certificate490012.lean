module

public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs22
import Certificates.Kernel.HMathieu.T22Glue
import Certificates.Kernel.HMathieu.C7069
import CFSG.Certificates.Kernel.HMathieu.FixTabSound
import CFSG.Certificates.Kernel.HMathieu.GreedyPSound
import CFSG.Certificates.Kernel.HMathieu.PredSound
import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH
open CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH in
theorem certificate490012 :
    ∀ k ∈ [1, 2, 3, 4, 5, 6],
      forallGreedyP pos22s2 inv22s2 (predOff22 k) k [] = true := by
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
    (q := fun l => l.isEmpty || predOff22 l.length l)
    (fun l x hl hx => indep_step T22.gtabs l x hl hx) (fun l hl hp => ?_) 6 []
    ⟨by simp, IndepList.nil⟩ hA
  · intro k hk
    have hb : 1 ≤ k ∧ k ≤ 6 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact forallGreedyP_of_all hB k hb.1 hb.2
  obtain ⟨hR, _⟩ := hl
  have hfix : fixMasks 10 act22s2 l =
      fixMasks 10 actM (l.map fun x => T22.Mc.getD (inv22s2.idxOf x) []) :=
    fixMasks_map 10 _ fun x hx => T22.act_mem (hR x hx)
  have hoff : l.all fixesOff22 = (l.map inv22s2.idxOf).all fun a =>
      offPts22.all fun i => CFSG.KC.Enum.pg 5 (CFSG.KS.mask 5) (T22.P.getD a 0) i == i := by
    rw [List.all_map]
    refine all_congr_mem fun x hx => all_congr_mem fun i hi => ?_
    have hlt : ∀ i ∈ offPts22, i < 24 := by decide
    simp only [Function.comp_apply]
    rw [T22.arr_get x (hlt i hi), show inv22s2 = T22s2.invols from rfl,
      pk_idxOf T22.packed T22.invData (Or.inl (hR x hx))]
  rw [Bool.and_eq_true] at hp
  replace hp := hp.2
  unfold predOffK fixSt at hp
  unfold predOff22
  rw [hfix, hoff]
  simp only [List.length_map, List.isEmpty_map] at hp ⊢
  exact hp

end Certificates
