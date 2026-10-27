
module

public import CFSG.Quasithin.Background.HMathieuSyl23
import Certificates.Kernel.HMathieu.T23CGlue
import Certificates.Kernel.HMathieu.T23XGlue
import Certificates.Kernel.HMathieu.C7072
import CFSG.Certificates.Kernel.HMathieu.FixTabSound
import CFSG.Certificates.Kernel.HMathieu.GreedyPSound
import CFSG.Certificates.Kernel.HMathieu.PredSound

public section

open CFSG.Quasithin.H.Mathieu
open CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1 CertificateChecks.KernelHMathieu

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu in
theorem certificate7072 :
    ∀ k ∈ [1, 2, 3, 4, 5],
      forallGreedyP pos23s2 inv23s2 (pred23 k) k [] = true := by
  have hFs : ∀ y < inv23s2.length,
      T23C.F23c.getD y [] = fixMasks 11 actM [T23C.Mc.getD y []] := by
    intro y hy
    rw [T23.len] at hy
    rw [fixTab_get T23C.tab y (by simp [T23C.lenMc]; omega)]
    simp [fixMasks, List.getD_eq_getElem?_getD, List.getElem?_take, hy]
  have hA := forallGreedyAll_fixT T23X.gtabs (by rw [T23.len]; exact T23X.rowsLen) pos23s2_eq
    T23C.Mc T23C.F23c 11 hFs _ (pred23K 4) (fun _ _ _ => rfl) 5
    (by rw [T23.len]; exact C7072.search)
  have hB := forallGreedyAll_mono_of (I := fun l => (∀ y ∈ l, y ∈ inv23s2) ∧ IndepList l)
    (q := fun l => l.isEmpty || pred23 l.length l)
    (fun l x hl hx => indep_step T23X.gtabs l x hl hx) (fun l hl hp => ?_) 5 []
    ⟨by simp, IndepList.nil⟩ hA
  · intro k hk
    have hb : 1 ≤ k ∧ k ≤ 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact forallGreedyP_of_all hB k hb.1 hb.2
  obtain ⟨hR, _⟩ := hl
  have hfix : fixMasks 11 act23s2 l =
      fixMasks 11 actM (l.map fun x => T23C.Mc.getD (inv23s2.idxOf x) []) :=
    fixMasks_map 11 _ fun x hx => T23C.act_mem (hR x hx)
  unfold pred23K fixSt at hp
  unfold pred23
  rw [hfix]
  simp only [List.length_map, List.isEmpty_map] at hp ⊢
  convert hp using 12

end Certificates
