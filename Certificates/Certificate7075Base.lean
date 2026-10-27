
module

public import Certificates.Kernel.HMathieu.T24Glue
import CFSG.Certificates.Kernel.HMathieu.PredSound
public import Certificates.Data.Kernel.HMathieu.Pred24

@[expose] public section

open CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu CFSG.QuasithinUnique.Setup.X1
open CertificateChecks.KernelHMathieu

namespace CertificateChecks.Batch7075

theorem xiCands_eq {l : List T24s2.Elem} (hl : IsCommInvol l) :
    xiCands 11 act24s2 l = xiCandsK T24.Mc 191 ((subprods l).map inv24s2.idxOf) := by
  have hS : ∀ s ∈ subprods l, s ∈ inv24s2 ∨ s = 1 :=
    fun s hs => mem_or_one_of_subprods T24.gtabs hl hs
  unfold xiCands xiCandsK
  rw [List.filter_map, List.flatMap_map]
  have hf : ((subprods l).filter ((fun s => s != 191) ∘ inv24s2.idxOf)) =
      (subprods l).filter fun s => decide (s ≠ 1) := by
    refine List.filter_congr fun s hs => ?_
    simp only [Function.comp_apply]
    rw [← T24.len, Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_iff, ne_eq,
      idxOf_eq_length_iff T24.gtabs (hS s hs)]
  rw [hf]
  refine List.flatMap_congr fun s hs => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hs
  have hsR : s ∈ inv24s2 := (hS s hs.1).resolve_right hs.2
  exact fixMasks_map 11 (fun x => T24.Mc.getD (inv24s2.idxOf x) [])
    (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact T24.act_mem hsR)

end CertificateChecks.Batch7075

