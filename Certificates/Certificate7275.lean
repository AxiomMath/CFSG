module

public import Certificates.Kernel.HMathieu.T24Glue
public import Certificates.Kernel.HMathieu.C7275
import CFSG.Certificates.Kernel.HMathieu.PredSound

public section

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

namespace CertificateChecks.Batch7275

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

theorem noQuad3 (act : T24s2.Elem → Nat → Nat)
    (M : List (List Nat)) (hM : ∀ k ≤ 191, act (el inv24s2 k) = actM (M.getD k []))
    (hK : gAllR 191 (fun st y => M.getD y [] :: st) (fun _ _ st => noQuadRank3 11 actM st) 6 []
      [191] (2 ^ 191 - 1) [] T24.rows 0 = true) :
    forallGreedyAll pos24s2 inv24s2 (noQuadRank3 11 act) 6 [] = true := by
  have hel : ∀ x ∈ inv24s2, act x = actM (M.getD (inv24s2.idxOf x) []) := by
    intro x hx
    have hk : inv24s2.idxOf x ≤ 191 := by
      rw [← T24.len]
      exact idxOf_le x
    rw [← hM _ hk, el_idxOf (Or.inl hx)]
  rw [forallGreedyAll_eq_gAllS_nil T24.gtabs pos24s2_eq (noQuadRank3 11 act)
    (fun st y => M.getD y [] :: st) (fun _ _ st => noQuadRank3 11 actM st)
    (fun l => l.map fun x => M.getD (inv24s2.idxOf x) []) (fun _ _ _ _ _ => rfl)
    (fun l hl _ => noQuadRank3_map 11 _ fun x hx => hel x (hl x hx)) 6, T24.len, List.map_nil,
    ← gAllR_eq T24.lenOK.2 _ _ 6 [] [191] _ [] (by simp [startK])]
  exact hK

end CertificateChecks.Batch7275

namespace Certificates

open CertificateChecks

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat in
theorem certificate7275 :
    (
      forallGreedyAll pos24s2 inv24s2 (noQuadRank3 11 act24s2) 6 [] = true) ∧
    (
      forallGreedyAll pos24s2 inv24s2 (noQuadRank3 11 actC24s2) 6 [] = true) :=
  ⟨CertificateChecks.Batch7275.noQuad3 act24s2 T24.Mc (fun _ hk => T24.act_el hk) C7275.coc,
    CertificateChecks.Batch7275.noQuad3 actC24s2 T24.Md (fun _ hk => T24.actC_el hk) C7275.code⟩

end Certificates
