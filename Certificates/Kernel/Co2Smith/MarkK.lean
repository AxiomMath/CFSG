module

public import Certificates.Data.Kernel.Co2Smith.Mark
public import Certificates.Kernel.Co2Smith.LettersData
public import CFSG.Sporadic.Co2Smith.GlC0MarkInputs
import CFSG.Certificates.Kernel.Common.AllChunks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KC.Co2InvS

@[expose] noncomputable def reflK : List Nat := (List.range 36).map fun i => wK LP (glMkRWord i)

theorem c0_k0 : ((glWit0.drop (0 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k1 : ((glWit0.drop (1 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k2 : ((glWit0.drop (2 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k3 : ((glWit0.drop (3 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k4 : ((glWit0.drop (4 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k5 : ((glWit0.drop (5 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k6 : ((glWit0.drop (6 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k7 : ((glWit0.drop (7 * 5)).take 5).all
    (fun e => glWit1.all fun e₁ => glWit2.all fun e₂ =>
    c0PredK (wK LP [12]) (wK LP [0]) reflK
      (mulV (mulV (mulV (wK LP e.2.2) (FM e.2.1)) (wK LP e₁.2)) (wK LP e₂.2))) = true := by
  decide +kernel

theorem c0_k : c0K LP FM (wK LP [12]) (wK LP [0]) reflK glWit0 glWit1 glWit2 = true := by
  unfold c0K
  refine CFSG.KC.AllChunks.all_of_chunks _ _ 5 8 (by decide) ?_
  intro k hk
  match k, hk with
  | 0, _ => exact c0_k0
  | 1, _ => exact c0_k1
  | 2, _ => exact c0_k2
  | 3, _ => exact c0_k3
  | 4, _ => exact c0_k4
  | 5, _ => exact c0_k5
  | 6, _ => exact c0_k6
  | 7, _ => exact c0_k7
  | k + 8, h => exact absurd h (by omega)

end CertificateChecks.KernelCo2Smith
