module

public import Certificates.Kernel.AE6F5.Checks
public import CFSG.Certificates.Kernel.AE6F5Sound

public section

namespace Certificates

open CFSG.KC.AE6F5K CFSG.KD.AE6F5

theorem gens517508 : ∀ l < 9, ∀ x : Fin 12, ap (el GN l) x.val = (genF l x).val := by
  decide +kernel

theorem pis517508 : ∀ t < 24, piOK GN CT HT FP FS t (D.getD t 0) = true := by
  intro t ht
  interval_cases t
  exacts [ch517508_p0, ch517508_p1, ch517508_p2, ch517508_p3, ch517508_p4, ch517508_p5,
    ch517508_p6, ch517508_p7, ch517508_p8, ch517508_p9, ch517508_p10, ch517508_p11, ch517508_p12,
    ch517508_p13, ch517508_p14, ch517508_p15, ch517508_p16, ch517508_p17, ch517508_p18,
    ch517508_p19, ch517508_p20, ch517508_p21, ch517508_p22, ch517508_p23]

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S in
theorem certificate517508 : ∀ σ : Equiv.Perm (Fin 12),
    (∀ m n : Fin 12, ae6Blk m = ae6Blk n ↔ ae6Blk (σ m) = ae6Blk (σ n)) →
    σ ∉ Subgroup.closure (Set.range ae6LetterHatPerm ∪ Set.range ae6GammaHatPerm) →
    ∃ τ ∈ Subgroup.closure (insert σ (Set.range ae6LetterHatPerm)), orderOf τ = 3 ∧
      (∀ n, ae6Blk (τ n) = ae6Blk n) ∧
      (Finset.univ.filter fun b : Fin 4 => ∃ n, ae6Blk n = b ∧ τ n ≠ n).card = 1 :=
  f5_of (D := fun t => D.getD t 0) ch517508_treeC0 ch517508_treeH0
    (FP := FP) (FS := FS)
    (fun l hl => pr_of_ap (gens517508 l hl)) (by decide +kernel) (by decide +kernel) pis517508

end Certificates
