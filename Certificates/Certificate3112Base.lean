
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionHomBase
import CFSG.Certificates.Kernel.Common.BvecLoop

@[expose] public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

namespace CertificateChecks.Batch3112

theorem count_zeros : Nat.count (fun x => qPoly (bvec 8 x) + 1 = 0) (2 ^ 8) = 136 := by
  decide +kernel

theorem count_zeros_ne : ¬ Nat.count (fun x => qPoly (bvec 8 x) + 1 = 0) (2 ^ 8) = 135 := by
  decide +kernel

theorem card_shift (P : V8 → Prop) [DecidablePred P] (v : V8) :
    (Finset.univ.filter fun w => P (w + v)).card = (Finset.univ.filter P).card :=
  Finset.card_bij (fun w _ => w + v) (fun w hw => by simpa using hw)
    (fun _ _ _ _ h => add_right_cancel h) (fun u hu => ⟨u - v, by simpa using hu, by simp⟩)

theorem card_zeros_one (v : V8) :
    (Finset.univ.filter fun w : V8 => qPoly (w + v) + 1 = 0).card = 136 := by
  rw [card_shift (fun u => qPoly u + 1 = 0), CFSG.KC.BvecLoop.card_filter_bvec, count_zeros]

end CertificateChecks.Batch3112

namespace Certificates

end Certificates
