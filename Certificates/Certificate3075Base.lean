
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs

@[expose] public section

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Sp8

namespace CertificateChecks.Batch3075

theorem kGram : ∀ k : Fin 45, ∀ i j : Fin 8,
    ∑ a : Fin 8, bvec 8 (genRow k i) a * (popc 8 (gramRows.getD a 0 &&& genRow k j) : ZMod 2) =
      bvec 8 (gramRows.getD i 0) j := by
  decide +kernel

theorem sum_eq (x y : ℕ) (g : Fin 8 → ℕ) :
    ∑ a : Fin 8, ∑ b : Fin 8, bvec 8 x a * bvec 8 (g a) b * bvec 8 y b =
      ∑ a : Fin 8, bvec 8 x a * (popc 8 (g a &&& y) : ZMod 2) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← bvec_dotProduct, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => mul_assoc _ _ _

end CertificateChecks.Batch3075

namespace Certificates

end Certificates
