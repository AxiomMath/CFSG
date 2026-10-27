
module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import Certificates.Data.BT2K1Vocab

@[expose] public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

namespace CertificateChecks.Batch3077

theorem rows_symm : ∀ i j : Fin 8,
    bvec 8 (gramRows.getD i 0) j = bvec 8 (gramRows.getD j 0) i := by decide +kernel

theorem rows_diag : ∀ i : Fin 8, bvec 8 (gramRows.getD i 0) i = 0 := by decide +kernel

theorem rows_diag_corrupt :
    ¬ ∀ i : Fin 8, bvec 8 ([129, 192, 56, 52, 44, 28, 130, 67].getD i 0) i = 0 := by decide +kernel

theorem gram0_symm (i j : Fin 8) : gram0 i j = gram0 j i := rows_symm i j

theorem gram0_diag (i : Fin 8) : gram0 i i = 0 := rows_diag i

theorem sum_alt {n : ℕ} (G : Fin n → Fin n → ZMod 2) (hs : ∀ i j, G i j = G j i)
    (hd : ∀ i, G i i = 0) (v : Fin n → ZMod 2) : ∑ i, ∑ j, v i * G i j * v j = 0 := by
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun i j => v i * G i j * v j)]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) (fun p _ => ?_) (fun p _ hp => ?_)
    (fun p _ => Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩) (fun p _ => rfl)
  · have e : v p.2 * G p.2 p.1 * v p.1 = v p.1 * G p.1 p.2 * v p.2 := by
      rw [hs p.2 p.1]
      ring
    rw [e]
    exact CharTwo.add_self_eq_zero _
  · intro e
    have hij : p.1 = p.2 := congrArg Prod.snd e
    apply hp
    rw [hij, hd, mul_zero, zero_mul]

end CertificateChecks.Batch3077

namespace Certificates

end Certificates
