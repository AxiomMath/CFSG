module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
public import Certificates.Kernel.BabyMonster.Fi23Fu
public import Certificates.Kernel.Sporadic.Fi23Fu.Rels
import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Sporadic.Co2Schreier.ThirdChain

public section

namespace CertificateChecks.Kernel17451

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.Sporadic.Bridge
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster


theorem phiB_uJ : phiB KernelSpor.Fi23Fu.uJ = KernelBM.Fi23Fu.uB := by
  rw [KernelSpor.Fi23Fu.uJ, KernelSpor.Fi23Fu.wJ_eq, KernelBM.Fi23Fu.uB]
  simp only [map_pow, map_mul, phiB_img (by norm_num : 1 < 10), phiB_img (by norm_num : 2 < 10),
    phiB_img (by norm_num : 3 < 10), phiB_img (by norm_num : 4 < 10),
    phiB_img (by norm_num : 7 < 10), phiB_img (by norm_num : 8 < 10)]

theorem rank_t3_one : Matrix.rank ((phiB (t3 1)).val.val - 1) = 2916 := by
  rw [← CFSG.Monster.Existence.rank_sub_one_of_isConj
    (phiB.map_isConj KernelSpor.Fi23Fu.isConj_uJ), phiB_uJ]
  exact KernelBM.Fi23Fu.rank_uB

theorem order_t3_one : orderOf (phiB (t3 1)) = 3 := by
  have hu1 : KernelSpor.Fi23Fu.uJ ≠ 1 := by
    intro h
    have e : KernelBM.Fi23Fu.uB = 1 := by rw [← phiB_uJ, h, map_one]
    have h0 := KernelBM.Fi23Fu.rank_uB
    rw [e, map_one, sub_self, Matrix.rank_zero] at h0
    exact absurd h0 (by norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_injective phiB phiB_injective, KernelSpor.Fi23Fu.t3_one_eq, ← MulAut.conj_apply,
    MulEquiv.orderOf_eq]
  exact orderOf_eq_prime KernelSpor.Fi23Fu.uJ_cube hu1

end CertificateChecks.Kernel17451

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate17451 :     Matrix.rank ((phiB (t3 1)).val.val - 1) = 2916 ∧ orderOf (phiB (t3 1)) = 3 :=
  ⟨Kernel17451.rank_t3_one, Kernel17451.order_t3_one⟩

end Certificates
