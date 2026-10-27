module

public import Certificates.Kernel.Co1Syl5.Glue
public import Certificates.Kernel.Co1Syl5.Checks14962
public import CFSG.Certificates.Kernel.SporSch.Co1CenSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Syl5

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.RankThree.PartOne.SPOR
open CFSG.Sporadic.Co1.TwoBNative

theorem sg_eq : #[unpack 24 24 (S.M 40), unpack 24 24 (S.M 38)] = gensArr 2 GA := by
  apply Array.ext (by simp [gensArr])
  intro l h₁ h₂
  have hl : l = 0 ∨ l = 1 := by
    simp only [List.size_toArray, List.length_cons, List.length_nil] at h₁
    omega
  rcases hl with rfl | rfl <;> rfl

theorem gt_eq : gtBFS (gensArr 2 GA) 700 = bfsTree T.N T.P T.PAR T.LAB ∧
    gtOK (gensArr 2 GA) (bfsTree T.N T.P T.PAR T.LAB) = true :=
  gtBFS_of_K kQ

theorem hT : T.N = 625 := Nat.eq_of_beq_eq_true kT

theorem check14962 : co1SylowOK co1SylowDerivs 41 39 42 = true := by
  have hv : ∀ M, CFSG.Sporadic.Co1.InvNative.validRows (unpack 24 24 M) = true := fun M => by
    rw [← unpackR_eq_unpack]
    exact CFSG.KC.Co1F2.validRows_unpackR M
  have hx : (pow (unpack 24 24 (S.M 41)) 5 == one) = true := by
    rw [pow_u, one_u, ← unpackR_eq_unpack, ← unpackR_eq_unpack, CFSG.KC.Co1B.beq_unpack]
    exact kX
  unfold co1SylowOK co1SylowCheck
  rw [dag_eq]
  simp only [Nat.reduceSub]
  rw [rows_getD (j := 40) (by rw [hN]; decide), rows_getD (j := 38) (by rw [hN]; decide),
    rows_getD (j := 41) (by rw [hN]; decide), sg_eq, gt_eq.1, gt_eq.2, cenK_sound _ _ kZ, hx,
    hv, hv, hv]
  simp [bfsTree, hT, hN]

end CertificateChecks.KernelCo1Syl5

end
