module

public import Certificates.Kernel.Co2Fuse.Counts
public import CFSG.Certificates.Kernel.Co2Fuse.Sylow

public section

namespace CertificateChecks.KernelSpor.Co2Fuse

open CFSG.KC.Co2Cls CFSG.KC.Co2Fuse CFSG.RankThree.Co2 Subgroup

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem card_Cm : Nat.card Cm = 2 ^ 18 * 2835 := by
  rw [CertificateChecks.KernelSpor.Co2TInv.Cm_eq,
    CertificateChecks.KernelSpor.Co2Cls.natCard_genMonN]
  norm_num

theorem card_unitsIn_Cm : Nat.card (unitsIn Cm) = 2 ^ 18 * 2835 := by
  rw [card_unitsIn isUnit_Cm, card_Cm]

theorem T_card_le : Nat.card (matGrp sylWords) ≤ 2 ^ 18 :=
  card_le_of_exp (fun x hx => isUnit_Cm x (CertificateChecks.KernelSpor.Co2TInv.T_le_Cm hx))
    CertificateChecks.KernelSpor.Co2J.tFacts.pow
    (fun _ hv => CertificateChecks.KernelSpor.Co2TInv.T_le_Cm hv) card_unitsIn_Cm (by norm_num)

theorem cmCensus : CmCensus := by
  intro x hx hsq h1
  obtain ⟨g, hg, y, hy, e⟩ := conj_into isUnit_Cm CertificateChecks.KernelSpor.Co2TInv.T_le_Cm
    CertificateChecks.KernelSpor.Co2J.tFacts.pow card_Cm (by norm_num)
    CertificateChecks.KernelSpor.Co2J.tFacts.card hx hsq
  obtain ⟨v, hv, hvg, -⟩ := exists_unitsIn isUnit_Cm hg
  have hy' : y = (v : M22) * x * ((v⁻¹ : M22ˣ) : M22) := by
    rw [hvg, e, mul_assoc, ← hvg, Units.mul_inv, mul_one]
  have hy2 : y * y = 1 := by
    rw [hy']
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc x x, hsq, one_mul, Units.mul_inv]
  have hy1 : y ≠ 1 := by
    intro h
    exact h1 ((isUnit_Cm g hg).mul_left_cancel (by rw [e, h, one_mul, mul_one]))
  obtain ⟨i, hi, k, hk, ek⟩ :=
    CertificateChecks.KernelSpor.Co2TInv.tInvFacts T_card_le y hy hy2 hy1
  refine ⟨i, hi, ((v⁻¹ : M22ˣ) : M22) * k, Cm.mul_mem ((unitsIn Cm).inv_mem hv) hk, ?_⟩
  rw [mul_assoc, ek, hy']
  simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem card_P3_le : Nat.card (matGrp pWords3) ≤ 2 ^ 16 := by
  obtain ⟨u, -, hux, -⟩ := exists_unitsIn isUnit_Cm (rep_mem_Cm (i := 2) (by norm_num))
  have hP3u : ∀ x ∈ matGrp pWords3, IsUnit x := fun x hx => isUnit_Cm x (P3_le_Cm hx)
  refine card_le_of_exp hP3u CertificateChecks.KernelSpor.Co2Syl.facts3.1.pow
    (H := unitsIn Cm ⊓ centralizer {u}) (fun v hv => ⟨P3_le_Cm hv,
      mem_centralizer_singleton_iff.2 (Units.ext ?_)⟩) ?_ (by norm_num : ¬ 2 ∣ 9)
  · rw [Units.val_mul, Units.val_mul, hux]
    exact CertificateChecks.KernelSpor.Co2Syl.facts3.1.comm 2 (by simp) _ hv
  · rw [card_cent_unitsIn isUnit_Cm, hux,
      ← (CertificateChecks.KernelSpor.Co2Cls.Final.class2).2,
      CertificateChecks.KernelSpor.Co2Syl.repMat_eq (by norm_num),
      CertificateChecks.KernelSpor.Co2TInv.Cm_eq]

theorem fuse_counts_final :
    fuseN {0, 2, 7} {4, 6, 8} {9} = 32 ∧ fuseN {0, 2, 7} {9} {4, 6, 8} = 0 ∧
      fuseN {0, 2, 7} {4, 6, 8} {1, 3, 5, 9} = 68 ∧ fuseN {0, 2, 7} {1, 3, 5, 9} {4, 6, 8} = 36 :=
  fuse_counts cmCensus card_P3_le

end CertificateChecks.KernelSpor.Co2Fuse

end
