module

public import Certificates.Data.TriD4Phi
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Link
public import Certificates.Kernel.D4.LinkFacts
public import Certificates.Kernel.D4.PhiChecks
public import CFSG.Certificates.Kernel.D4PhiSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4Phi CFSG.Monster.B.Co2 CFSG.StandardType.TriD4TwoRow
open CFSG.Monster.B.Fischer CFSG.RankThree.Native CFSG.AGLEmbedding.ChevOuter

theorem phiFacts : permB 2457 12 (PH 0) = true ∧
    (∀ i < 2457, unpack 8 3 (LV (pg 12 (mask 12) (PH 0) i)) = frobCode (unpack 8 3 (LV i))) ∧
    (∀ i < 2457, pg 12 (mask 12) (PH 0) (pg 12 (mask 12) (PH 0) (pg 12 (mask 12) (PH 0) i)) = i) ∧
    ∀ k < 18, ∀ i < 2457, pg 12 (mask 12) (PH 0) (pg 12 (mask 12) (LP k) i) =
      pg 12 (mask 12) (LP (sg k)) (pg 12 (mask 12) (PH 0) i) :=
  phiK_sound phiOK

theorem keys_inj : ∀ i < lineCert.pts.size, ∀ j < lineCert.pts.size,
    keyV lineCert.pts[i]! = keyV lineCert.pts[j]! → i = j :=
  fun _ hi _ hj e => arrCertOK_keys_inj pin.1 hi hj e

theorem ph_lt {i : ℕ} (hi : i < 2457) : pg 12 (mask 12) (PH 0) i < 2457 :=
  (pp_of_permB szOK' phiFacts.1).2.1 i hi

theorem phiArr_eq : phiArr () = unpack 2457 12 (PH 0) := by
  have hs : (phiArr ()).size = 2457 := by simp [phiArr, pin.2.1]
  apply Array.ext
  · rw [hs]
    simp [unpack]
  · intro i h1 _
    have hi : i < 2457 := by rwa [hs] at h1
    rw [← getElem!_pos, ← getElem!_pos, Orb.unpack_get hi]
    refine phiArr_get keys_inj (by rw [pin.2.1]; exact hi) (by rw [pin.2.1]; exact ph_lt hi) ?_
    rw [pin.2.2.1 _ (ph_lt hi), pin.2.2.1 _ hi, phiFacts.2.1 i hi]

theorem rep_phi : Rep 2457 (unpack 2457 12 (PH 0)) d4Phi := by
  unfold d4Phi
  rw [phiArr_eq]
  exact rep_of_validA (validA_of phiFacts.1)

theorem phi_val (x : Fin 2457) : (d4Phi x : ℕ) = pg 12 (mask 12) (PH 0) x :=
  (rep_phi x).symm.trans (Orb.unpack_get x.2)

theorem phi_facts : (∀ i : Fin 2457, lineCert.pts[(d4Phi i : ℕ)]! = frobCode lineCert.pts[(i : ℕ)]!) ∧
    Rep 2457 (phiArr ()) d4Phi ∧ d4Phi ^ 3 = 1 ∧
    ∀ k < 18,
      d4Phi * d4Rho (letterX k) = d4Rho (letterX (sg k)) * d4Phi := by
  refine ⟨fun i => ?_, phiArr_eq ▸ rep_phi, ?_, ?_⟩
  · rw [phi_val, pin.2.2.1 _ (ph_lt i.2), pin.2.2.1 _ i.2, phiFacts.2.1 i i.2]
  · refine Equiv.ext fun x => Fin.ext ?_
    rw [pow_succ, pow_two, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      phi_val, phi_val, phi_val]
    exact phiFacts.2.2.1 x x.2
  · intro k hk
    have hL : ∀ l < 18, ∀ x : Fin 2457, (d4Rho (letterX l) x : ℕ) = pg 12 (mask 12) (LP l) x :=
      fun l hl x => ((piArr_eq hl ▸ rep_d4Rho_letter hl) x).symm.trans (Orb.unpack_get x.2)
    refine Equiv.ext fun x => Fin.ext ?_
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, phi_val, hL k hk, hL (sg k) (sg_lt k hk),
      phi_val]
    exact phiFacts.2.2.2 k hk x x.2

end CertificateChecks.KernelD4

end
