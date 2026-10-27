module

public import CFSG.ClassicalInvolution.Phan.Phan3ACheck
import Certificates.Kernel.PhanA3.Tables
import Certificates.Kernel.PhanA3.Act
public import Certificates.Kernel.PhanA3.ActData
import CFSG.Certificates.Kernel.Misc.Coset.TableFact

public section

namespace CertificateChecks.Batch270005

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.ClassicalInvolution.Phan.Q3G
  CFSG.Certificates.CosetEnumeration

theorem codesA : codes phanA3Rels = CFSG.KAct.PhanA3.R := by decide +kernel

theorem codesKW : phanA3KernelWords.map (fun p => p.1.map letterCode) = CFSG.KAct.PhanA3.KW := by
  decide +kernel

theorem cycAll_spec {A : ℕ → ℕ} {L ℓ : ℕ} :
    ∀ {us : List (List ℕ)}, CFSG.KAct.PhanA3.cycAll A L us ℓ = true →
      ∀ u ∈ us, Act.cycleOK A L u ℓ = true
  | [], _, u, hu => absurd hu List.not_mem_nil
  | v :: vs, h, u, hu => by
    change Act.andB (Act.cycleOK A L v ℓ) (CFSG.KAct.PhanA3.cycAll A L vs ℓ) = true at h
    rw [Act.andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h.1
    · exact cycAll_spec h.2 u hu

theorem card_le : Finite PhanA3Group ∧ Nat.card PhanA3Group ≤ 19440 * 6048 :=
  TableFact.card_restrict phanA3Rels (by norm_num) (subsetOf 6 [0, 1, 2, 3]) (by decide)
    CFSG.KBFact.P3A CFSG.KBFact.P3S

theorem three_dvd {w : List (Fin 6 × Bool)} (hw : (w, 3) ∈ phanA3KernelWords) :
    3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk w) : PhanA3Group) := by
  have hpt : ∀ x < 19440, Act.pointOK CFSG.KAct.PhanA3.A 6 19440 CFSG.KAct.PhanA3.R x = true :=
    fun x hx => Act.allR_spec CFSG.KAct.PhanA3.all x (Nat.zero_le _) (by omega)
  have hm : w.map letterCode ∈ CFSG.KAct.PhanA3.KW := by
    rw [← codesKW]
    exact List.mem_map.2 ⟨_, hw, rfl⟩
  have hc := cycAll_spec CFSG.KAct.PhanA3.cycles _ hm
  exact Act.cycleOK_sound (N := 19440) phanA3Rels codesA (by norm_num) hpt w hc

end CertificateChecks.Batch270005

namespace Certificates

open CertificateChecks

theorem certificate270005 :
    (Finite CFSG.ClassicalInvolution.Phan.Q3G.PhanA3Group ∧
        Nat.card CFSG.ClassicalInvolution.Phan.Q3G.PhanA3Group ≤ 19440 * 6048) ∧
      ∀ w : List (Fin 6 × Bool), (w, 3) ∈ CFSG.ClassicalInvolution.Phan.Q3G.phanA3KernelWords →
        3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk w) :
          CFSG.ClassicalInvolution.Phan.Q3G.PhanA3Group) :=
  ⟨CertificateChecks.Batch270005.card_le, fun _ hw => CertificateChecks.Batch270005.three_dvd hw⟩

end Certificates
