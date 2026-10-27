module

public import Certificates.Kernel.AE6Q8.Facts
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModelBase

public section

namespace CertificateChecks.Batch517504

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CIdx
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native Certificates.AE6Model
open CertificateChecks.KernelAE6Q8
open CFSG.KS.Raw.Orb (Gen)
open CFSG.EvenSmallLie.OmegaEight (omegaT gen gen_mem_omegaT)

theorem curtisPerms_getD {l : ℕ} (hl : l < 8) :
    (curtisPerms ()).getD l 1 = CFSG.EvenSmallLie.OmegaEight.gen l := by
  have hr := rep_permOfArr (Orb.isInvA_unpack ((Orb.allN_iff.1 GS_perm) l hl))
  have h1 := Orb.prep_of_rep hr.1
  rw [GS_eq l hl] at h1
  have h2 := CertificateChecks.KernelAE6F.prep_curtis hl
  have e : CFSG.EvenSmallLie.OmegaEight.gen l = permOfArr 360 (unpack 360 9 (CertificateChecks.KernelO8.AP.S l)) := by
    rw [CFSG.EvenSmallLie.OmegaEight.gen, CertificateChecks.KernelO8.genAP.2 l (by omega)]
  rw [e]
  exact Equiv.ext fun x => Fin.ext ((h2 x).symm.trans (h1 x))

theorem GC_le : GC ≤ omegaT := by
  rw [Subgroup.closure_le]
  rintro _ ⟨l, rfl⟩
  change (curtisPerms ()).getD l.val 1 ∈ omegaT
  rw [curtisPerms_getD l.isLt]
  exact gen_mem_omegaT l.isLt

theorem fact : ∀ r ∈ Subgroup.closure {g | g ∈ sGens ()}, orderOf r = 2 →
    ∀ i ∈ omegaT, ∀ j ∈ omegaT, i * i = r → j * j = r → i * j * i = j →
    (∀ h ∈ omegaT, h * r = r * h →
      h⁻¹ * i * h ∈ Subgroup.closure {g | g ∈ sGens ()} ∧
        h⁻¹ * j * h ∈ Subgroup.closure {g | g ∈ sGens ()}) →
    (∃ c ∈ Subgroup.closure {g | g ∈ sGens ()}, r = c * z0 () * c⁻¹) ∨
      5 ≤ Set.ncard {J' | ∃ c ∈ omegaT, c * r = r * c ∧
        (Subgroup.closure {i, j}).map (MulAut.conj c).toMonoidHom = J'} := by
  intro r hr ho i _ j _ hii hjj hiji hcut
  rw [← gen_eq_S] at hr hcut ⊢
  rcases q8_fact hr ho hii hjj hiji fun h hh hc => hcut h (GC_le hh) hc with h | h
  · exact Or.inl h
  · refine Or.inr (h.trans (Set.ncard_le_ncard ?_ ?_))
    · rintro _ ⟨c, hc, hcr, rfl⟩
      exact ⟨c, GC_le hc, hcr, rfl⟩
    · refine (Set.finite_univ.image fun c : Equiv.Perm (Fin 360) =>
        (Subgroup.closure {i, j}).map (MulAut.conj c).toMonoidHom).subset ?_
      rintro _ ⟨c, -, -, rfl⟩
      exact ⟨c, Set.mem_univ _, rfl⟩

end CertificateChecks.Batch517504

namespace Certificates

open CertificateChecks

open Certificates.AE6Model CFSG.EvenSmallLie.OmegaEight in
theorem certificate517504 : ∀ r ∈ Subgroup.closure {g | g ∈ sGens ()}, orderOf r = 2 →
    ∀ i ∈ omegaT, ∀ j ∈ omegaT, i * i = r → j * j = r → i * j * i = j →
    (∀ h ∈ omegaT, h * r = r * h →
      h⁻¹ * i * h ∈ Subgroup.closure {g | g ∈ sGens ()} ∧
        h⁻¹ * j * h ∈ Subgroup.closure {g | g ∈ sGens ()}) →
    (∃ c ∈ Subgroup.closure {g | g ∈ sGens ()}, r = c * z0 () * c⁻¹) ∨
      5 ≤ Set.ncard {J' | ∃ c ∈ omegaT, c * r = r * c ∧
        (Subgroup.closure {i, j}).map (MulAut.conj c).toMonoidHom = J'} :=
  CertificateChecks.Batch517504.fact

end Certificates
