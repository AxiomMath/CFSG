
module

public import Certificates.Kernel.Co1Cover.Checks
import CFSG.Certificates.Kernel.Co1FixCount
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelCo1Cover

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1.CoverNative
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.InvNative

theorem rowsA_eq : CFSG.Sporadic.Co1.Module.dat.rowsA = unpackR 24 R0 := by
  change rowsOfPayload 24 CFSG.Sporadic.Co1.Native.seedA = _
  rw [SeedA.eq]
  exact bind_sound seedA_bind

theorem rowsB_eq : CFSG.Sporadic.Co1.Module.dat.rowsB = unpackR 24 R1 := by
  change rowsOfPayload 24 CFSG.Sporadic.Co1.Native.seedB = _
  rw [SeedB.eq]
  exact bind_sound seedB_bind

theorem regs_eq : regsRowsCov = (R.map (unpackR 24)).toArray := by
  have hi : initRowsCov = ((R.take 2).map (unpackR 24)).toArray := by
    rw [initRowsCov, rowsA_eq, rowsB_eq]
    rfl
  rw [regsRowsCov, hi]
  exact prog_sound prog_ok

theorem rr4 : rrCov 4 = unpackR 24 R4 := by
  rw [rrCov, regs_eq]
  rfl

theorem rr5 : rrCov 5 = unpackR 24 R5 := by
  rw [rrCov, regs_eq]
  rfl

theorem epsRows_eq : epsRows = (E.map (unpackR 24)).toArray := by
  simp [epsRows, rrCov, regs_eq, List.range_succ, R, E]

theorem Aa_eq : Aa = unpackR 11 AaP := by
  have h := packB_sound packA_ok
  rwa [Array.toArray_toList] at h

theorem Ba_eq : Ba = unpackR 11 BaP := by
  have h := packB_sound packB_ok
  rwa [Array.toArray_toList] at h

theorem qRows_eq : CFSG.Sporadic.Co1.Module.qRows = unpackR 24 QP := by
  have h := packB_sound packQ_ok
  rwa [Array.toArray_toList] at h

theorem t0Rows_eq : t0Rows = unpackR 24 T0P := by
  have hx : x0mask = 722 := rfl
  rw [t0Rows, epsRows_eq, hx, eprod_sound lenE eprod_ok, rr4, mul_sound t0_ok]

theorem facts10061 :
    (CFSG.Sporadic.Co1.InvNative.validRows (rrCov 4) = true ∧
        CFSG.Sporadic.Co1.InvNative.validRows (rrCov 5) = true)
    ∧ (epsBasicOK epsRows = true)
    ∧ (epsInjOK epsRows = true)
    ∧ (normOK epsRows (rrCov 4) (transposeRows 11 Aa) = true)
    ∧ (normOK epsRows (rrCov 5) (transposeRows 11 Ba) = true)
    ∧ (orderIs t0Rows 2 = true)
    ∧ (CFSG.Sporadic.Co1.Module.countsOK t0Rows 4096 0 = true) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rr4]
    exact validRows_unpackR _
  · rw [rr5]
    exact validRows_unpackR _
  · rw [epsRows_eq]
    exact epsBasic_sound basic_ok
  · rw [epsRows_eq]
    exact epsInj_sound inj_ok
  · rw [epsRows_eq, rr4, Aa_eq, tr_sound trA_ok]
    exact norm_sound lenE normA_ok
  · rw [epsRows_eq, rr5, Ba_eq, tr_sound trB_ok]
    exact norm_sound lenE normB_ok
  · rw [t0Rows_eq]
    exact orderIs_sound t0_order
  · obtain ⟨h1, h2⟩ := CFSG.KC.Co1Fix.fixK_sound fix_ok
    rw [CFSG.Sporadic.Co1.Module.countsOK, t0Rows_eq, tr_sound trT0_ok, qRows_eq, tr_sound trQ_ok,
      h1, h2]
    rfl

private theorem presentation_eq :
    TauCeti.SporadicName.M24.presentation = TauCeti.Sporadic.m24Presentation := rfl

theorem fget_zero (X : Nat) : fget X 0 24 = X / 2 ^ (24 * 0) % 2 ^ 24 := by
  have h := Nat.and_two_pow_sub_one_eq_mod X 24
  simp only [fget, maskN, pw2, Nat.mul_zero, pow_zero, Nat.div_one]
  exact h

theorem facts10063 :
    (relCheckAB 24 (rrCov 4) (rrCov 5) (invRows (rrCov 4)) (invRows (rrCov 5))
      TauCeti.SporadicName.M24.presentation.relatorLetters = true)
    ∧ (relCheckAB 11 Aa Ba Aa (mulRows 11 Ba Ba)
      TauCeti.SporadicName.M24.presentation.relatorLetters = true)
    ∧ (CFSG.Sporadic.SmallF2.rowsMatrix 24 (mulRows 24 (rrCov 4) (rrCov 5)) ≠
      CFSG.Sporadic.SmallF2.rowsMatrix 24 (mulRows 24 (rrCov 5) (rrCov 4))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [presentation_eq, CFSG.KBAlt.M24.rels_eq, rr4, rr5, inv_sound inv4_ok, inv_sound inv5_ok]
    exact relCheck_sound rel24_ok
  · rw [presentation_eq, CFSG.KBAlt.M24.rels_eq, Aa_eq, Ba_eq, mul_sound bb_ok]
    exact relCheck_sound rel11_ok
  · rw [rr4, rr5, mul_sound (Nat.beq_refl (mulF 24 R4 R5)), mul_sound (Nat.beq_refl (mulF 24 R5 R4))]
    intro h
    have hrow : ∀ j : Fin 24, CFSG.Sporadic.SmallF2.toVecD 24 ((unpackR 24 (mulF 24 R4 R5))[0]?.getD 0) j =
        CFSG.Sporadic.SmallF2.toVecD 24 ((unpackR 24 (mulF 24 R5 R4))[0]?.getD 0) j := fun j => by
      have := congrFun (congrFun h ⟨0, by norm_num⟩) j
      simpa only [CFSG.Sporadic.SmallF2.rowsMatrix_apply] using this
    have hlt : ∀ X : Nat, (unpackR 24 X)[0]?.getD 0 < 2 ^ 24 := fun X => by
      simp only [unpackR, Array.getElem?_ofFn]
      simpa using Nat.mod_lt _ (by norm_num)
    have heq := CFSG.Sporadic.SmallF2.toVecD_injective (hlt _) (hlt _) (funext hrow)
    have hn := noncomm_ok
    have hd : ndiff = 0 := rfl
    rw [hd, fget_zero, fget_zero] at hn
    simp only [unpackR, Array.getElem?_ofFn] at heq
    simp only [Nat.ofNat_pos, ↓reduceDIte, Option.getD_some] at heq
    rw [heq] at hn
    simp [notB, Nat.beq_refl] at hn

end CertificateChecks.KernelCo1Cover

end
