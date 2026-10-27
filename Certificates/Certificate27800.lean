module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Table
import CFSG.Certificates.Kernel.TS8JKSound
import Certificates.Kernel.TS8J.Checks27800
import Certificates.Kernel.U43Rho.Glue

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27800

open CFSG.KS.Raw.Orb (PRep prep_of_rep permOK_facts)
open CFSG.EvenSporadicStandard.Fin76b CFSG.LieType.Multipliers.U43

theorem prep_SI {j : Nat} (hj : j < 7) {g : Equiv.Perm (Fin 820)}
    (hP : PRep 820 10 (KernelU43B.C.S j) g) : PRep 820 10 (KernelU43B.C.SI j) g⁻¹ := fun y => by
  obtain ⟨-, -, h⟩ := permOK_facts (CFSG.KS.Raw.Orb.allN_iff.1 KernelU43B.perm j hj)
  have e := (h (g⁻¹ y) (g⁻¹ y).2).2
  have e2 : g (g⁻¹ y) = y := by simp
  rw [hP (g⁻¹ y), e2] at e
  exact e

theorem prep_A : PRep 820 10 (KernelU43B.C.S 0) (psi xElt) := by
  apply prep_of_rep
  rw [← KernelU43B.unpack_of_bind (by decide) KernelU43B.bindA]
  exact rep_tabA

theorem prep_B : PRep 820 10 (KernelU43B.C.S 1) (psi yElt) := by
  apply prep_of_rep
  rw [← KernelU43B.unpack_of_bind (by decide) KernelU43B.bindB]
  exact rep_tabB

theorem LT_ge {l : Nat} (hl : 4 ≤ l) : CFSG.KD.TS8J.LT l = KernelU43Rho.RH 0 := by
  unfold CFSG.KD.TS8J.LT
  rw [CFSG.KC.TS8WrK.beq_false (x := l) (y := 0) (by omega),
    CFSG.KC.TS8WrK.beq_false (x := l) (y := 1) (by omega),
    CFSG.KC.TS8WrK.beq_false (x := l) (y := 2) (by omega),
    CFSG.KC.TS8WrK.beq_false (x := l) (y := 3) (by omega)]
  rfl

theorem letter_prep (l : Nat) : ∃ g ∈ U43Ext, PRep 820 10 (CFSG.KD.TS8J.LT l) g := by
  have hx : psi xElt ∈ U43Ext := Subgroup.subset_closure (Or.inl ⟨xElt, rfl⟩)
  have hy : psi yElt ∈ U43Ext := Subgroup.subset_closure (Or.inl ⟨yElt, rfl⟩)
  have hr : rhoPerm ∈ U43Ext := Subgroup.subset_closure (Or.inr rfl)
  rcases Nat.lt_or_ge l 4 with hl | hl
  · interval_cases l
    · exact ⟨_, hx, prep_A⟩
    · exact ⟨_, hy, prep_B⟩
    · exact ⟨_, U43Ext.inv_mem hx, prep_SI (by norm_num) prep_A⟩
    · exact ⟨_, U43Ext.inv_mem hy, prep_SI (by norm_num) prep_B⟩
  · rw [LT_ge hl]
    exact ⟨_, hr, prep_of_rep KernelU43Rho.rep_RH⟩

end CertificateChecks.Batch27800

public section

namespace Certificates

open CertificateChecks

open CFSG.KD.TS8J in
theorem certificate27800 : ∃ J : Subgroup (Equiv.Perm (Fin 820)), J ≤ CFSG.EvenSporadicStandard.Fin76b.U43Ext ∧
    Nat.card J = 256 ∧ ∀ ζ ∈ J, ∀ α ∈ J, ∀ t ∈ J, ∀ g₁ ∈ J, ∀ g₂ ∈ J, ∀ h₁ ∈ J, ∀ h₂ ∈ J,
      CFSG.EvenSporadicStandard.Fin76b.OuterTable ζ α t g₁ g₂ h₁ h₂ →
        ∃ k ∈ CFSG.EvenSporadicStandard.Fin76b.U43Ext, k * ζ * k⁻¹ = α :=
  CFSG.KC.TS8JKSound.cert_of_checks (H := CFSG.EvenSporadicStandard.Fin76b.U43Ext)
    CertificateChecks.Batch27800.letter_prep ch27800gen (by decide +kernel) ch27800cw ch27800tree
    (by
      intro s hs
      interval_cases s
      exacts [ch27800rec0, ch27800rec1, ch27800rec2, ch27800rec3, ch27800rec4, ch27800rec5,
        ch27800rec6, ch27800rec7, ch27800rec8, ch27800rec9, ch27800rec10, ch27800rec11,
        ch27800rec12, ch27800rec13, ch27800rec14, ch27800rec15])
    (by
      intro s hs
      interval_cases s
      exacts [ch27800mt0, ch27800mt1, ch27800mt2, ch27800mt3, ch27800mt4, ch27800mt5,
        ch27800mt6, ch27800mt7])
    ch27800iv ch27800sort ch27800rt ch27800z ch27800za ch27800rows

end Certificates
