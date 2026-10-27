module

public import CFSG.Quasithin.Recognition.St84.AutJ2VtxInputs
public import CFSG.Sporadic.SmallOddCore.LocalSpec
import Certificates.Kernel.AutJ2Vtx.NormFacts
import Certificates.Kernel.AutJ2Vtx.KFacts

public section

namespace Certificates

open CFSG.Quasithin.F112R.St84.AutJ2Model CertificateChecks.KernelAJV CertificateChecks.KernelAJC

open CFSG.Quasithin.F112R.St84.AutJ2Model CFSG.Sporadic.SmallOddCore in
theorem certificate733002 :
    (autJ2VtxC0 () = true) ∧
    (Nat.card (genOf 315 sylT) = 256 ∧ Nat.card (genOf 315 (sylT ++ [gWT])) = 3840 ∧
      Nat.card (genOf 315 (sylT ++ [g1T])) = 2304) ∧
    (Nat.card (genOf 315 q2T) = 32 ∧
      genOf 315 (sylT ++ [gWT]) ≤
        Subgroup.normalizer (genOf 315 q2T : Set (Equiv.Perm (Fin 315)))) ∧
    (autJ2VtxC3 () = true) ∧
    (autJ2VtxC4 () = true) ∧
    (autJ2VtxC5 () = true) ∧
    (Nat.card (genOf 315 [rmRT, bmRT, tmRT, gmRT]) = 36 ∧
      genOf 315 (sylT ++ [g1T]) ≤
        Subgroup.normalizer (genOf 315 q1Gens : Set (Equiv.Perm (Fin 315)))) ∧
    (Nat.card (genOf 315 q1Gens) = 64) := by
  have hW : sylT ++ [gWT] = [0, 1, 2, 6].map tt := by rw [sylT_eq, gWT_eq]; rfl
  have hX1 : sylT ++ [g1T] = [0, 1, 2, 7].map tt := by rw [sylT_eq, g1T_eq]; rfl
  have hQ2 : q2T = [8, 9, 10, 11].map tt := by rw [q2T_eq]; rfl
  have hA : [rmRT, bmRT, tmRT, gmRT] = [21, 20, 18, 19].map tt := by
    rw [rmRT_eq, bmRT_eq, tmRT_eq, gmRT_eq]; rfl
  have hQ1 : q1Gens = [14, 15, 16, 17].map tt := by
    rw [q1Gens, e1RT_eq, e2RT_eq, f1RT_eq, f2RT_eq]; rfl
  have hS : sylT = [0, 1, 2].map tt := by rw [sylT_eq]; rfl
  refine ⟨c0, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, c3, c4, c5,
    ⟨?_, ?_⟩, ?_⟩
  · rw [hS]; exact card_S
  · rw [hW]; exact card_W
  · rw [hX1]; exact card_X1
  · rw [hQ2]; exact card_Q2
  · rw [hW, hQ2]; exact norm_W
  · rw [hA]; exact card_A
  · rw [hX1, hQ1]; exact norm_X1
  · rw [hQ1]; exact card_Q1

end Certificates
