module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeDefs
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Dag
public import Certificates.Data.TabCo1ThreeB
import Certificates.Kernel.Co1ThreeK.GlueCen
import Certificates.Kernel.Co1ThreeK.GluePlane

public section

namespace Certificates

open CertificateChecks.KernelCo1ThreeK in
open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271 in
theorem certificate10146 :     (∀ A : Subgroup ↥GA, A ≤ Co1T.Qg → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → 729 ≤ Nat.card A →
      A ≤ Subgroup.closure {x | x ∈ Co1T.aGA}) ∧
    ∃ n : ↥GA, n⁻¹ * Co1T.root 1 * n ∈ Subgroup.closure {x | x ∈ Co1T.aGA} ∧
      n⁻¹ * ⟨TabCo1.kG TabCo1ThreeB.ext 91, TabCo1.kG_mem _ 91⟩ * n ∈
        Subgroup.closure {x | x ∈ Co1T.aGA} := by
  refine ⟨fun A hAQ hA h => ?_, ?_⟩
  · rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.SplitData.T_eq_closure eSplitK]
    exact le_TK hAQ hA h
  · simpa only [CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.SplitData.T_eq_closure]
      using plane_K

end Certificates
