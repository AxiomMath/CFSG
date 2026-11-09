module

public import Certificates.Data.GH74.AE117
import Mathlib.Logic.Equiv.Fin.Basic

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelCensus

open Certificates.AE117

theorem cocCheck₅_eq : cocCheck₅ () = true := by decide +kernel
theorem cocCheck₆_eq : cocCheck₆ () = true := by decide +kernel

@[expose] def vecOf (n c : Nat) : Fin n → ZMod 2 := fun j => ((c / 2 ^ (j : Nat) % 2 : Nat) : ZMod 2)

theorem exists_vecOf {n : Nat} (b : Fin n → ZMod 2) : ∃ c < 2 ^ n, vecOf n c = b := by
  let f : Fin n → Fin 2 := fun j => ⟨(b j).val, ZMod.val_lt (b j)⟩
  refine ⟨finFunctionFinEquiv f, (finFunctionFinEquiv f).2, ?_⟩
  funext j
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) j
  rw [Equiv.symm_apply_apply] at h
  simp only [vecOf]
  rw [← h]
  simp [f]

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr in
@[expose] def cocQ (c : Nat) : Prop :=
  ∀ v₂ : Fin 7 → ZMod 2, ∑ i, vecOf 7 c i = 0 → ∑ i, v₂ i = 0 →
    (∀ w ∈ rels₇, inPi (evalG [ofPerm g₁₇ * ofVec (vecOf 7 c), ofPerm g₂₇ * ofVec v₂] w) = true) →
      ∃ u : Fin 7 → ZMod 2,
        eqPi (ofVec u * ofPerm g₁₇ * (ofVec u)⁻¹) (ofPerm g₁₇ * ofVec (vecOf 7 c)) = true ∧
          eqPi (ofVec u * ofPerm g₂₇ * (ofVec u)⁻¹) (ofPerm g₂₇ * ofVec v₂) = true

instance : DecidablePred cocQ := fun c => by unfold cocQ; infer_instance

theorem cocQ0 : ∀ c < 32, 0 ≤ c → cocQ c := by decide +kernel
theorem cocQ1 : ∀ c < 64, 32 ≤ c → cocQ c := by decide +kernel
theorem cocQ2 : ∀ c < 96, 64 ≤ c → cocQ c := by decide +kernel
theorem cocQ3 : ∀ c < 128, 96 ≤ c → cocQ c := by decide +kernel

theorem coc₇_rels : ∀ w ∈ rels₇, inPi (evalG [CFSG.ClassicalInvolution.Q3.AE.Wr.ofPerm g₁₇,
    CFSG.ClassicalInvolution.Q3.AE.Wr.ofPerm g₂₇] w) = true := by
  decide +kernel

theorem cocCheck₇_eq : cocCheck₇ () = true := by
  unfold cocCheck₇
  rw [decide_eq_true_iff]
  refine ⟨coc₇_rels, fun v₁ v₂ => ?_⟩
  obtain ⟨c, hc, rfl⟩ := exists_vecOf v₁
  have hq : cocQ c := by
    rcases Nat.lt_or_ge c 32 with h1 | h1
    · exact cocQ0 c h1 (Nat.zero_le c)
    rcases Nat.lt_or_ge c 64 with h2 | h2
    · exact cocQ1 c h2 h1
    rcases Nat.lt_or_ge c 96 with h3 | h3
    · exact cocQ2 c h3 h2
    · exact cocQ3 c hc h3
  exact hq v₂
theorem genCheck₅_eq : genCheck₅ () = true := by decide +kernel
theorem genCheck₆_eq : genCheck₆ () = true := by decide +kernel
theorem genCheck₇_eq : genCheck₇ () = true := by decide +kernel
theorem spanCheck_five : spanCheck 5 () = true := by decide +kernel
theorem spanCheck_six : spanCheck 6 () = true := by decide +kernel
theorem spanCheck_seven : spanCheck 7 () = true := by decide +kernel

end CertificateChecks.KernelCensus
