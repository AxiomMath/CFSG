module

public import Certificates.Kernel.Co1B.Syl2B
public import Certificates.Kernel.Co1B.Chk25170
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Comm25170

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.TwoBNative
  CFSG.EvenSporadicStandard.TwoCo1.HypOne CFSG.EvenSporadicStandard.Solomon78
  CertificateChecks.KernelCo1B CertificateChecks.KernelSporSch.Co1Packed

theorem twoBCommOf_of {M MI : Nat → Nat} {A : Nat} {ws : List (List Nat)} {base : List Rows}
    (hb : base = (List.range 4).map fun i => unpack 24 24 (M i))
    (hw : ws.map decWord = [twoBCommWX, twoBCommWY]) (hK : dagWK M MI 4 6 ws = true)
    (hA : aR = unpack 24 24 A)
    (hc : (Nat.beq (CFSG.KC.Co1B.mulWK (M 4) A) (CFSG.KC.Co1B.mulWK A (M 4)) &&
      Nat.beq (CFSG.KC.Co1B.mulWK (M 5) A) (CFSG.KC.Co1B.mulWK A (M 5)) &&
      Nat.beq (CFSG.KC.Co1B.mulWK (M 4) (M 5))
        (CFSG.KC.Co1B.mulWK A (CFSG.KC.Co1B.mulWK (M 5) (M 4)))) = true) :
    twoBCommOf (dag base [twoBCommWX, twoBCommWY]) = true := by
  rw [← hw, dagWK_sound hb hK]
  simp only [Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨⟨e₁, e₂⟩, e₃⟩ := hc
  unfold twoBCommOf
  dsimp only
  rw [Syl2B.getD_range_map _ (by decide : 4 < 6), Syl2B.getD_range_map _ (by decide : 5 < 6), hA]
  simp only [mul_unpackW, e₁, e₂, e₃, beq_self_eq_true, Bool.and_self]

theorem pick_eq : pickRows ((List.range Syl2B.S2.N).map fun i => unpack 24 24 (Syl2B.S2.M i),
      (List.range Syl2B.S2.N).map fun i => unpack 24 24 (Syl2B.S2.MI i), true) sylIdxB =
    (List.range 4).map fun i => unpack 24 24 (CD.M i) := by
  have hj : ∀ j ∈ sylIdxB, j < Syl2B.S2.N := Syl2B.hN.2
  have h := kCB
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨e₀, e₁⟩, e₂⟩, e₃⟩ := h
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  rw [hr]
  simp only [pickRows, sylIdxB, List.map_cons, List.map_nil]
  rw [Syl2B.getD_range_map _ (hj 80 (by decide)), Syl2B.getD_range_map _ (hj 81 (by decide)),
    Syl2B.getD_range_map _ (hj 82 (by decide)), Syl2B.getD_range_map _ (hj 83 (by decide)),
    e₀, e₁, e₂, e₃]

theorem aR_D1 : aR = unpack 24 24 (Cent2045.D1.M 0) := by
  rw [aR_u, Nat.eq_of_beq_eq_true Cent2045.kb0]

theorem check_of {D₁ DS : List Rows × List Rows × Bool}
    (h₁ : D₁ = ((List.range 43).map fun i => unpack 24 24 (Cent2045.D1.M i),
      (List.range 43).map fun i => unpack 24 24 (Cent2045.D1.MI i), true))
    (hS : DS = ((List.range Syl2B.S2.N).map fun i => unpack 24 24 (Syl2B.S2.M i),
      (List.range Syl2B.S2.N).map fun i => unpack 24 24 (Syl2B.S2.MI i), true)) :
    (D₁.2.2 && DS.2.2 && twoBCommOf (dag (pickRows DS sylIdxB) [twoBCommWX, twoBCommWY])) =
      true := by
  subst h₁ hS
  dsimp only
  rw [twoBCommOf_of pick_eq kCW kCD aR_D1 kComm]
  rfl

open Certificates in
theorem c25170 : CFSG.EvenSporadicStandard.Solomon78.twoBCommCheck = true :=
  check_of (D₁ := brayRows aR twoBD1)
    (DS := dag (CFSG.Sporadic.Co1Block.Native.brayElts (brayRows aR twoBD1) twoBBray) sylD2B)
    Syl2B.dag₁_eq Syl2B.dagS_eq

end CertificateChecks.KernelCo1B.Comm25170

end
