module

public import CFSG.Monster.B.TwoA.Census.CosetSquaresInputs
public import Certificates.Kernel.MonsterB.Sq3022
public import CFSG.Certificates.Kernel.MonsterB.Rep4371RowEq

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.KC.KDense
  CFSG.KC.Rep4371Row CFSG.KC.Trace6091

namespace CertificateChecks.Batch3022

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Rep4371 CFSG.Monster.B CFSG.KC.KDense
  CFSG.KC.Rep4371Row CFSG.KC.Trace6091

open CertificateChecks.Sq3022

theorem genCheck_model : genCheck Model.conjYN Model.conjPermN = true := by decide +kernel

theorem sq_ok (i : Nat) {A P BT K : Nat} {s : Bool} {a d : Nat} (hA : cosetA i = A)
    (hP : ∀ k < 24, pe P k = (cosetArr i)[k]!) (hBT : betaTabT P = BT)
    (hK : (Model.kappaN (cosetArr i) 63).toNat = K) (hk : sqRowsT A P BT K s.toNat a d = true) :
    sqRowCheck Model.eYN Model.ePermN Model.ePauliN i (s, a, d) = true := by
  have hr := allBelow_spec hk (by decide)
  unfold sqRowCheck
  refine List.all_eq_true.2 fun c hc => ?_
  have hq : Model.pi0N c / 2 < 2048 := by
    have := pi0_lt (List.mem_range.1 hc)
    omega
  have hrq := hr _ hq
  dsimp only at hrq
  have e2 : Nat.mul 2 (Model.pi0N c / 2) = Model.pi0N c := pi0_two_mul c
  rw [e2] at hrq
  obtain ⟨h0, h1⟩ := bAnd_true hrq
  have key : ∀ η : Bool, Nat.beq (sqT A P BT K η.toNat (Model.pi0N c))
      (ePauliT s.toNat a d η.toNat (Model.pi0N c)) = true →
      (eSigmaSq Model.eYN Model.ePermN i η c == Model.ePauliN (s, a, d) η c) = true := by
    intro η h
    apply encB_beq
    have h' := Nat.eq_of_beq_eq_true h
    rw [sqT_eq hP hBT hK, ePauliT_eq, ePauliN_pi0, eYN_pi0, ← hA] at h'
    exact h'
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨key false h0, key true h1⟩

theorem hP1 : ∀ k < 24, pe P1 k = (cosetArr 1)[k]! := by decide +kernel

theorem hP2 : ∀ k < 24, pe P1 k = (cosetArr 2)[k]! := by decide +kernel

theorem hP6 : ∀ k < 24, pe P6 k = (cosetArr 6)[k]! := by decide +kernel

theorem hK_of {i P BT : Nat} (hP : ∀ k < 24, pe P k = (cosetArr i)[k]!) (hBT : betaTabT P = BT)
    (h : kappaT BT 63 = 0) : (Model.kappaN (cosetArr i) 63).toNat = 0 := by
  rw [← kappaT_eq hP, hBT, h]

theorem sqRow_model : ∀ i ∈ [1, 2, 6],
    sqRowCheck Model.eYN Model.ePermN Model.ePauliN i (sqPauli i) = true := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact sq_ok 1 (s := false) (by decide +kernel) hP1 bt1 (hK_of hP1 bt1 k1) rows1
  · exact sq_ok 2 (s := true) (by decide +kernel) hP2 bt1 (hK_of hP2 bt1 k1) rows2
  · exact sq_ok 6 (s := false) (by decide +kernel) hP6 bt6 (hK_of hP6 bt6 k6) rows6

end CertificateChecks.Batch3022

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Rep4371 in
theorem certificate3022 : (genCheck Native.conjYN Native.conjPermN = true)
    ∧ (∀ i ∈ [1, 2, 6],
       sqRowCheck Native.eYN Native.ePermN Native.ePauliN i (sqPauli i) = true) := by
  rw [native_conjYN, native_conjPermN, native_eYN, native_ePermN, native_ePauliN]
  exact ⟨CertificateChecks.Batch3022.genCheck_model, CertificateChecks.Batch3022.sqRow_model⟩

end Certificates
