module

public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono26_0
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono26_1
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono26_2
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Mono26_3
public import CFSG.Certificates.Kernel.BabyMonster.DyLane.Quot26
public import Certificates.Kernel.BabyMonster.Aligned
public import Certificates.Kernel.BabyMonster.LaneBase

public section

namespace CertificateChecks.KernelBM.Dy

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Lat CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic

set_option maxRecDepth 100000

@[expose] noncomputable def rowsBelow (C : List (List Nat)) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (Nat.blt (recOf C i) (Nat.shiftLeft (nat_lit 1) (nat_lit 4370))))

set_option exponentiation.threshold 8192 in
theorem rowsBelow_sound {C : List (List Nat)} : ∀ {n : Nat}, rowsBelow C n = true →
    ∀ i < n, recOf C i < 2 ^ 4370
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    have e : rowsBelow C (n + 1) = andB (rowsBelow C n)
        (Nat.blt (recOf C n) (Nat.shiftLeft (nat_lit 1) (nat_lit 4370))) := rfl
    obtain ⟨h1, h2⟩ := andB_true (e ▸ h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact rowsBelow_sound h1 i hi
    · have h3 : recOf C i < 1 <<< 4370 := Nat.le_of_ble_eq_true h2
      rwa [Nat.one_shiftLeft] at h3

theorem below_F0 : rowsBelow NativePair.F0.rows 4370 = true := by quickRfl

theorem aligned26 : allAligned M26.b0 = true := by quickRfl

theorem stab26 : ∀ s < 4370, RowStabP CFSG.KC.BM.Dyadic.Bs (kNumMono (nthN G26.b0 0))
    FixedLine.f (recOf NativePair.F0.rows s) (skipP s) := by
  have hst : ∀ s < 4370, stPOK CFSG.KC.BM.Dyadic.Bs
      (monoF CFSG.KC.BM.Dyadic.Bs M26.b0 (nthN G26.b0 1)) FixedLine.f (recOf NativePair.F0.rows)
      s = true :=
    CFSG.KC.BM.Ln.stPOK_of_lanes lnData (F := monoF CFSG.KC.BM.Dyadic.Bs M26.b0 (nthN G26.b0 1))
      (C := CFSG.KC.BM.DyLane.C26.rows) (by forall_lt_consts CFSG.KC.BM.Dyadic.lnSt26_ 274)
      CFSG.KC.BM.DyLane.lens26 (by forall_lt_consts CFSG.KC.BM.DyLane.quot26_ 69)
  intro s hs
  exact stMonoP_sound blocks rows Align.shifts aligned26 net26 (by quickRfl) hs (hst s hs)
    (rowsBelow_sound below_F0 s hs)

end CertificateChecks.KernelBM.Dy

end
