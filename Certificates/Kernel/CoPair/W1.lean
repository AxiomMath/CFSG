module

public import Certificates.Kernel.CoPair.Gens
public import CFSG.Certificates.Kernel.CoPairSound
public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.Monster.Existence.CoPair.Native

set_option Elab.async false

@[expose] def W1PText : String := include_str "w1p.hex"

@[expose] def W1EText : String := include_str "w1e.hex"

@[expose] noncomputable def W1P : Nat := by hex_nat W1PText 282624 6883942553446158791

@[expose] noncomputable def W1E : Nat := by hex_nat W1EText 753661 11200487743565646880

@[expose] noncomputable def W1D : OrbData := ⟨MX, MY, TX, TY, W1P, W1E, 0⟩

noncomputable abbrev w1Pt : Nat → Bool := orbPt TX TY W1P W1E 47104 0

theorem w1c0 : allR 0 1000 w1Pt = true := by quickRfl
theorem w1c1 : allR 1000 1000 w1Pt = true := by quickRfl
theorem w1c2 : allR 2000 1000 w1Pt = true := by quickRfl
theorem w1c3 : allR 3000 1000 w1Pt = true := by quickRfl
theorem w1c4 : allR 4000 1000 w1Pt = true := by quickRfl
theorem w1c5 : allR 5000 1000 w1Pt = true := by quickRfl
theorem w1c6 : allR 6000 1000 w1Pt = true := by quickRfl
theorem w1c7 : allR 7000 1000 w1Pt = true := by quickRfl
theorem w1c8 : allR 8000 1000 w1Pt = true := by quickRfl
theorem w1c9 : allR 9000 1000 w1Pt = true := by quickRfl
theorem w1c10 : allR 10000 1000 w1Pt = true := by quickRfl
theorem w1c11 : allR 11000 1000 w1Pt = true := by quickRfl
theorem w1c12 : allR 12000 1000 w1Pt = true := by quickRfl
theorem w1c13 : allR 13000 1000 w1Pt = true := by quickRfl
theorem w1c14 : allR 14000 1000 w1Pt = true := by quickRfl
theorem w1c15 : allR 15000 1000 w1Pt = true := by quickRfl
theorem w1c16 : allR 16000 1000 w1Pt = true := by quickRfl
theorem w1c17 : allR 17000 1000 w1Pt = true := by quickRfl
theorem w1c18 : allR 18000 1000 w1Pt = true := by quickRfl
theorem w1c19 : allR 19000 1000 w1Pt = true := by quickRfl
theorem w1c20 : allR 20000 1000 w1Pt = true := by quickRfl
theorem w1c21 : allR 21000 1000 w1Pt = true := by quickRfl
theorem w1c22 : allR 22000 1000 w1Pt = true := by quickRfl
theorem w1c23 : allR 23000 1000 w1Pt = true := by quickRfl
theorem w1c24 : allR 24000 1000 w1Pt = true := by quickRfl
theorem w1c25 : allR 25000 1000 w1Pt = true := by quickRfl
theorem w1c26 : allR 26000 1000 w1Pt = true := by quickRfl
theorem w1c27 : allR 27000 1000 w1Pt = true := by quickRfl
theorem w1c28 : allR 28000 1000 w1Pt = true := by quickRfl
theorem w1c29 : allR 29000 1000 w1Pt = true := by quickRfl
theorem w1c30 : allR 30000 1000 w1Pt = true := by quickRfl
theorem w1c31 : allR 31000 1000 w1Pt = true := by quickRfl
theorem w1c32 : allR 32000 1000 w1Pt = true := by quickRfl
theorem w1c33 : allR 33000 1000 w1Pt = true := by quickRfl
theorem w1c34 : allR 34000 1000 w1Pt = true := by quickRfl
theorem w1c35 : allR 35000 1000 w1Pt = true := by quickRfl
theorem w1c36 : allR 36000 1000 w1Pt = true := by quickRfl
theorem w1c37 : allR 37000 1000 w1Pt = true := by quickRfl
theorem w1c38 : allR 38000 1000 w1Pt = true := by quickRfl
theorem w1c39 : allR 39000 1000 w1Pt = true := by quickRfl
theorem w1c40 : allR 40000 1000 w1Pt = true := by quickRfl
theorem w1c41 : allR 41000 1000 w1Pt = true := by quickRfl
theorem w1c42 : allR 42000 1000 w1Pt = true := by quickRfl
theorem w1c43 : allR 43000 1000 w1Pt = true := by quickRfl
theorem w1c44 : allR 44000 1000 w1Pt = true := by quickRfl
theorem w1c45 : allR 45000 1000 w1Pt = true := by quickRfl
theorem w1c46 : allR 46000 1000 w1Pt = true := by quickRfl
theorem w1c47 : allR 47000 104 w1Pt = true := by quickRfl

theorem w1chunks : ∀ k < 47, allR (1000 * k) 1000 w1Pt = true := by
  intro k hk
  interval_cases k
  exacts [w1c0, w1c1, w1c2, w1c3, w1c4, w1c5, w1c6, w1c7, w1c8, w1c9, w1c10, w1c11, w1c12, w1c13,
    w1c14, w1c15, w1c16, w1c17, w1c18, w1c19, w1c20, w1c21, w1c22, w1c23, w1c24, w1c25, w1c26,
    w1c27, w1c28, w1c29, w1c30, w1c31, w1c32, w1c33, w1c34, w1c35, w1c36, w1c37, w1c38, w1c39,
    w1c40, w1c41, w1c42, w1c43, w1c44, w1c45, w1c46]

theorem w1seed : Nat.beq (f24 W1P 0) (seedW1 ()) = true := by quickRfl

theorem w1_ok : orbOK xWordN yWordN seedW1 47104 W1D = true :=
  orbOK_intro rowsX rowsY tabX tabY (by decide) (Nat.eq_of_beq_eq_true w1seed)
    (all_of_allR (all_of_chunks w1chunks) w1c47)

end CertificateChecks.KernelCoPair

end
