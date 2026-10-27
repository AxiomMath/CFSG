module

public import Certificates.Kernel.CoPair.Gens
public import Certificates.Kernel.CoPair.U62Bind
public import CFSG.Certificates.Kernel.CoPairEqSound
public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.Monster.Existence.CoPair.Native CFSG.F4.Native CFSG.Sporadic.Th.Native

set_option maxRecDepth 100000
set_option Elab.async false

@[expose] def U62MAText : String := include_str "u62ma.hex"
@[expose] def U62MBText : String := include_str "u62mb.hex"
@[expose] def U62TAText : String := include_str "u62ta.hex"
@[expose] def U62TBText : String := include_str "u62tb.hex"
@[expose] def U62QText : String := include_str "u62q.hex"
@[expose] def U62LText : String := include_str "u62l.hex"
@[expose] def U62RText : String := include_str "u62r.hex"
@[expose] def U62SAText : String := include_str "u62sa.hex"
@[expose] def U62SBText : String := include_str "u62sb.hex"

@[expose] noncomputable def U62MA : Nat := by hex_nat U62MAText 144 2632742973168773105
@[expose] noncomputable def U62MB : Nat := by hex_nat U62MBText 143 15844184724321109511
@[expose] noncomputable def U62TA : Nat := by hex_nat U62TAText 4608 818172504917304969
@[expose] noncomputable def U62TB : Nat := by hex_nat U62TBText 4608 10109451905214465701
@[expose] noncomputable def U62Q : Nat := by hex_nat U62QText 149688 4411599114163653903
@[expose] noncomputable def U62L : Nat := by hex_nat U62LText 399163 18176304535233109719
@[expose] noncomputable def U62R : Nat := by hex_nat U62RText 2771 5841360057391923112
@[expose] noncomputable def U62SA : Nat := by hex_nat U62SAText 2771 2322220972244219462
@[expose] noncomputable def U62SB : Nat := by hex_nat U62SBText 2771 11468846991434802704

@[expose] noncomputable def U62D : EqData :=
  ⟨MX, MY, TX, TY, U62MA, U62MB, U62TA, U62TB, U62Q, U62L, U62R, U62SA, U62SB, 24948⟩

noncomputable abbrev u62Pt : Nat → Bool := eqPt U62TA U62TB U62Q U62L U62SA U62SB 24948 693

theorem uRowsA : rowsW U62MA TX TY (u62WordA ()) = true := by quickRfl
theorem uRowsB : rowsW U62MB TX TY (u62WordB ()) = true := by quickRfl
theorem uTabA : tabOK U62MA U62TA = true := by quickRfl
theorem uTabB : tabOK U62MB U62TB = true := by quickRfl
theorem uFixA : Nat.beq (bact U62TA 4096) 4096 = true := by quickRfl
theorem uFixB : Nat.beq (bact U62TB 4096) 4096 = true := by quickRfl
theorem uReps : allN 693 (repPt U62L U62R 24948) = true := by quickRfl

theorem uc0 : allR 0 1000 u62Pt = true := by quickRfl
theorem uc1 : allR 1000 1000 u62Pt = true := by quickRfl
theorem uc2 : allR 2000 1000 u62Pt = true := by quickRfl
theorem uc3 : allR 3000 1000 u62Pt = true := by quickRfl
theorem uc4 : allR 4000 1000 u62Pt = true := by quickRfl
theorem uc5 : allR 5000 1000 u62Pt = true := by quickRfl
theorem uc6 : allR 6000 1000 u62Pt = true := by quickRfl
theorem uc7 : allR 7000 1000 u62Pt = true := by quickRfl
theorem uc8 : allR 8000 1000 u62Pt = true := by quickRfl
theorem uc9 : allR 9000 1000 u62Pt = true := by quickRfl
theorem uc10 : allR 10000 1000 u62Pt = true := by quickRfl
theorem uc11 : allR 11000 1000 u62Pt = true := by quickRfl
theorem uc12 : allR 12000 1000 u62Pt = true := by quickRfl
theorem uc13 : allR 13000 1000 u62Pt = true := by quickRfl
theorem uc14 : allR 14000 1000 u62Pt = true := by quickRfl
theorem uc15 : allR 15000 1000 u62Pt = true := by quickRfl
theorem uc16 : allR 16000 1000 u62Pt = true := by quickRfl
theorem uc17 : allR 17000 1000 u62Pt = true := by quickRfl
theorem uc18 : allR 18000 1000 u62Pt = true := by quickRfl
theorem uc19 : allR 19000 1000 u62Pt = true := by quickRfl
theorem uc20 : allR 20000 1000 u62Pt = true := by quickRfl
theorem uc21 : allR 21000 1000 u62Pt = true := by quickRfl
theorem uc22 : allR 22000 1000 u62Pt = true := by quickRfl
theorem uc23 : allR 23000 1000 u62Pt = true := by quickRfl
theorem uc24 : allR 24000 948 u62Pt = true := by quickRfl

theorem uchunks : ∀ k < 24, allR (1000 * k) 1000 u62Pt = true := by
  intro k hk
  interval_cases k
  exacts [uc0, uc1, uc2, uc3, uc4, uc5, uc6, uc7, uc8, uc9, uc10, uc11, uc12, uc13, uc14, uc15,
    uc16, uc17, uc18, uc19, uc20, uc21, uc22, uc23]

theorem u62_eq : eqOK (u62WordA ()) (u62WordB ()) (seedW2 ()) 693 U62D = true :=
  eqOK_intro rowsX rowsY tabX tabY uRowsA uRowsB uTabA uTabB (by decide)
    (Nat.eq_of_beq_eq_true uFixA) (Nat.eq_of_beq_eq_true uFixB)
    (all_of_allR (all_of_chunks uchunks) uc24) ((allN_iff _ _).1 uReps)

theorem uSA : allN 693 (fun i => Nat.beq (f16 U62SA i) (xw (xw (xw i)))) = true := by quickRfl

theorem uSB : allN 693 (fun i => Nat.beq (f16 U62SB i) (yw (yw i))) = true := by quickRfl

theorem u62_tabs : (∀ i < 693, f16 U62SA i = ap (t46XT ()) i) ∧
    ∀ i < 693, f16 U62SB i = ap (t46YT ()) i :=
  ⟨fun i hi => by rw [ap_t46XT i hi]; exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 uSA i hi),
    fun i hi => by rw [ap_t46YT i hi]; exact Nat.eq_of_beq_eq_true ((allN_iff _ _).1 uSB i hi)⟩

end CertificateChecks.KernelCoPair

end
