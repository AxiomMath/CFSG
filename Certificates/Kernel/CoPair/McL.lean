module

public import Certificates.Kernel.CoPair.Gens
public import CFSG.Certificates.Kernel.CoPairEqSound
public import Certificates.Data.Kernel.CoPairMcL
public import Certificates.Data.CFSGNative.MonsterAxis.CoPairData
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.F3R
import CFSG.Certificates.Kernel.Common.Harness

public section

#ks_chars CertificateChecks.KernelCoPair.SeedA CFSG.Sporadic.McL.Native.seedA
#ks_chars CertificateChecks.KernelCoPair.SeedB CFSG.Sporadic.McL.Native.seedB

namespace CertificateChecks.KernelCoPair

open CFSG.KC.CoPair CFSG.Monster.Existence.CoPair.Native CFSG.F3.Native CFSG.KS.F3R
  CFSG.Sporadic.McL.Native CFSG.Sporadic.VecOrbit.Native

set_option maxRecDepth 100000

@[expose] def MclMAText : String := include_str "mclma.hex"
@[expose] def MclMBText : String := include_str "mclmb.hex"
@[expose] def MclTAText : String := include_str "mclta.hex"
@[expose] def MclTBText : String := include_str "mcltb.hex"
@[expose] def MclQText : String := include_str "mclq.hex"
@[expose] def MclLText : String := include_str "mcll.hex"
@[expose] def MclRText : String := include_str "mclr.hex"
@[expose] def MclSAText : String := include_str "mclsa.hex"
@[expose] def MclSBText : String := include_str "mclsb.hex"
@[expose] def MclVText : String := include_str "mclv.hex"

@[expose] noncomputable def MclMA : Nat := by hex_nat MclMAText 144 17730659778721962708
@[expose] noncomputable def MclMB : Nat := by hex_nat MclMBText 144 16933142049024532241
@[expose] noncomputable def MclTA : Nat := by hex_nat MclTAText 4608 5525977579776340917
@[expose] noncomputable def MclTB : Nat := by hex_nat MclTBText 4607 12134215247092008288
@[expose] noncomputable def MclQ : Nat := by hex_nat MclQText 1650 1523906579867669833
@[expose] noncomputable def MclL : Nat := by hex_nat MclLText 4394 6243786561905533550
@[expose] noncomputable def MclR : Nat := by hex_nat MclRText 1098 17652918042029055245
@[expose] noncomputable def MclSA : Nat := by hex_nat MclSAText 1099 9631743679706876422
@[expose] noncomputable def MclSB : Nat := by hex_nat MclSBText 1099 5636901205293987829
@[expose] noncomputable def MclV : Nat := by hex_nat MclVText 4397 13530280025403095099

@[expose] noncomputable def MclD : EqData :=
  ⟨MX, MY, TX, TY, MclMA, MclMB, MclTA, MclTB, MclQ, MclL, MclR, MclSA, MclSB, 275⟩

theorem mRowsA : rowsW MclMA TX TY (mclWordA ()) = true := by quickRfl
theorem mRowsB : rowsW MclMB TX TY (mclWordB ()) = true := by quickRfl
theorem mTabA : tabOK MclMA MclTA = true := by quickRfl
theorem mTabB : tabOK MclMB MclTB = true := by quickRfl
theorem mFixA : Nat.beq (bact MclTA 1) 1 = true := by quickRfl
theorem mFixB : Nat.beq (bact MclTB 1) 1 = true := by quickRfl
theorem mPts : allN 275 (eqPt MclTA MclTB MclQ MclL MclSA MclSB 275 275) = true := by quickRfl
theorem mReps : allN 275 (repPt MclL MclR 275) = true := by quickRfl

theorem mcl_eq : eqOK (mclWordA ()) (mclWordB ()) (seedW1 ()) 275 MclD = true :=
  eqOK_intro rowsX rowsY tabX tabY mRowsA mRowsB mTabA mTabB (by decide)
    (Nat.eq_of_beq_eq_true mFixA) (Nat.eq_of_beq_eq_true mFixB) ((allN_iff _ _).1 mPts)
    ((allN_iff _ _).1 mReps)

@[expose] noncomputable def ATK : Array V := transposeK 21 (rowsOfL 21 SeedA.chars)

@[expose] noncomputable def BTK : Array V := transposeK 21 (rowsOfL 21 SeedB.chars)

theorem tA : transpose 21 (matA ()) = ATK := by
  unfold matA ATK
  rw [SeedA.eq, rowsOf_ofList, transpose_eq]

theorem tB : transpose 21 (matB ()) = BTK := by
  unfold matB BTK
  rw [SeedB.eq, rowsOf_ofList, transpose_eq]

@[expose] noncomputable def vecK (j : Nat) : Bool :=
  (decVM (f64 MclV j)).wf && Nat.blt (f16 MclSA j) 275 && Nat.blt (f16 MclSB j) 275 &&
    (combK 21 ATK (decVM (f64 MclV j))).beq (decVM (f64 MclV (f16 MclSA j))) &&
    (combK 21 BTK (decVM (f64 MclV j))).beq (decVM (f64 MclV (f16 MclSB j)))

theorem mVec : allN 275 vecK = true := by quickRfl

theorem mBasis : basisOK 21 (chainQ.map fun r => decVM (f64 MclV r)) basisTinv = true := by
  unfold basisOK
  simp only [chainQ, List.map_toArray, List.map_cons, List.map_nil]
  simp only [wfM_eq, eqM_eq, mul_eq]
  decide +kernel

theorem mcl_vec : mclVecOK MclV MclSA MclSB := by
  refine ⟨fun j hj => ?_, mBasis⟩
  have h := (allN_iff _ _).1 mVec j hj
  unfold vecK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [tA, tB, comb_eq, comb_eq]
  exact ⟨h1, h2, h3, h4, h5⟩

end CertificateChecks.KernelCoPair

end
