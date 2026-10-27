module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Quasithin.Background.C48SporCoverM22Data
public meta import CFSG.Quasithin.Background.C48SporCoverM22Data
public meta import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.GroupTheory.LocalCores.Fitting
public meta import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Action
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Quasithin.Background.C48SporCoverStab
public meta import CFSG.Quasithin.Background.C48SporCoverStab
public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public meta import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public import CFSG.Sporadic.Schreier.ImagePairs
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC48M22

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Recognition.M22Multiplier CFSG.Quasithin.C48Cover

@[expose] def zOf (l : Fin 2 × Bool) : ℤ := if l.2 then Int.ofNat (l.1.val + 1) else Int.negSucc l.1.val

@[expose] def eW (j : ℕ) : List ℤ :=
  (CFSG.CosetTable.substWord m22GenWords (m22Word (e8NormW.getD j []))).map zOf

meta def gE8 : Array (Array Nat) :=
  (e8Gen.map fun g => (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

meta def SE8 : Array (Array Nat) := strongOf 22 gE8 e8ChainW

meta def baseE8 : Array Nat := #[0, 1, 2]

end CertificateChecks.KernelC48M22

#ks_rawchain CertificateChecks.KernelC48M22.CE8 22 5 16 CertificateChecks.KernelC48M22.SE8
  CertificateChecks.KernelC48M22.baseE8 2 CFSG.Quasithin.C48Cover.e8ChainW

end
