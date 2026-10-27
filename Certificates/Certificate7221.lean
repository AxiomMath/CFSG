module

public import CFSG.Quasithin.Background.C48SporCoverM22Data
import Certificates.Kernel.C48M22Stab.Glue
import Certificates.Kernel.C48M22Stab.Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.Open.Defs
public import CFSG.Quasithin.Background.C48SporCoverStab
public import CFSG.Quasithin.Vol2.KGFactC31OrbCheck
public import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.M22Data

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M22
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Schreier in
theorem certificate7221 : Nat.card (Subgroup.closure {g : Equiv.Perm (Fin 22) | g ∈ CFSG.Quasithin.C48Cover.e8Gen}) =
      1344 ∧
    ((CFSG.Quasithin.C48Cover.e8Gen.zip CFSG.Quasithin.C48Cover.e8Masks).all
      fun p => masksOK 22 e8T (toTable p.1) p.2) = true ∧
    ∃ S : Subgroup (PresentedGroup {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}),
      (∀ u ∈ CFSG.Quasithin.C48Cover.e8SubW, PresentedGroup.mk _ (FreeGroup.mk u) ∈ S) ∧
        PresentedGroup.mk _ (FreeGroup.mk m22B11) ∉ S := KernelC48M22.cert7221

end Certificates
