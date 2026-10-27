
module

public import Certificates.Certificate3166Base
import Certificates.Kernel.HN3166.SimpleBase

public import CFSG.Sporadic.HN.F5Group
public import CFSG.Sporadic.Recognition.HNMultiplierInputs
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Perm.ChainSpec
public import CFSG.Sporadic.HN.F5Chain
import CFSG.Sporadic.Presentation.HNInputs
import CFSG.Sporadic.HNBase
import CFSG.Sporadic.Presentation.HN
import Certificates.Data.CFSGNative.Bridge.HNGPL
import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.HN3166.Simple
import Certificates.Kernel.HNMult.Facts
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Recognition.CoverChainSub
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.F5 in
theorem certificate3166 : mA CFSG.Sporadic.HN.Native.hnData ^ 2 = 1 ∧ mB CFSG.Sporadic.HN.Native.hnData ^ 3 = 1 ∧
    (∃ g : J CFSG.Sporadic.HN.Native.hnData,
      orderOf (CFSG.Sporadic.F5.a CFSG.Sporadic.HN.Native.hnData * (g⁻¹ * b CFSG.Sporadic.HN.Native.hnData * g)) =
        19) ∧
    (∀ M : Matrix (Fin (CFSG.Sporadic.HN.Native.hnData.d)) (Fin (CFSG.Sporadic.HN.Native.hnData.d))
        (ZMod 5),
      M * mA CFSG.Sporadic.HN.Native.hnData = mA CFSG.Sporadic.HN.Native.hnData * M →
      M * mB CFSG.Sporadic.HN.Native.hnData = mB CFSG.Sporadic.HN.Native.hnData * M →
      ∃ c : ZMod 5, M = c • 1) ∧
    Nat.card (J CFSG.Sporadic.HN.Native.hnData) = 273030912000000 ∧
    ((∀ r ∈ CFSG.Sporadic.Recognition.HNMultiplier.hnRels,
      FreeGroup.lift (fun i : Fin 7 => CFSG.Sporadic.Bridge.TableSurj.img
        CFSG.Sporadic.Recognition.HNMultiplier.hnTabSpec
        (CFSG.Perm.pairG (CFSG.Sporadic.F5.gs CFSG.Sporadic.HN.Native.hnData)) i.val) (FreeGroup.mk r) = 1) ∧
      (∀ i, FreeGroup.lift (fun j : Fin 7 => CFSG.Sporadic.Bridge.TableSurj.img
        CFSG.Sporadic.Recognition.HNMultiplier.hnTabSpec
        (CFSG.Perm.pairG (CFSG.Sporadic.F5.gs CFSG.Sporadic.HN.Native.hnData)) j.val)
        (FreeGroup.mk (CFSG.Sporadic.Recognition.HNMultiplier.hnCommWord i)) =
        CFSG.Sporadic.Bridge.TableSurj.img CFSG.Sporadic.Recognition.HNMultiplier.hnTabSpec
          (CFSG.Perm.pairG (CFSG.Sporadic.F5.gs CFSG.Sporadic.HN.Native.hnData)) i.val) ∧
      Subgroup.closure (Set.range fun i : Fin 7 => CFSG.Sporadic.Bridge.TableSurj.img
        CFSG.Sporadic.Recognition.HNMultiplier.hnTabSpec
        (CFSG.Perm.pairG (CFSG.Sporadic.F5.gs CFSG.Sporadic.HN.Native.hnData)) i.val) = ⊤) :=
  ⟨KernelHN.facts3166.1, KernelHN.facts3166.2.1, KernelHN.facts3166.2.2.1,
    KernelHN.facts3166.2.2.2.1, KernelHN.facts3166.2.2.2.2, KernelHNMult.facts⟩

end Certificates
