
module

public import Certificates.Certificate1021Base1

public import CFSG.Sporadic.Th.KernelContract
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Certificates.Kernel.Th.Soundness
import Certificates.Kernel.Th.Dce
import Certificates.Kernel.Th.Sylow2
import Certificates.Kernel.Th.Sylow3
import Certificates.Kernel.Th.Sylow5
import Certificates.Kernel.Th.Sylow7
import Certificates.Kernel.Th.Orders
import Certificates.Kernel.Th.Fwd
import Certificates.Kernel.Th.Gen
import Certificates.Kernel.Th.DceStruct
import Certificates.Kernel.ThCent.Contract
import Certificates.Kernel.ThDemp.OrbAssembly
import CFSG.Sporadic.ThSchreier.LocalOrbit
import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
meta import CFSG.Sporadic.ThSchreier.Words
meta import CFSG.Sporadic.ThSchreier.LocalData
import CFSG.Sporadic.Th.Max3.Involutions
import CFSG.Sporadic.Th.Max3.AllConjInputs
import CFSG.Sporadic.Th.Max3.Quotient
import CFSG.Sporadic.Th.Max3.InvolutionsInputs
import CFSG.Sporadic.Th.Max3.Core
import CFSG.Sporadic.Th.Max3.AltNine
import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.Sporadic.Th.Max3.QuotientInputs
import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.Th.KernelCentralizer
public import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.Th.Soundness CFSG.Sporadic.Th CertificateChecks.KernelTh

theorem th_kernel_facts_ok :
    CFSG.Sporadic.Th.Kernel.KernelFacts := by
  have hJ : Nat.card CFSG.Blueprint.NativeSporadic.Th = Nat.card J :=
    Nat.card_congr thEquivJ.toEquiv
  have hd := dce_sound dceData dce_ok
  have ho := orders_sound ordersData orders_hA orders_hB orders_ok
  have hf := fwd_sound fwdData fwd_hA fwd_hB fwd_chk
  have hg := gen_sound genData gen_hA gen_hB gen_ok
  exact {
    finite := hd.1
    card_le := hd.2
    dvd2 := hJ ▸ sylow2_sound sylow2Data sylow2_hA sylow2_hB sylow2_chk
    dvd3 := hJ ▸ sylow3_sound sylow3Data sylow3_hA sylow3_hB sylow3_chk
    dvd5 := hJ ▸ sylow5_sound sylow5Data sylow5_hA sylow5_hB sylow5_chk
    dvd7 := hJ ▸ sylow7_sound sylow7Data sylow7_hA sylow7_hB sylow7_chk
    dvd13 := hJ ▸ ho.1
    dvd19 := hJ ▸ ho.2.1
    dvd31 := hJ ▸ ho.2.2.1
    ab19 := ho.2.2.2
    fwd := hf.1
    x_fix := hf.2.1
    y_fix := hf.2.2.1
    b_moves := hf.2.2.2
    dce := dceStruct_sound dceStructData dceStruct_chk
    gen0 := hg.1
    gen1 := hg.2 }

theorem certificate1021 : CFSG.Sporadic.Th.Kernel.ThKernelFacts := by
  have h := th_kernel_facts_ok
  refine ⟨h, ?_, CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M h, KernelThCent.exists_cent7 h, ?_⟩
  · rw [← CFSG.Sporadic.ThSchreier.localY_eq, pow_three, ← mul_assoc]
    exact CFSG.Sporadic.ThSchreier.localY_cube
  · obtain ⟨⟨x, -, hx, hc⟩, -⟩ :=
      KernelThDemp.th_centralizer_bounds (Kernel.card_J_eq h).le
    exact ⟨x, hx, hc⟩

end Certificates
