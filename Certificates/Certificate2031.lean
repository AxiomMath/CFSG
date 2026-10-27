
module

public import Certificates.Certificate2031Base

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadsInputs
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Monster.B.Classical.PlaneData
import Certificates.Kernel.LocalComp.M22Hexads
import CFSG.Sporadic.Schreier.M22Data
meta import CFSG.Sporadic.Schreier.M22Data
import Certificates.Data.CFSGNative.Mathieu.M22

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign CFSG.Sporadic.Mathieu in
open CFSG.Monster.B.Classical.Plane in
open scoped Pointwise in
theorem certificate2031 : (hexadList.length = 77 ∧ hexadList.Nodup ∧ hexad0 ∈ hexadList ∧
      hexadList.all (fun B => B.card == 6) = true ∧
      hexadList.all (fun B => hexadMasks.contains (mask (B.map m22gA.toEmbedding)) &&
        hexadMasks.contains (mask (B.map m22gB.toEmbedding))) = true
    )
    ∧ (∀ x y z : Fin 22, x ≠ y → x ≠ z → y ≠ z →
      (hexadMasks.filter fun m => m.testBit x && m.testBit y && m.testBit z).length = 1
    )
    ∧ (∀ m ∈ hexadMasks,
      (hexadMasks.filter fun m' => interBits m m' == 0).length = 16 ∧
        (hexadMasks.filter fun m' => interBits m m' == 2).length = 60
    )
    ∧ (m22Count (fun g => ∀ x ∈ hexad0, g x ∈ hexad0) = 5760) :=
  ⟨KernelLC.hexadList_checks', KernelLC.hexadMasks_triples', KernelLC.hexadMasks_intersections',
    KernelLC.m22Count_hexad0⟩

end Certificates

end
