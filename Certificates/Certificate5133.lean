module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.ClassCount
public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.Recognition.CertU33Psu
public import CFSG.Quasithin.Recognition.CertU33Perm
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.GH74.KGroups.U33Inputs
import Certificates.Kernel.Misc.KGroups.U33

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.KGroups in
open CFSG.GH74.KGroups.U33 in
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate5133 : (QP.check = true ∧ QP.orderCertificate = 6048)
    ∧ (QA.check = true ∧ QA.orderCertificate = 12096)
    ∧ (orderOf pu = 2 ∧ orderOf pv = 7 ∧ PairInv wsU pu pv)
    ∧ (pu ∈ Subgroup.closure {pa, pb} ∧ pv ∈ Subgroup.closure {pa, pb} ∧
        pa ∈ Subgroup.closure {pu, pv} ∧ pb ∈ Subgroup.closure {pu, pv})
    ∧ (sg0 * pu * sg0⁻¹ ∈ Subgroup.closure {pa, pb} ∧
        sg0 * pv * sg0⁻¹ ∈ Subgroup.closure {pa, pb})
    ∧ (∀ k : Fin 5, CFSG.Quasithin.u33Img k ∈ Subgroup.closure {pa, pb})
    ∧ Nat.card {x // x ∈ Subgroup.closure {pa, pb} ∧ orderOf x = 2} = 63
    ∧ Nat.card {y // y ∈ Subgroup.closure {pa, pb} ∧ orderOf y = 7 ∧ PairInv wsU pu y} = 192
    ∧ centCard (Subgroup.closure {pa, pb}) pu = 96
    ∧ centCard (Subgroup.closure {pa, pb}) pt2 = 24
    ∧ (pt2 ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf pt2 = 2)
    ∧ Nat.card {x // x ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf x = 2} = 315
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) pu = 192
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) pt2 = 48
    ∧ (∀ σ ∈ Subgroup.closure {pa, pb, sg0}, σ * pu = pu * σ → σ * pv = pv * σ → σ = 1)
    ∧ E9At (Subgroup.closure {pa, pb, sg0}) pu
    ∧ E9At (Subgroup.closure {pa, pb, sg0}) pt2
    ∧ (px1 ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf px1 = 3)
    ∧ (px2 ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf px2 = 3)
    ∧ Nat.card {x // x ∈ Subgroup.closure {pa, pb, sg0} ∧ orderOf x = 3} = 728
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) px1 = 216
    ∧ centCard (Subgroup.closure {pa, pb, sg0}) px2 = 18
    ∧ E27At (Subgroup.closure {pa, pb, sg0}) px1
    ∧ E27At (Subgroup.closure {pa, pb, sg0}) px2 := KernelMisc.U33K.facts

end Certificates
