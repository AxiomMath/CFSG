module

public import Certificates.Data.GMS78RuCzRigidCheck
public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.CFSGNative.Ru.Data
import Certificates.Kernel.GMS78.Coset.Cards104
import Certificates.Kernel.GMS78.W104
import Certificates.Kernel.GMS78.CzJ
public import CFSG.Sporadic.Th.F2Spec
import CFSG.Certificates.CosetTableColumns
import CFSG.Certificates.CosetTableShort

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GMS78 CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj in
theorem certificate15104 : (∀ v ∈ RuCz.czJRelRels, (∀ l ∈ v, l.1 < 7) ∧
      wordProd (CFSG.Sporadic.Bridge.VecSurj.img RuPi7.pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1) ∧
    (Finite (CFSG.CosetTable.PG 6 RuCz.czRelsJW) ∧
      Nat.card (CFSG.CosetTable.PG 6 RuCz.czRelsJW) ≤ 2048) ∧ RuCz.czRigidCheck = true ∧
    RuCz.czJIdentCheck = true ∧
    (∀ v ∈ RuCz.c2RuRels, (∀ l ∈ v, l.1 < 7) ∧
      wordProd (CFSG.Sporadic.Bridge.VecSurj.img RuPi7.pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1) ∧
    (Finite (CFSG.CosetTable.PG 10 RuCz.czEps1Rels) ∧
      Nat.card (CFSG.CosetTable.PG 10 RuCz.czEps1Rels) ≤ 122880) ∧
    (Finite (CFSG.CosetTable.PG 10 RuCz.czEps2Rels) ∧
      Nat.card (CFSG.CosetTable.PG 10 RuCz.czEps2Rels) ≤ 122880) ∧
    (Finite (CFSG.CosetTable.PG 10 RuCz.czEps3Rels) ∧
      Nat.card (CFSG.CosetTable.PG 10 RuCz.czEps3Rels) ≤ 122880) ∧
    ((CFSG.CosetTable.genSub {r : FreeGroup (Fin 10) | r ∈ RuCz.czRels.map FreeGroup.mk}
        RuCz.sub9).FiniteIndex ∧
      (CFSG.CosetTable.genSub {r : FreeGroup (Fin 10) | r ∈ RuCz.czRels.map FreeGroup.mk}
        RuCz.sub9).index ≤ 5) ∧
    (Finite (CFSG.CosetTable.PG RuCz.sub9.length RuCz.p12Rels) ∧
      Nat.card (CFSG.CosetTable.PG RuCz.sub9.length RuCz.p12Rels) ≤ 49152) ∧
    (∀ v ∈ RuCz.czRuRels, (∀ l ∈ v, l.1 < 7) ∧
      wordProd (CFSG.Sporadic.Bridge.VecSurj.img RuPi7.pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1) ∧
    ((CFSG.CosetTable.genSub {r : FreeGroup (Fin 7) | r ∈ RuPi7.pi7Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf 7 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (CFSG.CosetTable.genSub {r : FreeGroup (Fin 7) | r ∈ RuPi7.pi7Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf 7 [0, 1, 2, 3, 4, 5])).index ≤ 593775) :=
  ⟨KernelGMS78.W.czJRel_hold, KernelGMS78.Coset.card_J6, KernelGMS78.CzJ.cz_rigid,
    KernelGMS78.CzJ.cz_jident, KernelGMS78.W.c2Ru_hold, KernelGMS78.Coset.card_eps1,
    KernelGMS78.Coset.card_eps2, KernelGMS78.Coset.card_eps3, KernelGMS78.Coset.pi0_index,
    KernelGMS78.Coset.card_P12, KernelGMS78.W.czRu_hold, KernelGMS78.Coset.pi7m1_index⟩

end Certificates
