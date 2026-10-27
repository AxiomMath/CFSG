module

public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Fi23
import Certificates.Kernel.Fi23U3.Lower
import Certificates.Kernel.Fi23U3.HAct
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound

public section

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

namespace Certificates

open CertificateChecks

instance fi23U3Cover3_neZero : NeZero fi23U3Cover3.m := ⟨by decide⟩

end Certificates

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary in
theorem certificate291381 :
    (∃ g : Fin fi23U3Cover3.m →
        (CFSG.Blueprint.NativeSporadic.seedMonoid 3 253 1 fi23U3Cover3.seedA fi23U3Cover3.seedB)ˣ,
      (∀ r ∈ fi23U3Cover3.rels, FreeGroup.lift g (FreeGroup.mk r) = 1) ∧ (∀ i, g i ^ 2 = 1) ∧
      6377292 ≤ Nat.card (Subgroup.closure (Set.range g))) ∧
    (Finite (PG fi23U3Cover3.m fi23U3Cover3.cover) ∧
      Nat.card (PG fi23U3Cover3.m fi23U3Cover3.cover) ≤ 6377292) :=
  ⟨KernelFi23U3.lower_facts, CFSG.KD.Fi23H.card_fiPC⟩

end Certificates
