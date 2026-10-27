module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Cert
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import Certificates.Certificate799010

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table

theorem ks12Facts_J3 : KS12Facts KS12J3.cert 6 7 15 3 4 9 :=
  ⟨mem_facts 0 rfl, mem_facts 1 rfl, ⟨2, mem_facts 2 rfl⟩, ⟨8, mem_facts 3 rfl⟩,
    mem_facts 4 rfl, mem_facts 5 rfl, mem_facts 6 rfl, ⟨0, mem_facts 7 rfl⟩,
    ⟨0, mem_facts 8 rfl⟩, ⟨0, mem_facts 9 rfl⟩, ⟨0, mem_facts 10 rfl⟩, ⟨0, mem_facts 11 rfl⟩,
    mem_facts 12 rfl, mem_facts 13 rfl, mem_facts 14 rfl, mem_facts 15 rfl,
    ⟨0, 1, mem_facts 16 rfl⟩, ⟨1, 1, mem_facts 17 rfl⟩,
    ⟨0, 1, mem_facts 18 rfl⟩, ⟨1, 1, mem_facts 19 rfl⟩⟩

theorem ks12ConfigN_J3 :
    KS12ConfigN Blueprint.NativeSporadic.J3 :=
  KS12Facts.config (spec2fr 80) Certificates.certificate799010 ks12Facts_J3

theorem ks12CoverJ3 : KS12CoverJ3 := by
  intro X _ _ _ hZ ⟨e⟩
  have h : KS12ConfigN Blueprint.NativeSporadic.J3 := ks12ConfigN_J3
  have h2 := @ks12Concl_of_configN X _ _ hZ Blueprint.NativeSporadic.J3 _ e
  exact h2 h

end CFSG.RankThree.PartTwo.KFacts
