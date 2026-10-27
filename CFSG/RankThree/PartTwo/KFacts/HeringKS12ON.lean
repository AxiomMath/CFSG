module

public import CFSG.RankThree.PartTwo.KFacts.HeringKS12Cert
public import Certificates.Certificate799020

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table

theorem ks12Facts_ON : KS12Facts KS12ON.cert 34 32 31 22 19 10 :=
  ⟨mem_facts 0 rfl, mem_facts 1 rfl, ⟨6, mem_facts 2 rfl⟩, ⟨2, mem_facts 3 rfl⟩,
    mem_facts 4 rfl, mem_facts 5 rfl, mem_facts 6 rfl, ⟨0, mem_facts 7 rfl⟩,
    ⟨0, mem_facts 8 rfl⟩, ⟨0, mem_facts 9 rfl⟩, ⟨0, mem_facts 10 rfl⟩, ⟨0, mem_facts 11 rfl⟩,
    mem_facts 12 rfl, mem_facts 13 rfl, mem_facts 14 rfl, mem_facts 15 rfl,
    ⟨0, 1, mem_facts 16 rfl⟩, ⟨1, 1, mem_facts 17 rfl⟩,
    ⟨1, 0, mem_facts 18 rfl⟩, ⟨0, 1, mem_facts 19 rfl⟩⟩

theorem ks12ConfigN_ON :
    KS12ConfigN Blueprint.NativeSporadic.ON :=
  KS12Facts.config (spec3 154) Certificates.certificate799020 ks12Facts_ON

theorem ks12CoverON : KS12CoverON := by
  intro X _ _ _ hZ ⟨e⟩
  have h : KS12ConfigN Blueprint.NativeSporadic.ON := ks12ConfigN_ON
  have h2 := @ks12Concl_of_configN X _ _ hZ Blueprint.NativeSporadic.ON _ e
  exact h2 h

end CFSG.RankThree.PartTwo.KFacts
