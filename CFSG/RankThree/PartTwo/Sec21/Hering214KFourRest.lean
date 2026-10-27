module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KFourCert
public import CFSG.RankThree.PartTwo.Sec21.Hering214KSporRest
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import Certificates.Certificate799200
public import Certificates.Certificate799201
public import Certificates.Certificate799202

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native

theorem fourFacts_he : Four27Facts FourHe.cert 13 14 17 18 19 20 22 23 25 26 28 29 31 :=
  ⟨⟨0, ⟨mem_facts 0 rfl, mem_facts 1 rfl, mem_facts 2 rfl, mem_facts 3 rfl, mem_facts 4 rfl⟩⟩,
    mem_facts 5 rfl, mem_facts 6 rfl, mem_facts 7 rfl, mem_facts 8 rfl, mem_facts 9 rfl,
    mem_facts 10 rfl,
    ⟨mem_facts 11 rfl, mem_facts 12 rfl, mem_facts 13 rfl, ⟨0, mem_facts 14 rfl⟩,
      ⟨0, mem_facts 15 rfl⟩, ⟨0, mem_facts 16 rfl⟩, ⟨1, 1, by decide, by decide, mem_facts 17 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 18 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 19 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 20 rfl⟩, Or.inl ⟨0, mem_facts 21 rfl⟩⟩,
    ⟨mem_facts 22 rfl, mem_facts 23 rfl, mem_facts 24 rfl, ⟨0, mem_facts 25 rfl⟩,
      ⟨0, mem_facts 26 rfl⟩, ⟨0, mem_facts 27 rfl⟩, ⟨1, 0, by decide, by decide, mem_facts 28 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 29 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 30 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 31 rfl⟩, Or.inr ⟨0, mem_facts 32 rfl⟩⟩,
    ⟨mem_facts 33 rfl, mem_facts 34 rfl, mem_facts 35 rfl, ⟨0, mem_facts 36 rfl⟩,
      ⟨0, mem_facts 37 rfl⟩, ⟨0, mem_facts 38 rfl⟩, ⟨1, 0, by decide, by decide, mem_facts 39 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 40 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 41 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 42 rfl⟩, Or.inr ⟨0, mem_facts 43 rfl⟩⟩,
    ⟨mem_facts 44 rfl, mem_facts 45 rfl, mem_facts 46 rfl, ⟨0, mem_facts 47 rfl⟩,
      ⟨0, mem_facts 48 rfl⟩, ⟨0, mem_facts 49 rfl⟩, ⟨1, 1, by decide, by decide, mem_facts 50 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 51 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 52 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 53 rfl⟩, Or.inl ⟨0, mem_facts 54 rfl⟩⟩⟩

theorem fourData27_he : FourData27 NativeSporadic.He :=
  fourFacts_he.fourData27 (specP 7 50) Certificates.certificate799200

theorem fourFacts_j2 : Four27Facts FourJ2.cert 5 6 9 10 11 12 14 15 17 18 20 21 23 :=
  ⟨⟨0, ⟨mem_facts 0 rfl, mem_facts 1 rfl, mem_facts 2 rfl, mem_facts 3 rfl, mem_facts 4 rfl⟩⟩,
    mem_facts 5 rfl, mem_facts 6 rfl, mem_facts 7 rfl, mem_facts 8 rfl, mem_facts 9 rfl,
    mem_facts 10 rfl,
    ⟨mem_facts 11 rfl, mem_facts 12 rfl, mem_facts 13 rfl, ⟨0, mem_facts 14 rfl⟩,
      ⟨0, mem_facts 15 rfl⟩, ⟨0, mem_facts 16 rfl⟩, ⟨1, 0, by decide, by decide, mem_facts 17 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 18 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 19 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 20 rfl⟩, Or.inr ⟨0, mem_facts 21 rfl⟩⟩,
    ⟨mem_facts 22 rfl, mem_facts 23 rfl, mem_facts 24 rfl, ⟨0, mem_facts 25 rfl⟩,
      ⟨0, mem_facts 26 rfl⟩, ⟨0, mem_facts 27 rfl⟩, ⟨1, 0, by decide, by decide, mem_facts 28 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 29 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 30 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 31 rfl⟩, Or.inr ⟨0, mem_facts 32 rfl⟩⟩,
    ⟨mem_facts 33 rfl, mem_facts 34 rfl, mem_facts 35 rfl, ⟨0, mem_facts 36 rfl⟩,
      ⟨0, mem_facts 37 rfl⟩, ⟨0, mem_facts 38 rfl⟩, ⟨0, 1, by decide, by decide, mem_facts 39 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 40 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 41 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 42 rfl⟩, Or.inl ⟨0, mem_facts 43 rfl⟩⟩,
    ⟨mem_facts 44 rfl, mem_facts 45 rfl, mem_facts 46 rfl, ⟨0, mem_facts 47 rfl⟩,
      ⟨0, mem_facts 48 rfl⟩, ⟨0, mem_facts 49 rfl⟩, ⟨1, 1, by decide, by decide, mem_facts 50 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 51 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 52 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 53 rfl⟩, Or.inl ⟨0, mem_facts 54 rfl⟩⟩⟩

theorem fourData27_j2 : FourData27 NativeSporadic.J2 :=
  fourFacts_j2.fourData27 (specP 5 14) Certificates.certificate799201

theorem fourFacts_ru : Four27Facts FourRu.cert 7 8 11 12 13 14 16 17 19 20 22 23 25 :=
  ⟨⟨0, ⟨mem_facts 0 rfl, mem_facts 1 rfl, mem_facts 2 rfl, mem_facts 3 rfl, mem_facts 4 rfl⟩⟩,
    mem_facts 5 rfl, mem_facts 6 rfl, mem_facts 7 rfl, mem_facts 8 rfl, mem_facts 9 rfl,
    mem_facts 10 rfl,
    ⟨mem_facts 11 rfl, mem_facts 12 rfl, mem_facts 13 rfl, ⟨0, mem_facts 14 rfl⟩,
      ⟨0, mem_facts 15 rfl⟩, ⟨0, mem_facts 16 rfl⟩, ⟨0, 1, by decide, by decide, mem_facts 17 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 18 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 19 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 20 rfl⟩, Or.inl ⟨0, mem_facts 21 rfl⟩⟩,
    ⟨mem_facts 22 rfl, mem_facts 23 rfl, mem_facts 24 rfl, ⟨0, mem_facts 25 rfl⟩,
      ⟨0, mem_facts 26 rfl⟩, ⟨0, mem_facts 27 rfl⟩, ⟨1, 1, by decide, by decide, mem_facts 28 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 29 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 30 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 31 rfl⟩, Or.inl ⟨0, mem_facts 32 rfl⟩⟩,
    ⟨mem_facts 33 rfl, mem_facts 34 rfl, mem_facts 35 rfl, ⟨0, mem_facts 36 rfl⟩,
      ⟨0, mem_facts 37 rfl⟩, ⟨0, mem_facts 38 rfl⟩, ⟨1, 0, by decide, by decide, mem_facts 39 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 40 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 41 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 42 rfl⟩, Or.inr ⟨0, mem_facts 43 rfl⟩⟩,
    ⟨mem_facts 44 rfl, mem_facts 45 rfl, mem_facts 46 rfl, ⟨0, mem_facts 47 rfl⟩,
      ⟨0, mem_facts 48 rfl⟩, ⟨0, mem_facts 49 rfl⟩, ⟨0, 1, by decide, by decide, mem_facts 50 rfl⟩,
      ⟨1, 1, by decide, by decide, mem_facts 51 rfl⟩,
      ⟨1, 0, by decide, by decide, mem_facts 52 rfl⟩,
      ⟨0, 1, by decide, by decide, mem_facts 53 rfl⟩, Or.inl ⟨0, mem_facts 54 rfl⟩⟩⟩

theorem fourData27_ru : FourData27 NativeSporadic.Ru :=
  fourFacts_ru.fourData27 (spec2fr 28) Certificates.certificate799202

theorem fourDataRest :
    FourDataRest :=
  ⟨fourData27_he, fourData27_j2, fourData27_ru⟩

end CFSG.RankThree.PartTwo.Sec21.Hering214
