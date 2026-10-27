module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Bridge.Co3Surj
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Bridge.ThSurj
public import Certificates.Certificate8086
public import Certificates.Certificate8087
public import Certificates.Certificate8088
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native TauCeti
open CFSG.Assembly.RankThreeEven (localRank)

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem le_localRank_three_of_w4Check [Inhabited M] (D : W4Data)
    (h : W4Data.check O D = true)
    [Finite (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ] :
    D.base.outs.length ≤
      localRank 3 (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ := by
  obtain ⟨t, E, ht, hE, hc, hEt⟩ := exists_of_w4Check Sp D h
  exact le_localRank_of_commute_involution Nat.prime_three ht hE hc hEt

end OpsSpec

theorem co3W3_check : W4Data.check (ops2 22) co3W3 = true :=
  Certificates.certificate8086

theorem three_le_localRank_nativeCo3
    [Finite NativeSporadic.Co3] : 3 ≤ localRank 3 NativeSporadic.Co3 :=
  OpsSpec.le_localRank_three_of_w4Check (spec2 22) co3W3 co3W3_check

theorem three_le_localRank_Co3
    [Finite (CFSGIndex.sporadic .Co3).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .Co3).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  have : Finite SporadicName.Co3.Group := ‹Finite (CFSGIndex.sporadic .Co3).Group›
  have : Finite NativeSporadic.Co3 := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.Co3 = localRank 3 (CFSGIndex.sporadic .Co3).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeCo3
  omega

theorem co2W3_check : W4Data.check (ops2 22) co2W3 = true :=
  Certificates.certificate8087

theorem three_le_localRank_nativeCo2
    [Finite NativeSporadic.Co2] : 3 ≤ localRank 3 NativeSporadic.Co2 :=
  OpsSpec.le_localRank_three_of_w4Check (spec2 22) co2W3 co2W3_check

theorem three_le_localRank_Co2
    [Finite (CFSGIndex.sporadic .Co2).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .Co2).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have : Finite SporadicName.Co2.Group := ‹Finite (CFSGIndex.sporadic .Co2).Group›
  have : Finite NativeSporadic.Co2 := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.Co2 = localRank 3 (CFSGIndex.sporadic .Co2).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeCo2
  omega

theorem thW3_check : W4Data.check (ops2 248) thW3 = true :=
  Certificates.certificate8088

theorem three_le_localRank_nativeTh
    [Finite NativeSporadic.Th] : 3 ≤ localRank 3 NativeSporadic.Th :=
  OpsSpec.le_localRank_three_of_w4Check (spec2 248) thW3 thW3_check

theorem three_le_localRank_Th
    [Finite (CFSGIndex.sporadic .Th).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .Th).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  have : Finite SporadicName.Th.Group := ‹Finite (CFSGIndex.sporadic .Th).Group›
  have : Finite NativeSporadic.Th := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.Th = localRank 3 (CFSGIndex.sporadic .Th).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeTh
  omega

theorem three_le_localRank_of_mem_F2
    (s : SporadicName) (hs : s ∈ [.Co3, .Co2, .Th])
    [Finite (CFSGIndex.sporadic s).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic s).Group := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact three_le_localRank_Co3
  · exact three_le_localRank_Co2
  · exact three_le_localRank_Th

end CFSG.RankThree.PartTwo.Census
