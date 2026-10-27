module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsFp
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Bridge.HNSurj
public import CFSG.Sporadic.Bridge.ONSurj
public import Certificates.Certificate8089
public import Certificates.Certificate8090
public import Certificates.Certificate8091
public import Certificates.Certificate8092
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native TauCeti
open CFSG.Assembly.RankThreeEven (localRank)

section Suz

theorem suzW3_check : W4Data.check (ops3 64) suzW3 = true :=
  Certificates.certificate8089

theorem three_le_localRank_nativeSuz [Finite NativeSporadic.Suz] :
    3 ≤ localRank 3 NativeSporadic.Suz := by
  obtain ⟨t, E, ht, hE, hc, hEt⟩ := OpsSpec.exists_of_w4Check (spec3 64) suzW3 suzW3_check
  exact le_localRank_of_commute_involution Nat.prime_three ht hE hc hEt

theorem three_le_localRank_Suz [Finite (CFSGIndex.sporadic .Suz).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .Suz).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have : Finite SporadicName.Suz.Group := ‹Finite (CFSGIndex.sporadic .Suz).Group›
  have : Finite NativeSporadic.Suz := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.Suz = localRank 3 (CFSGIndex.sporadic .Suz).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeSuz
  omega

end Suz

section Ly

theorem lyW3_check : W4Data.check (opsP 5 111) lyW3 = true :=
  Certificates.certificate8090

theorem three_le_localRank_nativeLy [Finite NativeSporadic.Ly] :
    3 ≤ localRank 3 NativeSporadic.Ly := by
  obtain ⟨t, E, ht, hE, hc, hEt⟩ := OpsSpec.exists_of_w4Check (specP 5 111) lyW3 lyW3_check
  exact le_localRank_of_commute_involution Nat.prime_three ht hE hc hEt

theorem three_le_localRank_Ly [Finite (CFSGIndex.sporadic .Ly).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .Ly).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv
  have : Finite SporadicName.Ly.Group := ‹Finite (CFSGIndex.sporadic .Ly).Group›
  have : Finite NativeSporadic.Ly := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.Ly = localRank 3 (CFSGIndex.sporadic .Ly).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeLy
  omega

end Ly

section HN

theorem hnV4_check : V4Data.check (opsP 5 133) hnV4 = true :=
  Certificates.certificate8091

theorem three_le_localRank_nativeHN [Finite NativeSporadic.HN] :
    3 ≤ localRank 3 NativeSporadic.HN :=
  OpsSpec.le_localRank_three_of_v4Check (specP 5 133) hnV4 hnV4_check

theorem three_le_localRank_HN [Finite (CFSGIndex.sporadic .HN).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .HN).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have : Finite SporadicName.HN.Group := ‹Finite (CFSGIndex.sporadic .HN).Group›
  have : Finite NativeSporadic.HN := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.HN = localRank 3 (CFSGIndex.sporadic .HN).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeHN
  omega

end HN

section ON

theorem onV4_check : V4Data.check (ops3 154) onV4 = true :=
  Certificates.certificate8092

theorem three_le_localRank_nativeON [Finite NativeSporadic.ON] :
    3 ≤ localRank 3 NativeSporadic.ON :=
  OpsSpec.le_localRank_three_of_v4Check (spec3 154) onV4 onV4_check

theorem three_le_localRank_ONan [Finite (CFSGIndex.sporadic .ONan).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic .ONan).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have : Finite SporadicName.ONan.Group := ‹Finite (CFSGIndex.sporadic .ONan).Group›
  have : Finite NativeSporadic.ON := Finite.of_equiv _ e.symm.toEquiv
  have h : localRank 3 NativeSporadic.ON = localRank 3 (CFSGIndex.sporadic .ONan).Group :=
    @localRank_eq_of_mulEquiv _ _ Units.instGroup _ _ _ e _ Nat.prime_three
  have h3 := three_le_localRank_nativeON
  omega

end ON

section Odd

theorem three_le_localRank_of_mem_odd (s : SporadicName) (hs : s ∈ [.Ly, .Suz, .ONan, .HN])
    [Finite (CFSGIndex.sporadic s).Group] :
    3 ≤ localRank 3 (CFSGIndex.sporadic s).Group := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact three_le_localRank_Ly
  · exact three_le_localRank_Suz
  · exact three_le_localRank_ONan
  · exact three_le_localRank_HN

end Odd

end CFSG.RankThree.PartTwo.Census
