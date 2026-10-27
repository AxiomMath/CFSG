module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeTorus
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Core

variable {D : Data G} {V₀ V L K₀ : Subgroup G}

theorem s15_Three_O1a_of_alt_core (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    (hperf : s15KNatPerf ↥(lBar V₀ V hV L) (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L))
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) 6 ∨ UC22.IsAlt ↥(lBar V₀ V hV L) 7 ∨
      IsLn ↥(lBar V₀ V hV L) 4 1)
    (hsig : D.sig = {3}) (hV0 : mSub V₀ ≤ 2) (hT : RTable137)
    (hAbs : RAbsIrr153) (hTor : RTorus3_153) (h1217 : R1217 D)
    (hrk : 3 ≤ CFSG.Open.pRank 3 D.M ∧
      CFSG.Open.pRank 3 D.M - 1 ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ∧
      CFSG.Open.pRank 3 (F11.CTilde D.M V₀ V) ≤ 1) :
    ∀ v ∈ V, v ∉ V₀ → 1 < CFSG.Open.pRank 3 (F11.CElt D.M V₀ v) := by
  intro v hv hv0
  obtain ⟨E, hEM, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 3) hrk.1
  obtain ⟨F, hFle, hFelem, hFcard⟩ :=
    s15_Three_O1a_of_torus hT hAbs hTor h1217 h hV hL hs hperf hrk.2.2 hEM hE
      (Or.inl ⟨hA, by rw [hEcard]; norm_num⟩) hv hv0
  have hcard : Nat.card F = 3 ^ 2 := by rw [hFcard]; norm_num
  have h2 : 2 ≤ CFSG.Open.pRank 3 (F11.CElt D.M V₀ v) :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hFle hFelem hcard
  omega

end Core

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
