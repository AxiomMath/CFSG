module

public import CFSG.RankThree.GF2n.Tim79aCitedInvol
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSporTools
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv
public import CFSG.Sporadic.FischerOddCore.Fi22FiveExact
public import CFSG.Sporadic.FischerOddCore.Fi22LocalComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23NonsolvCent
public import CFSG.Sporadic.Fi23.Simple
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeC
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.GlueO23
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ReifartTransport

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Subgroup CFSG.Blueprint

theorem fi22InvolutionCentralizerStatement_holds :
    Fi22InvolutionCentralizerStatement := by
  intro G _ _ hG t ht
  obtain ⟨e₀⟩ := hG
  let e : G ≃* ↥CFSG.Monster.B.Fischer.fi22P := e₀.trans CFSG.Monster.B.Fischer.fi22PermEquiv
  rw [← CFSG.Sporadic.FischerOddCore.card_centralizer_mulEquiv e t]
  set q : ↥CFSG.Monster.B.Fischer.fi22P := e t with hqdef
  have hq : orderOf q = 2 := by rw [hqdef, MulEquiv.orderOf_eq]; exact ht
  have hτ : orderOf (q : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hq
  obtain ⟨k, hk, r, hr, hrτ⟩ := CFSG.Sporadic.FischerOddCore.fi22R_involution_conj
    (CFSG.Monster.B.Fischer.fi22P_le_R q.2) hτ
  have hrn := CFSG.Monster.B.Fischer.fi22R_le_normalizer hr
  have hkP : CFSG.Sporadic.FischerOddCore.fi22ExtRep k ∈ CFSG.Monster.B.Fischer.fi22P := by
    rw [← hrτ]
    exact (Subgroup.mem_normalizer_iff.1 hrn _).1 q.2
  have hk3 : k < 3 := by
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    exact (CFSG.Sporadic.FischerOddCore.CTUC_Fi22_all_extension_involutions_covered.2.1 j
      (by omega)).2 hkP
  rw [CFSG.LocalAnalysis.EvenBN.Tits.R2.card_centralizer_subgroup, Nat.card_congr
    (CFSG.Sporadic.FischerOddCore.fi22CP_conj_equiv hrn _).toEquiv, hrτ]
  obtain ⟨h0, h1, -, -, -, hlist⟩ :=
    CFSG.Sporadic.FischerOddCore.CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · rw [h0, CFSG.Sporadic.FischerOddCore.card_fi22H_zero]
    exact Or.inr (Or.inr rfl)
  · have hc1 : Nat.card ↥(CFSG.Sporadic.FischerOddCore.fi22H 1) = 53084160 := by
      have := congrArg (fun l : List ℕ => l.getD 1 0) hlist
      simpa using this
    rw [h1, hc1]
    exact Or.inr (Or.inl rfl)
  · rw [CFSG.Sporadic.FischerOddCore.fi22ExtRep_two,
      Nat.card_congr CFSG.Sporadic.FischerOddCore.fi22CPzEquiv.toEquiv,
      CFSG.LocalAnalysis.EvenBN.Tits.R2.card_centralizer_of_isConj
        CFSG.Sporadic.FischerOddCore.isConj_fi22OuterZP_fi22Ya,
      CFSG.Sporadic.FischerOddCore.card_centralizer_fi22Ya]
    exact Or.inl rfl

end CFSG.RankThree.GF2n.Tim79a
