module

public import CFSG.RankThree.PartOne.K133B.NC5Cover
public import CFSG.RankThree.PartOne.Q1327S.Center
public import CFSG.RankThree.PartOne.Census3.NativeForm
public import CFSG.RankThree.PartOne.KF.F128SU
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.Blueprint TauCeti Subgroup CFSG.RankThree.PartOne.N143
open CFSG.Assembly.LowTwoRank CFSG.Models

theorem five_center_alternating {Q : Type} [Group Q] [Finite Q] (hq : IsQuasisimple Q)
    (hdvd : 5 ∣ Nat.card (center Q))
    (h5 : Census3.ThmThreeItem5 (Q ⧸ center Q)) : False := by
  obtain ⟨n, hn5, hn12, ⟨e⟩⟩ := h5
  have : Group.IsPerfect Q := hq.1
  exact Mult.alternating_center_small_primes (K := Q) hn5 e Nat.prime_five (by norm_num) hdvd

section Sporadic

theorem five_center_sporadic {Q : Type} [Group Q] [Finite Q] (hq : IsQuasisimple Q)
    (hZ5 : IsPGroup 5 (center Q)) (hdvd : 5 ∣ Nat.card (center Q))
    (h6 : Census3.ThmThreeItem6 (Q ⧸ center Q)) : False := by
  obtain ⟨s, hs, ⟨e0⟩⟩ := h6
  have hsimple : IsSimpleGroup (Q ⧸ center Q) := hq.2.1
  have : IsSimpleGroup (CFSGIndex.sporadic s).Group := e0.symm.isSimpleGroup
  obtain ⟨e1⟩ := Census3.nonempty_carrier_mulEquiv_of_mem hs
  let e : Q ⧸ center Q ≃* NativeSporadic.Carrier s := e0.trans e1.symm
  have hZ := Q1327S.center_eq_bot_of_sporadic hq hs e Nat.prime_five (le_refl 5) hZ5
  rw [hZ, Subgroup.card_bot] at hdvd
  omega


theorem five_dvd_center_cases (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q]
    [Finite Q] (hq : IsQuasisimple Q) (hZ5 : IsPGroup 5 (center Q))
    (hdvd : 5 ∣ Nat.card (center Q)) (hList : Census3.TheoremThreeList (Q ⧸ center Q)) :
    ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel (Q ⧸ center Q) .PSU 5 2 f ∧
      Nat.card (center Q) = 5 := by
  have hGA' : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels := hGA
  have hcov : ∀ {d : LieTypeIndex}, Census3.IsoLie (Q ⧸ center Q) d → PrimeCoverLieIndex 5 d := by
    rintro d ⟨hv, ⟨e⟩⟩
    exact primeCoverLie_five hGA' ⟨d, hv⟩ hq e hdvd
  rcases hList with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · obtain ⟨q, -, -, hd⟩ := h1
    have := (hcov hd).1
    omega
  · obtain ⟨q, -, -, hd | hd⟩ := h2
    · have := (hcov hd).1
      omega
    · have := (hcov hd).1
      omega
  · exact (hcov h3).elim
  · obtain ⟨q, -, -, hd | hd | hd | hd⟩ := h4
    · exact (hcov hd).elim
    · exact (hcov hd).elim
    · have := (hcov hd).1
      omega
    · have := (hcov hd).1
      omega
  · exact (five_center_alternating hq hdvd h5).elim
  · exact (five_center_sporadic hq hZ5 hdvd h6).elim
  · rcases h7 with ⟨q, -, hd⟩ | ⟨m, hd⟩ | ⟨q, hq2, hd | hd | hd | hd | hd | hd | hd⟩ | ⟨m, hd⟩ | hd
    · have := (hcov hd).1
      omega
    · exact (hcov hd).elim
    · have := (hcov hd).1
      omega
    · have := (hcov hd).1
      omega
    · exact (hcov hd).elim
    · exact (hcov hd).elim
    · have := (hcov hd).1
      omega
    ·
      obtain ⟨hv, ⟨e0⟩⟩ := hd
      have hmod : StatedClassicalModel (Q ⧸ center Q) .PSU 5 2 q.exponent := by
        have := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 q hv e0
        rw [hq2] at this
        exact this
      have hdvd' : Nat.card (center Q) ∣
          CFSG.RankThree.PartTwo.Sec4.Census.tableOrder .PSU 5 2 q.exponent :=
        CFSG.RankThree.PartTwo.Sec4.Census.card_center_dvd_tableOrder hGA' hq (MulEquiv.refl _)
          (CFSG.RankThree.PartTwo.Sec4.Census.lieModel_of_statedClassicalModel hmod)
      have htab : CFSG.RankThree.PartTwo.Sec4.Census.tableOrder .PSU 5 2 q.exponent =
          Nat.gcd 5 (2 ^ q.exponent + 1) := by
        have := exceptionalOrders_psu (n := 5) (f := q.exponent)
          (Or.inl ⟨by norm_num, by norm_num⟩)
        simp [CFSG.RankThree.PartTwo.Sec4.Census.tableOrder, this,
          CFSG.Blueprint.Multiplier.genericOrders]
      rw [htab] at hdvd'
      exact ⟨q.exponent, q.exponent_pos, hmod,
        Nat.dvd_antisymm (hdvd'.trans (Nat.gcd_dvd_left 5 _)) hdvd⟩
    · exact (hcov hd).elim
    · exact (hcov hd).elim
    · exact (hcov hd).elim
  · obtain ⟨q, -, hd | hd | hd⟩ := h8
    · have := (hcov hd).1
      omega
    · exact (hcov hd).elim
    · exact (hcov hd).elim
  · obtain ⟨q, hq2, hq1, hd | hd | hd | hd | hd | hd | hd⟩ := h9
    · have h4 := (hcov hd).2
      have hcard : q.card = 2 := by simp [PrimePower.card_def, hq2, hq1]
      rw [hcard] at h4
      omega
    · have := (hcov hd).1
      omega
    · have := (hcov hd).1
      omega
    · have := (hcov hd).1
      omega
    · exact (hcov hd).elim
    · exact (hcov hd).elim
    · exact (hcov hd).elim

end Sporadic

end CFSG.RankThree.PartOne.K133B
