module

public import CFSG.OddTranspositions.TheoremTwo.QCentral.StepOne
public import CFSG.OddTranspositions.TheoremTwo.QCentral.PairStep
public import CFSG.OddTranspositions.TheoremTwo.ThirdKindExclusion
public import CFSG.OddTranspositions.FiveThreeQZ
public import CFSG.OddTranspositions.PartThree.EightFive.QNotCentralCore
public import CFSG.OddTranspositions.DeltaCentSet

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

theorem qCentralStatement_holds : QCentralStatement := by
  intro G _ _ D hC hrad hL w v n htri hn hn1 hord hv hB
  by_contra hQ
  have hS := hC.setup
  have hfaith := QZ.faithfulOnBlocks_of_localSecond hC hrad hL
  have hfirst := no_firstKind_of_H' hC fun x y t hx hy ht htri' h1 => by
    have h4 := DalphaStar_triangles_of_localSecond hC hL x hx y hy t ht htri'
    rw [h4] at h1
    exact absurd h1.1 (by decide)
  have h1 := exists_pCore_conj_ne hS hL htri hn hord hQ
  have htr := thirdK_transitive hS hL htri hn hord
  rw [Delta_eq_centSet, thirdK_eq_localGroup] at htr
  rw [thirdK_eq_localGroup] at h1
  have hB' : CFSG.BenderSuzuki.IsBenderGroup (localGroup D ((hC.d * v * w) ^ n) ⧸
      CFSG.solvableRadical (localGroup D ((hC.d * v * w) ^ n))) := by
    have key : ∀ K : Subgroup G, K = localGroup D ((hC.d * v * w) ^ n) →
        CFSG.BenderSuzuki.IsBenderGroup (K ⧸ CFSG.solvableRadical K) →
        CFSG.BenderSuzuki.IsBenderGroup (localGroup D ((hC.d * v * w) ^ n) ⧸
          CFSG.solvableRadical (localGroup D ((hC.d * v * w) ^ n))) := by
      rintro K rfl h
      exact h
    exact key _ (thirdK_eq_localGroup _) hB
  obtain ⟨q, hq, haD, hane, hda⟩ := h1
  obtain ⟨c, htri2, m, hm, -, hordm⟩ :=
    exists_thirdKind_of_commute_d hC hfaith hfirst htri ⟨n, hn, hn1, hord⟩ hv haD hda hane.symm
  have htr2 := thirdK_transitive hS hL htri2 hm hordm
  rw [Delta_eq_centSet, thirdK_eq_localGroup] at htr2
  obtain ⟨r, hr, hrd, hrv, hrw⟩ :=
    exists_commute_of_thirdKind_conj_pCore hS htri hn hn1 hord rfl htr hB' hq rfl htri2 hm hordm
      rfl htr2
  have h4 := hL r hr hC.d w v hrd.symm hrw.symm hrv.symm htri
  rw [hord] at h4
  obtain rfl : n = 2 := by omega
  exact absurd hn (by decide)

end CFSG.OddTranspositions

end

