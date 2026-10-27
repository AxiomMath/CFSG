module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8QA3A1A
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_cTilde_no_seven
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (h7 : 7 ∈ D.sig) :
    ¬ 7 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) := by
  have h7L : 7 ∣ Nat.card ↥(lBar ⊥ V h.hyp151.isElemAbelian L) := by
    obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hrow.1
    letI := hKf
    letI := hKfin
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKcard]
    norm_num
  intro h7C
  obtain ⟨x, hxM, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 (by rw [hs2]; norm_num)
  obtain ⟨E, hEM, hEab, hEbig⟩ := s16h_exists_Eb_of_dvd_cTil D h hcomp
    Nat.prime_seven (by norm_num) h7L h7C hxM hxn
  exact absurd (hbad 7 h7 E hEM hEab) (not_lt_of_ge hEbig)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
