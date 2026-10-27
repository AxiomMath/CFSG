module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCoverWide
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResCenter
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.AltTriple
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.SporData
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3Model
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3ResSL3Rep
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup TauCeti
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

private theorem false_of_pRank_three_of_abelian_bound {K : Type} [Group K] [Finite K]
    (hb : ∀ A : Subgroup K, IsPGroup 3 A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      Nat.card A ≤ 9)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 3) : False := by
  obtain ⟨E, -, hE, hc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup K)
  rw [hrk] at hc
  have h9 := hb E (IsPGroup.of_card hc)
    (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  rw [hc] at h9
  norm_num at h9

section Certificates


theorem k34odd_threeCover_of_three_dvd
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    (L : Type) [Group L] [Finite L] (hq : CFSG.Open.IsQuasisimple L)
    (hcat : CFSG.Open.IsCatalogGroup (L ⧸ center L)) (h3 : 3 ∣ Nat.card (center L))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3) :
    ThreeCover (fun Y _ => IsSpor Y .ONan) L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcore : CFSG.pCore 3 L ≠ ⊥ := by
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L)) 3 h3
    have hzo : orderOf (z : L) = 3 := by rw [Subgroup.orderOf_coe, hz]
    have hle : Subgroup.zpowers (z : L) ≤ CFSG.pCore 3 L :=
      le_sSup ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2),
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])⟩
    intro hbot
    rw [hbot] at hle
    have h1 : (z : L) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
    rw [h1, orderOf_one] at hzo
    exact absurd hzo (by norm_num)
  let N : Subgroup L := GL83.I243.Cover.primeCentre 3 L
  have hqN : CFSG.Open.IsQuasisimple (L ⧸ N) := GL83.I243.Cover.isQuasisimple_quotient hq
  have hcatN : CFSG.Open.IsCatalogGroup ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N)) := by
    obtain ⟨e⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hq
    obtain ⟨i, ⟨f⟩⟩ := hcat
    exact ⟨i, ⟨e.trans f⟩⟩
  have hneN : Subgroup.center (L ⧸ N) ≠ ⊥ := GL83.I243.Cover.center_quotient_ne_bot hq hcore
  have hZpN : IsPGroup 3 (Subgroup.center (L ⧸ N)) :=
    GL83.I243.Cover.isPGroup_center_quotient hq
  have hNc : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      GL83.I243.Cover.coprime_card_primeCentre
  have hrkN : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ N)) = 3 :=
    (CFSG.SectionRank.pRank_quotient_eq N hNc).trans hrk
  obtain ⟨hcyc, hZ3⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.bal3ThreeCenter_of_tables
      hGA hAlt hSpor (L ⧸ N) hqN hcatN hneN hZpN hrkN.le
  open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.TripleCover in
  rcases kFactAlphaListM3Wide_of_tables hGA hSpor (L ⧸ N) hqN hcatN hneN hZpN hcyc hrkN.le with
    he6 | he7 | heM | heO | ⟨d, hd, heL⟩
  ·
    obtain ⟨e6⟩ := he6
    have hb :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.altTripleCoverAbelianBound_holds
        (L ⧸ N) hqN hZ3 ⟨6, by norm_num, ⟨e6⟩⟩
    exact (false_of_pRank_three_of_abelian_bound hb hrkN).elim
  ·
    obtain ⟨e7⟩ := he7
    have hb :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.altTripleCoverAbelianBound_holds
        (L ⧸ N) hqN hZ3 ⟨7, by norm_num, ⟨e7⟩⟩
    exact (false_of_pRank_three_of_abelian_bound hb hrkN).elim
  ·
    obtain ⟨eM⟩ := heM
    have hb :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.abelian_three_card_le_nine_hatM22
        hqN.1 hZ3 eM
    exact (false_of_pRank_three_of_abelian_bound hb hrkN).elim
  ·
    obtain ⟨eO⟩ := heO
    obtain ⟨c⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hq
    have hL : CFSG.IsQuasisimple L :=
      ⟨⟨hq.1⟩, hq.2,
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq⟩
    have hdvd : Nat.card (Subgroup.center L) ∣ 3 :=
      GL83.I243.CoverList.card_center_dvd_sporadic hSpor hL (c.symm.trans eO)
    have hZ3' : Nat.card (Subgroup.center L) = 3 := Nat.dvd_antisymm hdvd h3
    obtain ⟨φ⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
    exact ⟨hq, hZ3', ⟨(c.symm.trans eO).trans φ.symm⟩⟩
  ·
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ N)) ≤ 2 :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.pRank_le_two_of_isSLThreePi
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.isSLThreePi_of_cover
          hGA hqN hZ3 ⟨d, hd, heL⟩)
    omega

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
