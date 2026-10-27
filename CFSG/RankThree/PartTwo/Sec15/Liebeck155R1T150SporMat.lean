module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
public import Certificates.Certificate13511
public import Certificates.Certificate13512
public import Certificates.Certificate13513
public import Certificates.Certificate13514
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard
import CFSG.RankThree.GF2n.Stroth80.Sec93OutSmall
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.Sporadic.Schreier.PairHSFaithful
public import CFSG.Sporadic.Schreier.PairJ2CertBase

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.Coordinator.B3S3 (Data check check_card_sound check_valid
  m22S3Data m23S3Data m24S3Data j2S3Data hsS3Data)
open CFSG.HardMathSupport.Solomon.Coordinator (rep_m22A rep_m22B rep_m23A rep_m23B rep_m24A
  rep_m24B)

theorem k150s_goodFor_of_check {J : Type} [Group J] (hJ : K150sTgt J) (D : Data)
    {A B : Equiv.Perm (Fin D.n)} (hA : CFSG.Monster.B.Co2.Rep D.n D.A A)
    (hB : CFSG.Monster.B.Co2.Rep D.n D.B B) (h : check D = true)
    (hcases : ∀ c < D.cases.size,
      ¬ 2520 ∣ D.cases[c]!.card ∧ ¬ 443520 ∣ D.cases[c]!.card) :
    ∀ x ∈ Subgroup.closure {A, B}, orderOf x = 3 →
      GoodFor J (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin D.n))) ⊓
        Subgroup.closure {A, B}) := by
  intro x hx hx3
  obtain ⟨c, hc, hcard⟩ := check_card_sound D hA hB h x hx hx3
  refine k150s_goodFor_of_not_dvd (hJ.not_dvd ?_ ?_)
  · rw [hcard]
    exact (hcases c hc).1
  · rw [hcard]
    exact (hcases c hc).2

theorem k150s_m24 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .M24) := by
  refine k150s_row_of_native CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  refine k150s_noCfg_of_subgroupModel (P := Blueprint.NativeSporadic.M24) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_le_two
      (CFSG.RankThree.GF2n.Stroth80.card_outer_le_two_m24 e)) ?_
  exact k150s_goodFor_of_check hJ m24S3Data rep_m24A rep_m24B
    Certificates.certificate13512 (by decide +kernel)

theorem k150s_m22 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .M22) := by
  refine k150s_row_of_native CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  refine k150s_noCfg_of_subgroupModel (P := Blueprint.NativeSporadic.M22) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_le_two
      (CFSG.RankThree.GF2n.Stroth80.card_outer_le_two_m22 e)) ?_
  exact k150s_goodFor_of_check hJ m22S3Data rep_m22A rep_m22B
    Certificates.certificate13511.2.2.1 (by decide +kernel)

theorem k150s_m23 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .M23) := by
  refine k150s_row_of_native CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  refine k150s_noCfg_of_subgroupModel (P := Blueprint.NativeSporadic.M23) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_le_two
      (CFSG.RankThree.GF2n.Stroth80.card_outer_le_two_m23 e)) ?_
  exact k150s_goodFor_of_check hJ m23S3Data rep_m23A rep_m23B
    Certificates.certificate13511.2.2.2 (by decide +kernel)

theorem k150s_j2 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .J2) := by
  refine k150s_row_of_native CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  have : Finite (Blueprint.NativeSporadic.Carrier .J2) := Finite.of_equiv S e.toEquiv
  have h := Certificates.certificate13513
  obtain ⟨hvA, hvB⟩ := check_valid h
  refine k150s_noCfg_of_subgroupModel (P := CFSG.Sporadic.Schreier.j2P)
    (e.trans CFSG.Sporadic.Schreier.j2PermEquiv) (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e
      (RonanK429H.not_three_dvd_outer_of_le_two card_outer_J2)) ?_
  exact k150s_goodFor_of_check hJ j2S3Data (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) h (by decide +kernel)

theorem k150s_hs {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .HS) := by
  refine k150s_row_of_native CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  have : Finite (Blueprint.NativeSporadic.Carrier .HS) := Finite.of_equiv S e.toEquiv
  have h := Certificates.certificate13514
  obtain ⟨hvA, hvB⟩ := check_valid h
  refine k150s_noCfg_of_subgroupModel (P := CFSG.Sporadic.Schreier.hsP)
    (e.trans CFSG.Sporadic.Schreier.hsPermEquiv) (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e
      (RonanK429H.not_three_dvd_outer_of_le_two card_outer_HS)) ?_
  exact k150s_goodFor_of_check hJ hsS3Data (CFSG.RankThree.Native.rep_of_validA hvA)
    (CFSG.RankThree.Native.rep_of_validA hvB) h (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
