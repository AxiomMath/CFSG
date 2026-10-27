module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS
open Proof1514

variable {G : Type} [Group G] [Finite G]

namespace Proof1514

theorem not_isoLThreePi_of_j2 {X : Type} [Group X] (φ : X ≃* CFSG.Blueprint.NativeSporadic.J2)
    {p e : ℕ} [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e := by
  rintro (⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩)
  · exact KFacts.KS14.ks17J2NotList.1 p e (Or.inl ⟨h1, ⟨φ.symm.trans f⟩⟩)
  · exact KFacts.KS14.ks17J2NotList.1 p e (Or.inr ⟨h2, ⟨φ.symm.trans f⟩⟩)

end Proof1514

omit [Finite G] in
theorem Ctx1514.not_j2 {A : Subgroup G} {LB : Subgroup G → Subgroup G} {c : G}
    {L Y : Subgroup G} (hctx : Ctx1514 A LB c L Y) :
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  obtain ⟨p, e, hp, -, hiso, -⟩ := hctx.concl1515
  exact ⟨fun φ => not_isoLThreePi_of_j2 φ hiso⟩

theorem rank3II_15_15_HJ_of
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (h131 : Item131) (h156 : Item156 A (lB A)) (hHJL : Step1515HJList) (hHJ : Step1515HJ) :
    Step1515 A (lB A) c L := by
  intro Y hY hm hce
  have hD := h.toSec13Data
  obtain ⟨φJ⟩ := hJ
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
    ⟨-, -, -, hcase⟩ | ⟨-, -, hMJ, -⟩ | ⟨-, hPGL, -, -⟩ | ⟨hcL, -⟩
  · exfalso
    rcases hcase with ⟨⟨p, e, hp, -, hiso⟩, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact not_isoLThreePi_of_j2 φJ hiso
    · exact KFacts.KS14.ks17J2NotList.2.1.false (φJ.symm.trans φ)
    · exact KFacts.KS14.ks17J2NotList.2.2.false (φJ.symm.trans φ)
  · rcases hMJ with hψ | hψ
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, -, ⟨χ⟩⟩ := facts_of_prod hD hM12p hM12z ψ
      exact ((isEmpty_mulEquiv_M12_of_J2 φJ).false χ).elim
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, hprod, -⟩ := facts_of_prod hD hJ2p hJ2z ψ
      rcases hHJL G A c L h ⟨φJ⟩ Y hY hm with h5 | h6 | hON | ⟨hYL, hLY⟩
      · exact ((h156 Y hY).1.false h5.some).elim
      · exact ((h156 Y hY).2.1 h6).elim
      · exact ((h156 Y hY).2.2 hON).elim
      · exact (hce (Or.inl ⟨hYL, hLY, hHJ G A c L h ⟨φJ⟩ Y hY hm hYL hLY, hprod,
          isEmpty_mulEquiv_M12_of_J2 φJ⟩)).elim
  · exfalso
    obtain ⟨⟨p, e, hp, -, hiso⟩, -, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
    exact not_isoLThreePi_of_j2 φJ hiso
  · exact (h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA hcL).elim

theorem item1514HJR_of
    (h131 : Item131) (h156 : Item156R)
    (hHJL : Step1515HJList) (hHJ : Step1515HJ) : Item1514HJR :=
  fun G _ _ A c L h hJ => rank3II_15_14_of_steps
    (rank3II_15_15_HJ_of h hJ h131 (h156 G A c L h) hHJL hHJ)
    (fun _ hctx => (hctx.not_j2.false hJ.some).elim)
    (fun _ hctx _ _ _ _ _ => (hctx.not_j2.false hJ.some).elim)
    (fun _ hctx _ _ _ => (hctx.not_j2.false hJ.some).elim)

end CFSG.RankThree.PartTwo.Sec15
