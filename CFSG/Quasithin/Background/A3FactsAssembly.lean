module

public import CFSG.Quasithin.Background.A3FactsTrialityTwo
public import CFSG.Quasithin.Background.A3FactsSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native36
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native38
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3Native39
public import CFSG.Quasithin.Background.A129One
public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.EmptyFaithful.S1417Stab
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1416
public import CFSG.Quasithin.EmptyFaithful.S14111Alt
public import CFSG.Quasithin.Vol2.Ch1A3Cat

public section

namespace CFSG.Quasithin

namespace A3Facts

open CFSG.QuasithinUnique.Vol2Native (SQTKHypCat A36CoreForSQTKCat A37ForSQTKCat A38ForSQTKCat
  A39ForSQTKCat A134For a36CoreForSQTKCat_of_a129 a37ForSQTKCat_of_core a38_part3_of_package
  nonnormal_package_of_a134 a39_part1_of_outSolvable a39_part2_cat)

@[expose] def A134ForSQTK : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.SectionRank.IsSQTKCat H → A134For H

theorem a134ForSQTK_of_rankOneList
    (h : RankOneList) : A134ForSQTK :=
  fun _ _ _ hH => a134Concl_of_sqtk h hH

theorem a134ForSQTK
    : A134ForSQTK :=
  a134ForSQTK_of_rankOneList rankOneList

theorem a38ForSQTKCat_of_a134ForSQTK
    (ha134 : A134ForSQTK) (h36 : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) : A38ForSQTKCat := fun Q _ hQ => by
  have := hQ.finite
  have hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup Q) ≤ 2 :=
    fun q hq hq2 => hQ.rank_top hq hq2
  have h36Q := h36 Q hQ
  have h37Q := h37 Q hQ
  refine a38_part3_of_package h37Q fun L hL hnorm => ?_
  have hL36 := h36Q L hL
  exact nonnormal_package_of_a134 mult2Fact hrank (ha134 Q hQ.isSQTKCat) h37Q hL
    (hQ.pCore_two_of_subnormal (subnormal_of_mem_cComp hL)) hL36.1 hL36.2.2 hnorm

theorem a39_part1_of_schreierSQTK
    (hS : SchreierSQTK) {G : Type} [Group G] (hG : SQTKHypCat G)
    (h37 : A37Statement G) (h38 : A38Part3 G) :
    cCompSpan (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) := by
  have := hG.finite
  have hqK : CFSG.SectionRank.IsKGroupCat (G ⧸ CFSG.solvableRadical G) :=
    hG.kgroup.quotient _
  exact a39_part1_of_outSolvable h37 h38 fun K hK =>
    hS ↥K hK.1 (hqK.subgroup K) (sqtkSimpleList_center_quotient_of_component hG.isSQTKCat hK)

theorem a39ForSQTKCat_of_schreierSQTK
    (hS : SchreierSQTK) (h36 : A36CoreForSQTKCat)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) : A39ForSQTKCat := fun Q _ hQ =>
  ⟨a39_part1_of_schreierSQTK hS hQ (h37 Q hQ) (h38 Q hQ), a39_part2_cat hQ (h36 Q hQ)⟩

theorem a3_inputs_of_a134_schreier
    (ha134 : A134ForSQTK) (hS : SchreierSQTK) :
    A37ForSQTK ∧ A38ForSQTK ∧ A39ForSQTK := by
  have h36 := a36CoreForSQTKCat_of_a129 a129One
  have h37 := a37ForSQTKCat_of_core h36
  have h38 := a38ForSQTKCat_of_a134ForSQTK ha134 h36 h37
  have h39 := a39ForSQTKCat_of_schreierSQTK hS h36 h37 h38
  exact ⟨fun Q _ hQ => h37 Q hQ.toCat, fun Q _ hQ => h38 Q hQ.toCat,
    fun Q _ hQ => h39 Q hQ.toCat⟩

theorem stageLemma1413_of_a134_schreier
    (ha134 : A134ForSQTK) (hS : SchreierSQTK) :
    StageLemma1413 :=
  stageLemma1413_of_a39 (a3_inputs_of_a134_schreier ha134 hS).2.2

theorem stageLemma1416_of_a134_schreier
    (ha134 : A134ForSQTK) (hS : SchreierSQTK) :
    StageLemma1416 :=
  stageLemma1416_of_a3 (a3_inputs_of_a134_schreier ha134 hS).1
    (a3_inputs_of_a134_schreier ha134 hS).2.1 (a3_inputs_of_a134_schreier ha134 hS).2.2

theorem stageLemma14111_of_inputs_solv'
    (hGN : GNCampbellC128Solv) (ha134 : A134ForSQTK)
    (hS : SchreierSQTK) (h1391 : Theorem1391Statement) : StageLemma14111 :=
  have h16 := stageLemma1416_of_a134_schreier ha134 hS
  stageLemma14111_of_parts_solv hGN h16 (S1417.stageLemma1417_of_stageLemma1416 h16)
    (S1417.stageLemma1417Stab_of_stageLemma1416 h16) (stageLemma14110_of_theorem1391 h1391)

theorem stageLemma14111_of_schreier_solv
    (hGN : GNCampbellC128Solv) (hS : SchreierSQTK)
    (h1391 : Theorem1391Statement) : StageLemma14111 :=
  stageLemma14111_of_inputs_solv' hGN a134ForSQTK hS h1391

end A3Facts

end CFSG.Quasithin
