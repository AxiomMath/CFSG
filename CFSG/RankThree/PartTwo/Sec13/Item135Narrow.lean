module

public import CFSG.RankThree.PartTwo.Sec13.Item135NarrowCensus
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeCover
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCover

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree (isoLThreePi_of_mulEquiv)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open scoped MatrixGroups

theorem item135SimpleReduce_narrow (h44 : Item4_4Types135)
    (hK : KS135TwoRank) (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    (h415 : Sec4.Item4_15) : Item135SimpleReduce := by
  intro G _ _ A c L hD htype hq
  have hLc := hD.mem_thetaComponentsAt
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hbar : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨hsimp, hZbar, hbig, E, hE3, hE9⟩ := typeFacts135 hspor h414 h415 hbar htype
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hθs : Group.IsSolvable (aschbacherSolvableCore 3 L) := hθ.1
  have hL4 : SectionFourHyp L := by
    have hst := hD.toPartTwoStanding
    have hCtop : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
      intro hCt
      have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
        have hg : g ∈ Subgroup.centralizer ({c} : Set G) := hCt ▸ Subgroup.mem_top g
        exact Subgroup.mem_centralizer_singleton_iff.mp hg
      rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · rw [h, Subgroup.mem_bot] at hcZ
        exact hD.ne_one hcZ
      · obtain ⟨a, b, hab⟩ := hst.nonabelian
        exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    have hLtop : L ≠ ⊤ := fun hLt => hCtop (top_le_iff.mp (hLt ▸ hD.le_centralizer))
    exact hst.toTheoremFourHyp.sectionFourHyp hLtop
  have hcardA : ∀ n : ℕ, 5 ≤ n → n ≤ 6 →
      1 < Nat.card (alternatingGroup (Fin n)) ∧ Nat.card (alternatingGroup (Fin n)) < 20160 := by
    intro n hn5 hn6
    rw [KFacts.KS14.card_alternatingGroup_fin (by omega)]
    interval_cases n <;> decide
  rcases h44 L hL4 hperf (aschbacherSolvableCore 3 L) hθs hsimp htype with
    h1 | he2 | ⟨p, hp, hp3, he3⟩ | (he4 | h4b) | ⟨hO2, h5⟩
  · exact absurd h1 hq
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hc : Nat.card SL(2, ZMod 5) = 120 := by
      rw [Sec4.Census.card_SL2]
      norm_num
    refine false_of_surjective_of_card_lt hθs (e2.toMonoidHom.comp (QuotientGroup.mk' _))
      (e2.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    obtain ⟨e3⟩ := he3
    exact (false_of_oTwoP_equiv_SL2 hp hp3 e3 hE3 hE9).elim
  ·
    exfalso
    obtain ⟨e4⟩ := he4
    have hc : Nat.card (projSL 3 (GaloisField 3 1)) = 5616 := by
      rw [← Nat.card_congr Sec4.Census.sl3EquivProjSL.toEquiv, Sec4.Census.card_SL3_three]
    refine false_of_surjective_of_card_lt hθs (e4.toMonoidHom.comp (QuotientGroup.mk' _))
      (e4.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
  ·
    obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
    exact (false_of_isExtOf_of_card_lt hθs h4b h1 (by omega)).elim
  ·
    rcases h5 hθ.2.2.1 with ⟨hm, hO | hext⟩ | ⟨-, hext | hext | hext⟩
    · refine ⟨hO2, hm, hO, ?_⟩
      have hOK := oddCore_le_of_isQuasisimple hθs hO
      have hZ := center_quotient_oddCore_eq_map hθs hZbar hO hOK
      have hN : ((aschbacherSolvableCore 3 L).map (QuotientGroup.mk' (CFSG.oddCore L))).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
      let e : (L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
          L ⧸ aschbacherSolvableCore 3 L :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientQuotientEquivQuotient _ _ hOK)
      have hZ2 : IsPGroup 2 (Subgroup.center (L ⧸ CFSG.oddCore L)) :=
        Sec4.Census.isPGroup_two_center_of_oddCore_eq_bot
          (CFSG.LyonsUnitaryFour.oddCore_quotient_oddCore_eq_bot L)
      have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup (L ⧸ CFSG.oddCore L)) =
          CFSG.Open.pRank 2 (⊤ : Subgroup L) :=
        CFSG.SectionRank.pRank_quotient_eq (CFSG.oddCore L) (fun h2 =>
          (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore L))
            (even_iff_two_dvd.mpr h2))
      have hKJ : (Nonempty ((L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
            CFSG.Blueprint.NativeSporadic.M12) ∨
          Nonempty ((L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
            CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty ((L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L) ≃*
            CFSG.Blueprint.NativeSporadic.M22) ∨
          ∃ f : ℕ, 1 ≤ f ∧
            Sec4.IsoLThreePi ((L ⧸ CFSG.oddCore L) ⧸ Subgroup.center (L ⧸ CFSG.oddCore L)) 2 f) →
          False := fun hT => by
        have := hK (L ⧸ CFSG.oddCore L) hO hZ2 hT
        omega
      rcases htype with ⟨p, f, hp, hf, hL⟩ | hM | hJ
      · by_cases hp2 : p = 2
        · subst hp2
          exact (hKJ (Or.inr (Or.inr (Or.inr ⟨f, hf, isoLThreePi_of_mulEquiv e hL⟩)))).elim
        · exact ⟨p, f, hp, hp2, hf, hL⟩
      · obtain ⟨φ⟩ := hM
        exact (hKJ (Or.inl ⟨e.trans φ⟩)).elim
      · obtain ⟨φ⟩ := hJ
        exact (hKJ (Or.inr (Or.inl ⟨e.trans φ⟩))).elim
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact (false_of_isExtOf_of_card_lt hθs hext h1 (by omega)).elim
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact (false_of_isExtOf_of_card_lt hθs hext h1 (by omega)).elim
    · obtain ⟨h1, h2⟩ := hcardA 5 le_rfl (by norm_num)
      exact (false_of_isExtOf_of_card_lt hθs hext h1 (by omega)).elim
    · obtain ⟨h1, h2⟩ := hcardA 6 (by norm_num) le_rfl
      exact (false_of_isExtOf_of_card_lt hθs hext h1 (by omega)).elim

theorem item135Simple_narrow (h44 : Item4_4Types135)
    (hK : KS135TwoRank) (hspor : SporadicModels131) (h414 : Sec4.Item4_14_local)
    (h415 : Sec4.Item4_15) (hL3 : Item135SimpleL3) : Item135Simple :=
  item135Simple_of_steps (item135SimpleReduce_narrow h44 hK hspor h414 h415) hL3

end CFSG.RankThree.PartTwo.Sec13
