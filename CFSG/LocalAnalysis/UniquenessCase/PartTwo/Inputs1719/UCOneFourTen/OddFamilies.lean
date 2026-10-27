module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddG2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCThetaComponents
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatDef
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatThreeDef
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup

private theorem noSzOverTwo_of_noSzSection {M : Type} [Group M]
    (h : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection M) : NoSzOverTwo M :=
  fun H N _ _ _ _ => h H N _ _

theorem noSzOverTwo_of_statedClassicalModel_PSL_two
    {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSL 2 p f) : NoSzOverTwo X := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hGL : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (GL (Fin 2) K) :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCThetaComponents.noSzSection_glTwo K
  have hSL : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection ↥(CFSG.Open.StatedSL 2 K) :=
    CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_of_injective
      (CFSG.Open.StatedSL 2 K).subtype (CFSG.Open.StatedSL 2 K).subtype_injective hGL
  have hProj : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection
      (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K)) :=
    CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.noSzSection_of_surjective
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K)))
      (QuotientGroup.mk'_surjective _) hSL
  exact noSzOverTwo_of_noSzSection
    (CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_of_injective e.toMonoidHom e.injective hProj)

theorem noSzOverTwo_of_isPSLType_three
    {X F : Type} [Group X] [Field F] [Finite F]
    (h : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPSLType 3 F X) : NoSzOverTwo X := by
  obtain ⟨e⟩ := h
  have hGL : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (GL (Fin 3) F) :=
    CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.noSzSection_of_surjective
      (Subgroup.topEquiv : (⊤ : Subgroup (GL (Fin 3) F)) ≃* GL (Fin 3) F).toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup (GL (Fin 3) F)) ≃* GL (Fin 3) F).surjective
      (CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.noSzSection_glThree
        (⊤ : Subgroup (GL (Fin 3) F)))
  have hSL : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection
      (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_of_injective
      Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective hGL
  have hPSL : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection
      (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
    CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.noSzSection_of_surjective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)))
      (QuotientGroup.mk'_surjective _) hSL
  exact noSzOverTwo_of_noSzSection
    (CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_of_injective e.toMonoidHom e.injective hPSL)

theorem noSzOverTwo_of_statedClassicalModel_PSU_three
    {X : Type} [Group X] {p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .PSU 3 p f) : NoSzOverTwo X := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hGL : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection (GL (Fin 3) K) :=
    CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.noSzSection_of_surjective
      (Subgroup.topEquiv : (⊤ : Subgroup (GL (Fin 3) K)) ≃* GL (Fin 3) K).toMonoidHom
      (Subgroup.topEquiv : (⊤ : Subgroup (GL (Fin 3) K)) ≃* GL (Fin 3) K).surjective
      (CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof.noSzSection_glThree
        (⊤ : Subgroup (GL (Fin 3) K)))
  have hSU : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection ↥(CFSG.Open.StatedSU 3 (p ^ f) K) :=
    CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_of_injective
      (CFSG.Open.StatedSU 3 (p ^ f) K).subtype
      (CFSG.Open.StatedSU 3 (p ^ f) K).subtype_injective hGL
  have hProj : CFSG.RankThree.PartTwo.Sec16.Steps166.NoSzSection
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (p ^ f) K)) :=
    CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof.noSzSection_of_surjective
      (QuotientGroup.mk' ((CFSG.Open.StatedScalars (Fin 3) K).subgroupOf
        (CFSG.Open.StatedSU 3 (p ^ f) K)))
      (QuotientGroup.mk'_surjective _) hSU
  exact noSzOverTwo_of_noSzSection
    (CFSG.RankThree.PartTwo.Sec16.Steps166.noSzSection_of_injective e.toMonoidHom e.injective hProj)

theorem noSzOverTwo_of_statedClassicalModel_PSp_two {X : Type}
    [Group X] {p f : ℕ} (hp2 : p ≠ 2) (h : CFSG.Open.StatedClassicalModel X .PSp 2 p f) :
    NoSzOverTwo X := by
  obtain ⟨hadm, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hp : p.Prime := hadm.1
  have hF : ringChar K ≠ 2 := by
    have : Fact p.Prime := ⟨hp⟩
    have : Fintype K := Fintype.ofFinite K
    have hcharP : CharP K p := by
      refine charP_of_card_eq_prime_pow (p := p) (f := f) ?_
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    have := hcharP
    rw [ringChar.eq K p]
    exact hp2
  exact noSzOverTwo_of_injective e.toMonoidHom e.injective (noSzOverTwo_statedProj_statedSp hF)

theorem noSzOverTwo_of_lie_odd
    {S : Type} [Group S] [Finite S] {d : TauCeti.ValidLieTypeIndex}
    (hd : d.1.characteristic ≠ 2) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hrk : CFSG.Open.pRank d.1.characteristic (⊤ : Subgroup S) ≤ 3) : NoSzOverTwo S := by
  set p := d.1.characteristic with hpdef
  have hp : p.Prime := TauCeti.ValidLieTypeIndex.characteristic_prime d
  have hp2 : p ≠ 2 := hd
  have hexc : CFSG.LieType.DefCharRankFourExc := CFSG.LieType.defCharRankFourExc
  have hG2 : CFSG.TauCetiBridge.UntwistedBridge .G2 TauCeti.LieTypeIndex.G2 :=
    CFSG.TauCetiBridge.chevalleyBridges.g2
  by_cases hp5 : 5 ≤ p
  · rcases CFSG.LocalAnalysis.AGL81I.Section3.lieDef_rank_three_cases (K := S) hexc hG2 hp hp5
        (d := d) hpdef e hrk with
      ⟨q, hqp, hqexp, hdA⟩ | h1 | h2 | h3 | h4 | h5 | h6
    · obtain ⟨d', hv⟩ := d
      have hdA' : d' = .A 1 q := hdA
      subst hdA'
      have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA (X := S) hv e
      exact noSzOverTwo_of_statedClassicalModel_PSL_two hm
    · exact noSzOverTwo_of_statedClassicalModel_PSL_two h1
    · exact noSzOverTwo_of_statedClassicalModel_PSL_two h2
    · exact noSzOverTwo_of_isPSLType_three h3
    · exact noSzOverTwo_of_statedClassicalModel_PSU_three h4
    · exact noSzOverTwo_of_statedClassicalModel_PSp_two hp2 h5
    · exact noSzOverTwo_of_chevalleyExceptionalModel_G2 hp2 h6
  · have hp3 : p = 3 := by
      have h2 := hp.two_le
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · obtain ⟨k, hk⟩ := h
        omega
    have hpd : 3 = d.1.characteristic := hp3 ▸ hpdef
    have hrk3 : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3 := by
      rw [hp3] at hrk
      exact hrk
    rcases CFSG.LocalAnalysis.AGL81I.Section3.lieDefThree_rank_three_cases (K := S) hexc hG2 hpd
        e hrk3 with h1 | h2 | h3 | h4 | h5
    · exact noSzOverTwo_of_statedClassicalModel_PSL_two h1
    · exact noSzOverTwo_of_statedClassicalModel_PSL_two h2
    · exact noSzOverTwo_of_isPSLType_three h3
    · exact noSzOverTwo_of_statedClassicalModel_PSU_three h4
    · exact noSzOverTwo_of_statedClassicalModel_PSp_two (by norm_num) h5

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
