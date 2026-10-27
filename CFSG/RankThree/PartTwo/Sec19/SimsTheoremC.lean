module

public import CFSG.CGT.Foote82.Statements
public import CFSG.RankThree.PartTwo.Sec6.Item641
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCClimb
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTI
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCFooteBlocks
import CFSG.RankThree.PartTwo.Sec19.SimsItem316Small
import CFSG.RankThree.PartTwo.Sec19.SimsItem316Narrow
import CFSG.RankThree.PartTwo.Sec19.F194Item316X
import CFSG.CGT.PushingUpLit.CGT6.EmbEndQuot

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.AGLEmbedding

namespace SimsTheoremC

variable {G : Type} [Group G]

theorem glbIsMaxTwoLocal_of_isMaximalTwoLocal {M : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) : CFSG.Open.GLBIsMaxTwoLocal M :=
  ⟨hM.1, fun X hX hMX => by
    by_contra hne
    exact hM.2 X (lt_of_le_of_ne hMX (Ne.symm hne)) hX⟩

theorem isMaximalTwoLocal_of_glbIsMaxTwoLocal {M : Subgroup G}
    (hM : CFSG.Open.GLBIsMaxTwoLocal M) : CFSG.IsMaximalTwoLocal M :=
  ⟨hM.1, fun H hlt hH => (ne_of_gt hlt) (hM.2 H hH hlt.le)⟩

theorem maximalTwoLocalsContaining_eq_singleton {M J : Subgroup G}
    (hM : CFSG.Open.GLBIsMaxTwoLocal M) (hJM : J ≤ M)
    (huniq : ∀ M' : Subgroup G, CFSG.Open.GLBIsMaxTwoLocal M' → J ≤ M' → M' = M) :
    CFSG.maximalTwoLocalsContaining (J : Set G) = {M} := by
  ext M'
  simp only [CFSG.maximalTwoLocalsContaining, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hM', hJ⟩
    exact huniq M' (glbIsMaxTwoLocal_of_isMaximalTwoLocal hM') hJ
  · rintro rfl
    exact ⟨isMaximalTwoLocal_of_glbIsMaxTwoLocal hM, hJM⟩

theorem normal_of_footeNonsolvableSimple (hC : CFSG.CGT.PushingUpLit.FooteNonsolvableSimple)
    [Finite G] (hs : IsSimpleGroup G) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hc : CFSG.Assembly.IsCharTwoType G) {M J : Subgroup G} (hM : CFSG.Open.GLBIsMaxTwoLocal M)
    (hJ : IsFooteBlock M J) (hshort : IsShort J)
    (huniq : ∀ M' : Subgroup G, CFSG.Open.GLBIsMaxTwoLocal M' → J ≤ M' → M' = M) :
    (J.subgroupOf M).Normal :=
  hC G hs hK hc M J (isMaximalTwoLocal_of_glbIsMaxTwoLocal hM) hJ.le
    ((CFSG.Open.IsSubnormal.iff_subgroupOf hJ.le).mp hJ.subnormal)
    (isShortGroup_of_isShort hshort)
    ((CFSG.CGT.PushingUpLit.CGT6.EndQuot.isQuasisimple_iff_open _).mpr hJ.quasisimple)
    (maximalTwoLocalsContaining_eq_singleton hM hJ.le huniq)

theorem isFooteBlock_of_isBlock {M L : Subgroup G} (hL : IsBlock M L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : IsFooteBlock M L :=
  ⟨hL.2.1, (CFSG.Open.IsSubnormal.iff_subgroupOf hL.2.1).mpr hL.2.2, hL.1.eq_twoResidual,
    (CFSG.CGT.PushingUpLit.CGT6.EndQuot.isQuasisimple_iff_open _).mp hq,
    ⟨hL.1.blockZ_lt_blockU, hL.1.irreducible⟩⟩

theorem isPGroup_of_isElemAbelian {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) :
    IsPGroup 2 V := fun g => ⟨1, by
  apply Subtype.ext
  simpa using hV.2 g g.2⟩

theorem normalizer_eq_of_normal [Finite G] {M J : Subgroup G} (hM : CFSG.IsMaximalTwoLocal M)
    (hJM : J ≤ M) (hn : (J.subgroupOf M).Normal) (hS : IsShort J) :
    Subgroup.normalizer (J : Set G) = M := by
  have hMN : M ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJM).mp hn
  have hU : blockU J ≤ CFSG.Open.pCoreOf 2 J := hS.blockU_le_center.trans inf_le_left
  have hQ1 : CFSG.Open.pCoreOf 2 J ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff] at hU
    have := hS.blockZ_lt_blockU
    rw [hU] at this
    exact not_lt_bot this
  have hloc : IsPLocal 2 (Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G)) :=
    CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup (isPGroup_pCoreOf J) hQ1
  have hNQ : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) := normalizer_le_normalizer_pCoreOf J
  have hEq : Subgroup.normalizer (CFSG.Open.pCoreOf 2 J : Set G) = M := by
    by_contra hne
    exact hM.2 _ (lt_of_le_of_ne (hMN.trans hNQ) (Ne.symm hne)) hloc
  exact le_antisymm (hNQ.trans hEq.le) hMN

theorem inCatalog_of_isFType (h5 : CFSG.CGT.Foote82.FooteFiveF)
    (h6 : CFSG.CGT.Foote82.FooteSixF) (h7S : CFSG.CGT.Foote82.FooteSevenSharpF)
    (hNS : CFSG.CGT.PushingUpLit.FooteNonsolvableSimple) (h310 : Sec6.Item3_10)
    (hX : Item316ScriptX) (hH : Lit316Harada) (hHall : Lit316Hall) (hE : Lit316SolomonEven)
    (h7 : Lit316SolomonSeven) [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (hc : CFSG.Assembly.IsCharTwoType G) (he3 : CFSG.Assembly.evenRank G = 3) {M L : Subgroup G}
    (hM : CFSG.IsMaximalTwoLocal M) (hL : IsBlock M L) (hF : IsFType L) :
    CFSG.Assembly.InCatalog G := by
  have hLF : IsFooteBlock M L := isFooteBlock_of_isBlock hL (isQuasisimple_of_isFType hL.1 hF)
  have hLB : InFooteB L :=
    h6 G hs hnab hK hc he3 M L (glbIsMaxTwoLocal_of_isMaximalTwoLocal hM) hLF hF
  obtain ⟨J, hJstar, hJF⟩ := exists_inFooteBStar_isFType h7S hs hnab hK hc he3 hLB hF
  obtain ⟨MJ, hMJ, hJMJ, huniq⟩ := h5 G hs hnab hK hc he3 J hJstar hJF
  have hMJ' : CFSG.IsMaximalTwoLocal MJ := isMaximalTwoLocal_of_glbIsMaxTwoLocal hMJ
  have huniq' : ∀ M' : Subgroup G, CFSG.IsMaximalTwoLocal M' → J ≤ M' → M' = MJ :=
    fun M' hM' hJM' => huniq M' (glbIsMaxTwoLocal_of_isMaximalTwoLocal hM') hJM'
  have hchar : MJ ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 MJ : Set G) ≤
      CFSG.Open.pCoreOf 2 MJ := hc MJ hMJ.1
  by_cases hab : ∀ x ∈ blockU J, ∀ y ∈ blockU J, x * y = y * x
  ·
    have hshort : IsShort J := isShort_of_isFooteBlock hJMJ hchar hab
    have hblock : IsBlock MJ J :=
      ⟨hshort, hJMJ.le, (CFSG.Open.IsSubnormal.iff_subgroupOf hJMJ.le).mp hJMJ.subnormal⟩
    have hnorm := normal_of_footeNonsolvableSimple hNS hs hK hc hMJ hJMJ hshort huniq
    have hNJ : Subgroup.normalizer (J : Set G) = MJ :=
      normalizer_eq_of_normal hMJ' hJMJ.le hnorm hshort
    have hsing := maximalTwoLocalsContaining_eq_singleton hMJ hJMJ.le huniq
    have hel : CFSG.Open.IsElemAbelian 2 (blockU J) := IsShort.isElemAbelian_blockU hshort
    have hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
      (CFSG.CGT.PushingUpLit.CGT6.EndQuot.isQuasisimple_iff_open _).mpr hJMJ.quasisimple
    have hperf : ⁅J, J⁆ = J := commutator_eq_of_isShort_of_isQuasisimple hshort hq
    have hcent : ∀ t ∈ CFSG.Open.pCoreOf 2 MJ, t ≠ 1 →
        CFSG.generalizedFitting ↥(Subgroup.centralizer ({t} : Set G)) =
          CFSG.pCore 2 ↥(Subgroup.centralizer ({t} : Set G)) :=
      fun t ht h1 => generalizedFitting_centralizer_eq_pCore hc ht h1
    rcases hJF with ⟨n, hn, hA⟩ | hA | ⟨m, hm, hO⟩ | ⟨m, hm, hO⟩ | hA
    · rcases Nat.even_or_odd n with he | ho
      · have h11 := Narrow316.le_eleven_of_isAltNaturalType he3 hMJ' hJMJ.le hA
        have h6810 : n = 6 ∨ n = 8 ∨ n = 10 := by
          obtain ⟨k, rfl⟩ := he
          omega
        exact hE G hs hnab hK hc he3 MJ J hMJ' hblock hel hNJ hsing ⟨n, h6810, hA⟩ hcent
      · exact hX G hs hnab hK hc MJ J hMJ' hblock (Or.inr ⟨n, ho, hA⟩)
    · exact h7 G hs hnab hK hc MJ J hMJ' hblock hel hNJ hsing hA hcent
    · rcases Nat.lt_or_ge m 4 with hm4 | hm4
      · obtain rfl : m = 3 := by omega
        exact hE G hs hnab hK hc he3 MJ J hMJ' hblock hel hNJ hsing
          ⟨8, by norm_num, isAltNaturalType_eight_of_isOmegaPlusType_three hO⟩ hcent
      · exact absurd (Narrow316.lt_four_of_isOmegaPlusType he3 hMJ' hJMJ.le hO) (by omega)
    · have hm4 := Narrow316.lt_four_of_isOmegaMinusType he3 hMJ' hJMJ.le hO
      have h23 : IsOmegaMinusType J 2 ∨ IsOmegaMinusType J 3 := by
        obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
        exacts [Or.inl hO, Or.inr hO]
      exact hH G hs hnab hK hc he3 MJ J hMJ' hblock hperf h23 hel hsing
    · exact hHall G hs hnab hK hc MJ J hMJ' hblock hperf hA hel hsing hcent
  ·
    obtain ⟨V, hV⟩ := exists_maximal_normal_elemAbelian MJ
    have hVJ : V ≤ Subgroup.centralizer (J : Set G) :=
      le_centralizer_of_isFooteBlock hJMJ hab hV.prop.2.2 hV.prop.1 hV.prop.2.1
    exact h310 G hs hnab hK hc MJ hMJ' V hV
      (isTI_of_unique hMJ' huniq' (isPGroup_of_isElemAbelian hV.prop.2.2) hV.prop.2.1 hVJ)

end SimsTheoremC

open SimsTheoremC in
theorem lit316NonGood_of_theoremC (h5 : CFSG.CGT.Foote82.FooteFiveF)
    (h6 : CFSG.CGT.Foote82.FooteSixF) (h7S : CFSG.CGT.Foote82.FooteSevenSharpF)
    (hNS : CFSG.CGT.PushingUpLit.FooteNonsolvableSimple) (h310 : Sec6.Item3_10)
    (hX : Item316ScriptX) (hH : Lit316Harada) (hHall : Lit316Hall) (hE : Lit316SolomonEven)
    (h7 : Lit316SolomonSeven) : Lit316NonGood := by
  intro G _ _ hs hnab hK hc he3 M L hM hL h
  have hF : IsFType L := by
    rcases h with ⟨hS, -⟩ | ⟨hHH, -⟩
    · exact isFType_of_isSolomonTypes hL.1 hS
    · exact isFType_of_isHaradaHallTypes hHH
  exact inCatalog_of_isFType h5 h6 h7S hNS h310 hX hH hHall hE h7 hs hnab hK hc he3 hM hL hF

open SimsTheoremC in
theorem item316_of_foote (hX : Item316ScriptX) (hH : Lit316Harada) (hHall : Lit316Hall)
    (hE : Lit316SolomonEven) (h7 : Lit316SolomonSeven) (h5 : CFSG.CGT.Foote82.FooteFiveF)
    (h6 : CFSG.CGT.Foote82.FooteSixF) (h7S : CFSG.CGT.Foote82.FooteSevenSharpF)
    (hNS : CFSG.CGT.PushingUpLit.FooteNonsolvableSimple)
    (h310 : Sec6.Item3_10) : Item316 :=
  have hN := lit316NonGood_of_theoremC h5 h6 h7S hNS h310 hX hH hHall hE h7
  item316_of_leaves hX (item316Small_of hX hE hN) hH hHall hE h7 hN

end CFSG.RankThree.PartTwo.Sec19
