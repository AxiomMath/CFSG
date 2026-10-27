module

public import CFSG.LocalAnalysis.StandardType.GGTPNC2Slices
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNE6TwoSeven
public import CFSG.LocalAnalysis.StandardType.GGTPNClGen
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
public import CFSG.LocalAnalysis.StandardType.GGExcGen
public import CFSG.LocalAnalysis.StandardType.GGTPNA8SevenR
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenComp
public import CFSG.LocalAnalysis.StandardType.GGTPNI1Holds
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_c2Classical
    (hGen : GGClGenRK fun p n labJ labX => GGRegimeC2 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    (hA8 : GGTablePKnownR GGRegimeA8Seven) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeC2 p n labJ labX ∧ GGTPNClTag labX.tag := by
  have hRA := ggC2ClRARK_holds
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hcl⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, hX8⟩ | ⟨hp5, hX5⟩
  · exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨⟨hreg, hp, hp2⟩, hg⟩ hhJ hhX
  · exact hRA p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hra⟩ hhJ hhX
  · exact hA8 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hp7, hX8⟩ hhJ hhX
  · have hg : GGKacGenericCl labX p := by
      subst hp5; subst hX5; unfold GGKacGenericCl; norm_num
    exact hGen p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨⟨hreg, hp, hp2⟩, hg⟩ hhJ hhX

theorem ggTablePKnownRK_c2Exc
    (hGenE : GGExcGenRK GGRegimeC2) (hRE : GGC2ExcRERK)
    (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeC2 p n labJ labX ∧ GGTPNExcTag labX.tag := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hreg, hexc⟩ := hr
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, hX⟩
  · by_cases hg : GGKacGeneric labX p
    · exact hGenE p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX ⟨hreg, hg⟩ hhJ hhX
    · exact hRE p hp hp2 X A Ab σ J n hd hk labJ labX hΛJ hΛX
        ⟨hreg, ggKacRE_of_excPair_of_not_generic hpair hg⟩ hhJ hhX
  · exact hE67 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX
      (ggRegimeE6TwoSevenOut_of_two_le hp7 hX hreg.2.2.1) hhJ hhX

theorem ggTablePKnownRK_c2
    (hB3 : GGK0ExcB3) : GGTablePKnownRK GGRegimeC2 := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union
      (ggTablePKnownRK_c2Classical
        (ggClGenRK_of_regime
          (R := fun p n labJ labX => GGRegimeC2 p n labJ labX ∧ p.Prime ∧ p ≠ 2)
          fun _ _ _ _ h lab hiso => ggRegimeC2_not_pRankOne h.1 lab hiso)
        ggTablePKnownR_a8Seven)
      (GGTablePKnownRK.union
        (ggTablePKnownRK_c2Exc (ggExcGenRK_holds (ggK0ExcBS_of_B3 hB3) GGRegimeC2)
          (ggC2ExcRERK_holds hB3)
          (ggTablePKnownR_e6TwoSevenOut E6TwoSeven.ggE6TwoSevenComp_holds))
        (ggNonExcRK_holds GGRegimeC2))) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggTablePRow_c2_cases {p m : ℕ} {labJ labX : LargeEvenLabel}
    (hJ : labJ = ⟨.C, 2, m⟩ ∨ labJ = ⟨.B, 2, m⟩) (h : GGTablePRow p labJ labX) :
    labX = ⟨.C, 3, m⟩ := by
  rcases hJ with rfl | rfl <;> unfold GGTablePRow at h <;> norm_num at h <;> exact h.2

theorem ggNbrLabel_c2_of_config
    (hB3 : GGK0ExcB3) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L)
    (hK : GGInnerDiagOn Bs K) (hn : GGNbr p B x D J y K) (hJK : J ≤ K)
    (hpJ : p ∣ Nat.card J) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {m : ℕ}
    (hm : 2 ≤ m) (hpm : p ∣ 2 ^ m - 1) (hΛJ : LargeEvenInLambda2 ⟨.C, 2, m⟩)
    (hhJ : GGHasLabel ⟨.C, 2, m⟩ (J ⧸ Subgroup.center J)) :
    LargeEvenInLambda2 ⟨.C, 3, m⟩ ∧ GGHasLabel ⟨.C, 3, m⟩ (K ⧸ Subgroup.center K) := by
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hN, hx, hBasic⟩ := ggTPNBasicB_of_config hc hL hK hn hJK hpJ hLB
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hK hn hJK hN hx hI1
  have hhJ' : GGHasLabel ⟨.C, 2, m⟩ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun hp7 hE6 => ?_, fun _ _ _ =>
      ggTPNRankJ_of_c2 ggLabelRigidInput_holds rfl rfl hΛJ hhJ'⟩
    have h7 := ggRegimeE6TwoSevenOut_of_two_le (p := p) (n := Nat.card Bs)
      (labJ := ⟨.C, 2, m⟩) (labX := ⟨.E6, 0, 1⟩) hp7 rfl hm
    exact ggTPNHalfJ_e6TwoSeven E6TwoSeven.ggE6TwoSevenComp_holds hBasic _ hΛJ hhJ' h7.2.2.1
      h7.2.2.2 hp7 hE6
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labK₀, hΛK₀, hhK₀, -⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    ggTablePKnownRK_c2 hB3 p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
      (Nat.card Bs) hD hker ⟨.C, 2, m⟩ labK₀ hΛJ hΛK₀ ⟨rfl, rfl, hm, hpm⟩ hhJ' hhK₀
  have hiso : GGLabelIso labJ' ⟨.C, 2, m⟩ :=
    ggLabelRigidInput_holds labJ' _ _ hΛJ' hΛJ hJ' hhJ'
  have hX : labX' = ⟨.C, 3, m⟩ := ggTablePRow_c2_cases (ggLabelIso_c2_right hiso) hrow
  subst hX
  exact ⟨hΛX', hX'⟩

end CFSG.StandardType

end
