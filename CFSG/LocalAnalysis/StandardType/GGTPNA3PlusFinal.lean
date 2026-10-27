module

public import CFSG.LocalAnalysis.StandardType.GGTPNA3PlusSlices
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
import CFSG.LocalAnalysis.StandardType.GGTypeANbrRowFilter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_a3PlusClassical
    (hGen : GGClGenRK fun p n labJ labX => GGRegimeA3Plus p n labJ labX ∧ p.Prime ∧ p ≠ 2)
    (hA8 : GGTablePKnownR GGRegimeA8Seven) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeA3Plus p n labJ labX ∧ GGTPNClTag labX.tag := by
  have hRA := ggA3PlusClRARK_holds
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

theorem ggTablePKnownRK_a3PlusExc
    (hGenE : GGExcGenRK GGRegimeA3Plus) (hRE : GGA3PlusExcRERK)
    (hE67 : GGTablePKnownR GGRegimeE6TwoSevenOut) :
    GGTablePKnownRK fun p n labJ labX => GGRegimeA3Plus p n labJ labX ∧ GGTPNExcTag labX.tag := by
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

theorem ggTablePKnownRK_a3Plus
    (hB3 : GGK0ExcB3) : GGTablePKnownRK GGRegimeA3Plus := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union
      (ggTablePKnownRK_a3PlusClassical
        (ggClGenRK_of_regime
          (R := fun p n labJ labX => GGRegimeA3Plus p n labJ labX ∧ p.Prime ∧ p ≠ 2)
          fun _ _ _ _ h lab hiso => ggRegimeA3Plus_not_pRankOne h.1 lab hiso)
        ggTablePKnownR_a8Seven)
      (GGTablePKnownRK.union
        (ggTablePKnownRK_a3PlusExc (ggExcGenRK_holds (ggK0ExcBS_of_B3 hB3) GGRegimeA3Plus)
          (ggA3PlusExcRERK_holds hB3)
          (ggTablePKnownR_e6TwoSevenOut E6TwoSeven.ggE6TwoSevenComp_holds))
        (ggNonExcRK_holds GGRegimeA3Plus))) ?_
  intro p n labJ labX hJ
  by_cases hcl : GGTPNClTag labX.tag
  · exact Or.inl ⟨hJ, hcl⟩
  · by_cases hexc : GGTPNExcTag labX.tag
    · exact Or.inr (Or.inl ⟨hJ, hexc⟩)
    · exact Or.inr (Or.inr ⟨hJ, hcl, hexc⟩)

theorem ggTablePRow_a3Plus_cases {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : p ∣ 2 ^ m + 1)
    {labJ labX : LargeEvenLabel} (hJ : labJ = ⟨.A, 3, m⟩ ∨ labJ = ⟨.D, 3, m⟩)
    (h : GGTablePRow p labJ labX) : labX = ⟨.A, 5, m⟩ ∨ labX = ⟨.twD, 4, m⟩ := by
  rcases hJ with rfl | rfl <;> unfold GGTablePRow at h <;> norm_num at h
  · rcases h with ⟨hq, -⟩ | ⟨-, hX⟩
    · exact (not_dvd_two_pow_sub_add hp2 hp hq hpm).elim
    · exact Or.inl hX
  · rcases h with ⟨hq, -⟩ | ⟨-, hX⟩
    · exact (not_dvd_two_pow_sub_add hp2 hp hq hpm).elim
    · exact Or.inr hX

theorem ggNbrLabel_a3Plus_of_config
    (hB3 : GGK0ExcB3) (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hc : GGConfig p B Bs x L D J) (hL : GGInnerDiagOn Bs L)
    (hK : GGInnerDiagOn Bs K) (hn : GGNbr p B x D J y K) (hJK : J ≤ K)
    (hpJ : p ∣ Nat.card J) (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) {m : ℕ}
    (hm : 2 ≤ m) (hpm : p ∣ 2 ^ m + 1) (hΛJ : LargeEvenInLambda2 ⟨.A, 3, m⟩)
    (hhJ : GGHasLabel ⟨.A, 3, m⟩ (J ⧸ Subgroup.center J)) :
    ∃ labK : LargeEvenLabel, (labK = ⟨.A, 5, m⟩ ∨ labK = ⟨.twD, 4, m⟩) ∧
      LargeEvenInLambda2 labK ∧ GGHasLabel labK (K ⧸ Subgroup.center K) := by
  have hβ := hc.1.2.2.2.2.2.1
  obtain ⟨hN, hx, hBasic⟩ := ggTPNBasicB_of_config hc hL hK hn hJK hpJ hLB
  have hker := ggTPNTrKernelI1_holds G p B Bs x L D J y K hc hL hK hn hJK hN hx hI1
  have hhJ' : GGHasLabel ⟨.A, 3, m⟩ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) := by
    refine ⟨fun hp7 hE6 => ?_, fun _ _ _ =>
      ggTPNRankJ_of_a3 ggLabelRigidInput_holds rfl rfl hΛJ hhJ'⟩
    have h7 := ggRegimeE6TwoSevenOut_of_two_le (p := p) (n := Nat.card Bs)
      (labJ := ⟨.A, 3, m⟩) (labX := ⟨.E6, 0, 1⟩) hp7 rfl hm
    exact ggTPNHalfJ_e6TwoSeven E6TwoSeven.ggE6TwoSevenComp_holds hBasic _ hΛJ hhJ' h7.2.2.1
      h7.2.2.2 hp7 hE6
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labK₀, hΛK₀, hhK₀, -⟩ := largeEvenMarking_exists_hasLabel hK
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    ggTablePKnownRK_a3Plus hB3 p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K)
      (Nat.card Bs) hD hker ⟨.A, 3, m⟩ labK₀ hΛJ hΛK₀ ⟨rfl, rfl, hm, hpm⟩ hhJ' hhK₀
  have hiso : GGLabelIso labJ' ⟨.A, 3, m⟩ :=
    ggLabelRigidInput_holds labJ' _ _ hΛJ' hΛJ hJ' hhJ'
  exact ⟨labX', ggTablePRow_a3Plus_cases hβ.1 hβ.2.1 hpm (ggLabelIso_a3_right hiso) hrow, hΛX',
    hX'⟩

end CFSG.StandardType

end
