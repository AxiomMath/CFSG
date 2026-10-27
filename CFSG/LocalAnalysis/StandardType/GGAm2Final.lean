module

public import CFSG.LocalAnalysis.StandardType.GGAm2Defs
public import CFSG.LocalAnalysis.StandardType.GGAm2Slices
public import CFSG.LocalAnalysis.StandardType.GGTPNNonExcR
public import CFSG.LocalAnalysis.StandardType.GGTPNExcTwoSlices
public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompListsRE
public import CFSG.LocalAnalysis.StandardType.GGF4TwoThree
public import CFSG.LocalAnalysis.StandardType.GGK0CompREMult
public import CFSG.LocalAnalysis.StandardType.GGB36JExc
public import CFSG.LocalAnalysis.StandardType.GGTPNClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGTPNExcCover
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPNRankJ_of_am2 (hrig : GGLabelRigidInput) {Y : Type} [Group Y] {J : Subgroup Y}
    {p n : ℕ} {labJ labX : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ)
    (hreg : GGRegimeAm2 p n labJ labX)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : GGTPNRankJ J := by
  intro lab hlab hhas hrk
  have hiso : GGLabelIso lab labJ := hrig lab labJ (↥J ⧸ Subgroup.center ↥J) hlab hΛ hhas hhJ
  obtain ⟨-, htag, hn, hrank⟩ := hreg
  obtain ⟨t, r, k⟩ := labJ
  obtain ⟨t', r', k'⟩ := lab
  simp only at htag hn hrank
  subst htag
  simp only [GGLabelIso] at hiso
  simp only [GGTPNRankOne] at hrk
  rcases hiso with h | h | h | h | h | h | h | h <;> simp_all <;> omega

theorem ggTablePKnownR_am2
    (hBig : GGAm2ExcBig)
    (hEx2 : GGTablePKnownR GGRegimeAm2ExcTwo) (hNon : GGNonExcR GGRegimeAm2) :
    GGTablePKnownR GGRegimeAm2 := by
  have hCl := ggAm2ClGen_holds
  have hRA := ggAm2RA_holds
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  have hp3 : p = 3 := hr.1
  have hm : GGTPNMarked p (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  by_cases hcl : GGTPNClTag labX.tag
  · rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, -⟩ | ⟨hp5, -⟩
    · exact hCl p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hg⟩ hhJ hhX
    · exact hRA p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hra⟩ hhJ hhX
    · omega
    · omega
  · by_cases hexc : GGTPNExcTag labX.tag
    · rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, -⟩
      · by_cases hn1 : labX.n = 1
        · refine hEx2 p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hn1, ?_⟩ hhJ hhX
          have h := hpair.2.2.2
          rcases h with h | h | h | h | h <;> simp [h]
        · have h1 : 1 ≤ labX.n := hΛX.1
          exact hBig p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hpair, by omega⟩ hhJ hhX
      · omega
    · exact hNon p hp hp2 X A Ab σ J n hd labJ labX hΛJ hΛX ⟨hr, hcl, hexc⟩ hhJ hhX

theorem ggNbrTablePNbrInputOn_am2
    (hT : GGTPNTransferBNoCorners) (hK : GGTablePKnownR GGRegimeAm2) :
    GGNbrTablePNbrInputOn GGRegimeAm2 := by
  intro G _ _ p B Bs x L D J y K hc hL hKi hn labJ labK hΛJ hΛK hr hhJ hhK
  have hp3 : p = 3 := hr.1
  obtain ⟨hJK, hN, hx, hBasic⟩ := hT G p B Bs x L D J y K hc hL hKi hn
  have hβ := hc.1.2.2.2.2.2.1
  have hhJ' : GGHasLabel labJ (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK).symm hhJ
  have hcorners : GGTPNCorners p (J.subgroupOf K) :=
    ⟨fun hp7 _ => absurd (hp3.symm.trans hp7) (by decide),
      fun _ _ _ => ggTPNRankJ_of_am2 ggLabelRigidInput_holds hΛJ hr hhJ'⟩
  have hD : GGTPNDatumB p (Nat.card Bs) (fun _ _ => True) (ggAutsOf K Bs hN)
      (ggAutsOf K B (hc.2.1.1.trans hN)) (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) :=
    ⟨hBasic, hcorners⟩
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hJ', hX'⟩ :=
    hK p hβ.1 hβ.2.1 ↥K (ggAutsOf K Bs hN) (ggAutsOf K B (hc.2.1.1.trans hN))
      (K.normalizerMonoidHom ⟨x, hx⟩) (J.subgroupOf K) (Nat.card Bs) hD labJ labK hΛJ hΛK
      hr hhJ' hhK
  exact ⟨labJ', labX', hΛJ', hΛX', hrow,
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJK) hJ', hX'⟩

theorem ggNbrTablePNbrInputOn_am2_of_leaves
    (hT : GGTPNTransferBNoCorners) (hB3 : GGK0ExcB3) :
    GGNbrTablePNbrInputOn GGRegimeAm2 := by
  have hRE : GGK0CompRE :=
    ggK0CompRE_of_mult (ggK0CompREMult_of_excB (ltqJx_excB_of_excBS (ggK0ExcBS_of_B3 hB3)))
  exact ggNbrTablePNbrInputOn_am2 hT
    (ggTablePKnownR_am2 (ggAm2ExcBig_holds TCJ.ggTCJKnown_holds)
      (ggTablePKnownR_am2ExcTwo (ggE6TwoThreeComp_of_K0RE hRE) (ggTwE6TwoThreeComp_of_K0RE hRE)
        (ggE7TwoThreeComp_of_K0RE hRE) (ggE8TwoThreeComp_of_K0RE hRE) ggF4TwoThreeComp_holds)
      (ggNonExcR_holds GGRegimeAm2))

theorem ggTablePRow_am2_a3_of_datum
    {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} {n : ℕ}
    (hd : GGTPNDatumB 3 n (fun _ _ => True) A Ab σ J)
    (hhJ : GGHasLabel (⟨.A, 3, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))
    (labX : LargeEvenLabel) (hΛX : LargeEvenInLambda2 labX)
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    GGTPNRow 3 J := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : 3 ≠ 2 := by norm_num
  have hΛJ : LargeEvenInLambda2 (⟨.A, 3, 1⟩ : LargeEvenLabel) := by
    simp [LargeEvenInLambda2]
  have hr : GGRegimeAm2 3 n (⟨.A, 3, 1⟩ : LargeEvenLabel) labX :=
    ⟨rfl, rfl, rfl, by norm_num⟩
  have hm : GGTPNMarked 3 (fun _ _ => True) A := hd.1.2.2.2.2.2.2.2
  by_cases hcl : GGTPNClTag labX.tag
  · rcases ggTPN_classicalCover hp hp2 hm hΛX hhX hcl with hg | hra | ⟨hp7, -⟩ | ⟨hp5, -⟩
    · exact ggAm2ClGen_holds 3 hp hp2 X A Ab σ J n hd (⟨.A, 3, 1⟩ : LargeEvenLabel) labX
        hΛJ hΛX ⟨hr, hg⟩ hhJ hhX
    · exact ggAm2RA_holds 3 hp hp2 X A Ab σ J n hd (⟨.A, 3, 1⟩ : LargeEvenLabel) labX
        hΛJ hΛX ⟨hr, hra⟩ hhJ hhX
    · omega
    · omega
  · by_cases hexc : GGTPNExcTag labX.tag
    · rcases ggTPN_excCover hp hp2 hm hΛX hhX hexc with hpair | ⟨hp7, -⟩
      · by_cases hn1 : labX.n = 1
        · rcases hpair.2.2.2 with hE6 | hTw | hE7 | hE8 | hF4
          · exact (am2_a3_exc_E6_false hd hhJ hΛX hE6 hn1 hhX).elim
          · exact (am2_a3_exc_twE6_false hd hhJ hΛX hTw hn1 hhX).elim
          · exact (am2_a3_exc_E78_false hd hhJ hΛX (Or.inl hE7) hhX).elim
          · exact (am2_a3_exc_E78_false hd hhJ hΛX (Or.inr hE8) hhX).elim
          · exact (ltqSl_A3_false_of_F4 ggF4TwoThreeComp_holds hd hΛX hF4 hn1 hhX hhJ).elim
        · have h2n : 2 ≤ labX.n := by
            have h := hΛX.1
            omega
          exact (ggAm2ExcBig_holds TCJ.ggTCJKnown_holds) 3 hp hp2 X A Ab σ J n hd
            (⟨.A, 3, 1⟩ : LargeEvenLabel) labX hΛJ hΛX ⟨hr, hpair, h2n⟩ hhJ hhX
      · omega
    · exact ggNonExcR_holds GGRegimeAm2 3 hp hp2 X A Ab σ J n hd
        (⟨.A, 3, 1⟩ : LargeEvenLabel) labX hΛJ hΛX ⟨hr, hcl, hexc⟩ hhJ hhX

end CFSG.StandardType

end
