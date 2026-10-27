module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyOneProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.WClosNormalizerGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 CFSG.Quasithin.H

variable {G : Type} [Group G] [Finite G]

theorem map_mbar_le_natNorm_of_ctx17_40 {D : Data G} {V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D ⊥ V L n) (h35 : R17_35At D ⊥ V)
    (hS : CNatModStructSU3 (Vtil (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian)
      (barSub (⊥ : Subgroup G) V c.ctx.hyp125.isElemAbelian L) 2) :
    (Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian).map
        (MulAut.congr (su3NatEquiv hS)).toMonoidHom ≤ natNorm (StatedSU 3 4 hS.K) := by
  have hV := c.ctx.hyp125.isElemAbelian
  have hLbarMbar : barSub (⊥ : Subgroup G) V hV L ≤ Mbar D.M ⊥ V hV :=
    barSub_mono (⊥ : Subgroup G) V hV c.ctx.mem_calC.1.le
  have hnormal : ((barSub (⊥ : Subgroup G) V hV L).subgroupOf (Mbar D.M ⊥ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal_of_ctx17_40 c h35
  have hMbarNorm : Mbar D.M ⊥ V hV ≤
      normalizer (barSub (⊥ : Subgroup G) V hV L : Set (MulAut (Vtil (⊥ : Subgroup G) V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarMbar).mp hnormal
  exact map_le_natNorm_of_cNatModSU3 hS hMbarNorm

theorem card_K_of_cNatModStructSU3_two {W : Type} [Group W] {X : Subgroup (MulAut W)}
    (hS : CNatModStructSU3 W X 2) : Nat.card hS.K = 16 := by
  have h := hS.cardK
  norm_num at h ⊢
  exact h

theorem aBar_le_two_of_ctx17_40 {D : Data G} {V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D ⊥ V L n) (h35 : R17_35At D ⊥ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    aBar D.M ⊥ V c.ctx.hyp125.isElemAbelian ≤ 2 := by
  classical
  obtain ⟨hS⟩ := cNatModSU3_two_of_ctx17_40 c h35 hx h61 h127 h1214
  have hImLe := map_mbar_le_natNorm_of_ctx17_40 c h35 hS
  calc aBar D.M ⊥ V c.ctx.hyp125.isElemAbelian
      = E3.aParam ((Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian).map
          (MulAut.congr (su3NatEquiv hS)).toMonoidHom) :=
        (CFSG.Quasithin.H.aParam_map_congrHom (su3NatEquiv hS) _).symm
    _ ≤ 2 := by
      have : CharP hS.K 2 := charP_cardK hS
      exact SU3.aParam_le (n := 2) le_rfl
        ((card_K_of_cNatModStructSU3_two hS).trans (by norm_num)) hImLe

theorem pRank_two_mbar_le_three_of_ctx17_40 {D : Data G} {V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D ⊥ V L n) (h35 : R17_35At D ⊥ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) :
    CFSG.Open.pRank 2 (Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian) ≤ 3 := by
  classical
  obtain ⟨hS⟩ := cNatModSU3_two_of_ctx17_40 c h35 hx h61 h127 h1214
  have hImLe := map_mbar_le_natNorm_of_ctx17_40 c h35 hS
  have h1 : CFSG.Open.pRank 2 (Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian) ≤
      CFSG.Open.pRank 2 ((Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian).map
        (MulAut.congr (su3NatEquiv hS)).toMonoidHom) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) _ (MulAut.congr (su3NatEquiv hS)).injective _
  have : CharP hS.K 2 := charP_cardK hS
  have h2 : CFSG.Open.pRank 2 ((Mbar D.M ⊥ V c.ctx.hyp125.isElemAbelian).map
      (MulAut.congr (su3NatEquiv hS)).toMonoidHom) ≤ 2 + 1 :=
    SU3.pRank_le (n := 2) (by norm_num)
      ((card_K_of_cNatModStructSU3_two hS).trans (by norm_num)) hImLe
  omega

theorem false_of_ctx17_40 {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_40 D V₀ V L n) (h35 : R17_35At D V₀ V) (h39 : R17_39At D V₀ V)
    (h41_3 : R17_41_3At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h111 : W3Thm111 G) : False := by
  classical
  have hV₀ : V₀ = ⊥ := c.v0
  subst hV₀
  have hp : Hyp125 D ⊥ V := c.ctx.hyp125
  obtain ⟨-, hk2, hm4, -⟩ := data_of_ctx17_33 c.ctx h35 h39
  have ha2 := aBar_le_two_of_ctx17_40 c h35 hx h61 h127 h1214
  have hm2 : MBarGT D.M ⊥ V 2 := (hp.mBarGT_iff_lt_mBar 2).2 (by omega)
  have hW0 : ⁅E3.wClos V 0 D.T, V⁆ = ⊥ :=
    commutator_wClos_eq_bot_of_lt D h111 hp hm2 (by omega)
  have hW0' : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hW0
  have hrk : ∀ q ∈ D.sig, 3 ≤ CFSG.pRank q ↥D.M := by
    intro q hq
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hx.three_le q hq
  have hNW0 : normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fifteen_thirteen_a D (r129_1_of_r127 D h127) h61 hx.sig_nonempty hrk hp hW0'
  have hmk : MBarGT D.M ⊥ V (D.k + 0) := (hp.mBarGT_iff_lt_mBar _).2 (by omega)
  have hC2 : ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M := by
    rcases twelve_ten_two D hx h61 h126 h111 hp rfl hmk with h | h
    · exact absurd hNW0 h
    · simpa [hk2] using h
  obtain ⟨A, hA, hAne⟩ := exists_gammaTwo_barSub_ne_bot hp hC2
  obtain ⟨g, hAg, hmA⟩ := hA.2
  have hpR := pRank_two_mbar_le_three_of_ctx17_40 c h35 hx h61 h127 h1214
  have hVg : V ≤ conjSubgroup D.M g :=
    le_conjSubgroup_of_mem_gammaTwo hp (h41_3 L n c) hpR hA hAne hmA hAg
  have hAC : ¬ A ≤ centralizer (V : Set G) := fun hle =>
    hAne ((barSub_bot_iff_le_centralizer hp (hA.1.trans D.sylowM.le)).2 hle)
  exact not_le_conjSubgroup_of_mem_gammaTwo hp hW0' hA hAC hAg hVg

theorem seventeen_thirtythree_two_three (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h35 : R17_35At D V₀ V) (h39 : R17_39At D V₀ V) (h41_3 : R17_41_3At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h111 : W3Thm111 G) :
    R17_33_2At D V₀ V ∧ R17_33_3At D V₀ V := by
  have key : ∀ (L : Subgroup G) (n : ℕ), L ∈ calC D.M → IsSU3 (Bar2 L) n →
      IsPowTwo n ∧ 1 < mSub V₀ := by
    intro L n hL hSU
    by_contra hcon
    have c : Ctx17_33 D V₀ V L n := ⟨hV, hL, hSU, hcon⟩
    exact false_of_ctx17_40 ⟨c, h39 L n c⟩ h35 h39 h41_3 hx h61 h126 h127
      h1214 h111
  exact ⟨fun L n hL hSU => (key L n hL hSU).1, fun L n hL hSU => (key L n hL hSU).2⟩

theorem seventeen_thirtythree_two (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h35 : R17_35At D V₀ V) (h39 : R17_39At D V₀ V) (h41_3 : R17_41_3At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h111 : W3Thm111 G) :
    R17_33_2At D V₀ V :=
  (seventeen_thirtythree_two_three D V₀ V hV h35 h39 h41_3 hx h61 h126 h127 h1214 h111).1

theorem seventeen_thirtythree_three (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h35 : R17_35At D V₀ V) (h39 : R17_39At D V₀ V) (h41_3 : R17_41_3At D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h111 : W3Thm111 G) :
    R17_33_3At D V₀ V :=
  (seventeen_thirtythree_two_three D V₀ V hV h35 h39 h41_3 hx h61 h126 h127 h1214 h111).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
