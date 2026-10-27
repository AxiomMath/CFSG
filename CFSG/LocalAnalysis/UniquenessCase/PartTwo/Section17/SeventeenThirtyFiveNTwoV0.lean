module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyFiveProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyNineGeneral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34ModuleSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_35_1_nTwoV0 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L : Subgroup G) (c : Ctx17_33 D V₀ V L 2), D.k = 2 → 3 ≤ mSub V₀ →
    mBar D.M V₀ V c.hyp125.isElemAbelian < 2 * 2 + 2

theorem gap17_35_1_nTwoV0_holds (D : Data G) (V₀ V : Subgroup G) :
    Gap17_35_1_nTwoV0 D V₀ V := by
  intro L c _ h3
  exact absurd ⟨⟨1, rfl⟩, by omega⟩ c.counter

theorem s17_rk_barSub_le_three
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h128 : W4Lem12_8)
    {V₀ V L : Subgroup G} (c : Ctx17_33 D V₀ V L 2) (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (h0 : V₀ ≠ ⊥) (h36a : R17_36aAt D V₀ V)
    (hm6 : mBar D.M V₀ V c.hyp125.isElemAbelian ≤ 2 * 2 + 2)
    {A : Subgroup G} (hAM : A ≤ D.M) (hA : IsElemAbelian 2 A) :
    CFSG.Quasithin.rk ↥(barSub V₀ V c.hyp125.isElemAbelian A) ≤ 3 := by
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hnt : ¬ F08.Thin8 L := not_thin_of_isSU3 hSyl c.shape
  have hLbar_ne : barSub V₀ V c.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_not_thin c.hyp125 h117 c.mem_calC hnt
  have hcomp := barSub_mem_compBar_of_ne_bot c.hyp125 c.mem_calC hLbar_ne
  have hSU : IsSU3 ↥(barSub V₀ V c.hyp125.isElemAbelian L) 2 :=
    isSU3_barSub c.hyp125 c.mem_calC hLbar_ne c.shape
  have hKY : barSub V₀ V c.hyp125.isElemAbelian L ≤ Mbar D.M V₀ V c.hyp125.isElemAbelian :=
    barSub_mono V₀ V c.hyp125.isElemAbelian hLM
  have hKn := barSub_subgroupOf_mbar_normal (V₀ := V₀) (V := V) c.hyp125.isElemAbelian hLM
    (uc2_17_36a_normal c h36a)
  have hO2 : ∀ P : Subgroup (MulAut (Vtil V₀ V c.hyp125.isElemAbelian)),
      P ≤ Mbar D.M V₀ V c.hyp125.isElemAbelian →
        (P.subgroupOf (Mbar D.M V₀ V c.hyp125.isElemAbelian)).Normal → IsPGroup 2 P → P = ⊥ :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D c.hyp125 hP hN h2
  have hYne : Mbar D.M V₀ V c.hyp125.isElemAbelian ≠ ⊥ := by
    intro hbot
    exact hLbar_ne (le_bot_iff.1 (hbot ▸ hKY))
  have hbasic := TwelveSeventeen.isBasicModule D hx h61 h127 h1214 c.hyp125 hYne
  have hfix := s15_Kbar_fixV_eq_bot_of_ne_bot c.hyp125 h0 hKY hKn hLbar_ne
  have hWsq := s15_Infra_vtil_sq_eq_one V₀ V c.hyp125.isElemAbelian
  have hirr := isIrrOn_of_isSU3_two_of_mParam_le_six h128 hWsq hKY hKn hcomp hSU hO2 hbasic
    hfix hm6
  have hYN : Mbar D.M V₀ V c.hyp125.isElemAbelian ≤
      Subgroup.normalizer (barSub V₀ V c.hyp125.isElemAbelian L :
        Set (MulAut (Vtil V₀ V c.hyp125.isElemAbelian))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).1 hKn
  have hAbM : barSub V₀ V c.hyp125.isElemAbelian A ≤ Mbar D.M V₀ V c.hyp125.isElemAbelian :=
    barSub_mono V₀ V c.hyp125.isElemAbelian hAM
  have hAel : IsElemAbelian 2 (barSub V₀ V c.hyp125.isElemAbelian A) :=
    IsElemAbelian.map (IsElemAbelian.comap hA (stabTil V₀ V).subtype_injective)
      (actTil V₀ V c.hyp125.isElemAbelian)
  have hcard := card_le_eight_of_isIrrOn_isSU3_two hWsq hSU hirr (hAbM.trans hYN)
    (fun a ha => by simpa using hAel.2 a ha)
  rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup hAel.isPGroup] at hcard
  by_contra hgt
  have h16 : 2 ^ 4 ≤ 2 ^ CFSG.Quasithin.rk ↥(barSub V₀ V c.hyp125.isElemAbelian A) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem gap17_35_1_nTwo_of_V0
    (D : Data G) (V₀ V : Subgroup G)
    (h34 : R17_34At D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D)
    (h127 : R127 D) (h1114 : R1114 D) (h1214 : F12.R1214 D) (h128 : W4Lem12_8)
    (h117 : C117 D V₀ V) (hSyl : UCK.U3Syl)
    (h162 : W3Thm162Gt2 G) (h183 : W3Thm183 G) (h161 : W16One G)
    (h36a : V₀ ≠ ⊥ → R17_36aAt D V₀ V)
    (hG : Gap17_35_1_nTwoV0 D V₀ V) : Gap17_35_1_nTwo D V₀ V := by
  intro L c h0 hk2
  have hle : mBar D.M V₀ V c.hyp125.isElemAbelian ≤ 2 * 2 + 2 := by
    have h := h34.2.1 L 2 c
    omega
  by_contra hge
  by_cases h3 : 3 ≤ mSub V₀
  · exact hge (hG L c hk2 h3)
  · refine s17_false_of_rk_barSub_add_lt D hx h61 h66 h127 h1114 h162 h183 h161 c.hyp125 h0
      (by omega) ?_
    intro g _ hAT
    have hrk := s17_rk_barSub_le_three D hx h61 h127 h1214 h128 c h117 hSyl h0 (h36a h0) hle
      (hAT.trans D.sylowM.le) (E3.isElemAbelian_conjSubgroup c.hyp125.isElemAbelian g)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
