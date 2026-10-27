module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx
public import CFSG.GroupTheory.GF4Scalar
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyEight
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise
open CFSG.GroupTheory (gf4Linear_of_mem_aSet_two_of_omega even_mQuot_fixV_of_gf4)

variable {G : Type} [Group G] [Finite G]

@[expose] def K_OmegaPlusFour_twoNat_inv : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ X H : Subgroup (MulAut W), X ≤ H → H ≤ Subgroup.normalizer (X : Set (MulAut W)) →
      IsOmegaPlus ↥X 4 2 →
      SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 →
      ∀ w ∈ H, w ≠ 1 → w ^ 2 = 1 →
        E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers w)) = 4 →
        (∀ c ∈ H ⊓ Subgroup.centralizer (X : Set (MulAut W)), c * w = w * c) ∧
        5 ∣ Nat.card ↥(X ⊓ Subgroup.centralizer ({w} : Set (MulAut W))) ∧
        ∀ y ∈ H, (∀ v ∈ CFSG.Quasithin.fixV (Subgroup.zpowers w), y v = v) → y = 1 ∨ y = w

@[expose] def K_OmegaPlusFour_twoNat_scalar : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ X : Subgroup (MulAut W),
    IsOmegaPlus ↥X 4 2 →
    SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 →
    (∃ t ∈ Subgroup.normalizer (X : Set (MulAut W)), orderOf t = 2 ∧
      E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4) →
      ∃ ω ∈ Subgroup.centralizer (X : Set (MulAut W)),
        (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * ω = ω * c) ∧
        orderOf ω = 3 ∧ (∀ v : W, ω v = v → v = 1) ∧
        (∀ z ∈ Subgroup.centralizer (X : Set (MulAut W)),
          (∀ c ∈ Subgroup.centralizer (X : Set (MulAut W)), c * z = z * c) →
            z ∈ Subgroup.zpowers ω)

theorem gap_18_4_ii_aSet (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (X : Subgroup (MulAut (Vtil ⊥ V hV)))
    (hW0 : E3.wClos V 0 D.T ≤ Subgroup.centralizer (V : Set G)) :
    Hyp125 D ⊥ V → IsOmegaPlus ↥X 4 2 →
    SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2 →
    mBar D.M ⊥ V hV = 4 → (4 : ℕ∞) < rMV D.M V →
    ∀ A ∈ F12.Gam 2 D.T V, barSub ⊥ V hV A ≠ ⊥ →
      barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV := by
  intro hp125 _hX _hsum hm4 hr4 A hA hAbar
  have hAgam : A ∈ E3.gammaSet V 2 D.T := by
    rw [← S17.gam_eq_gammaSet 2 D.T V hV]
    exact hA
  obtain ⟨hAT, g, hAg, hmQ⟩ := E3.mem_gammaSet_iff.1 hAgam
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  have hAne : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun h =>
    hAbar ((S17.barSub_bot_iff_le_centralizer hp125 hAM).2 h)
  have hVgM : ¬ V ≤ conjSubgroup D.M g :=
    S17.not_le_conjSubgroup_of_mem_gammaTwo hp125 hW0 hAgam hAne hAg
  have hbeta : ∀ n : ℕ, (3 : ℕ∞) < betaN n D.M V := by
    intro n
    have hm4' : mBar D.M ⊥ V hp125.isElemAbelian = 4 := hm4
    have hm3 : MBarGT D.M ⊥ V 3 := (hp125.mBarGT_iff_lt_mBar 3).2 (by omega)
    have h3 : 3 < E3.mParam (autI hV ⊤) :=
      (TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hp125.inCalV 3).1 hm3
    have h4 : (4 : ℕ) ≤ E3.mParam (autI hV ⊤) := by omega
    have h4' : (4 : ℕ∞) ≤ (E3.mParam (autI hV ⊤) : ℕ∞) := by exact_mod_cast h4
    exact lt_of_lt_of_le (by norm_num : (3 : ℕ∞) < 4)
      (h4'.trans (CFSG.LocalAnalysis.WeakClosure81.mParam_autI_top_le_betaN hV
        hp125.normalizer_eq n))
  have hall : ∀ B : Subgroup G, B ≤ A → E3.mQuot A B < 2 →
      V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) := by
    intro B hBA hltB
    have hBM : B ≤ conjSubgroup V g ⊓ D.M := le_inf (hBA.trans hAg) (hBA.trans hAM)
    have hmB : E3.mQuot (conjSubgroup V g) B ≤ 3 := by
      rw [E3.mQuot_add hBA hAg, hmQ]
      omega
    have hr' : ((E3.mQuot (conjSubgroup V g) B + mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) <
        rMV D.M V := by
      rw [show mSub (⊥ : Subgroup G) = 0 from CFSG.Quasithin.rk_bot, add_zero]
      exact lt_of_le_of_lt (by exact_mod_cast hmB)
        (lt_trans (by norm_num : (3 : ℕ∞) < 4) hr4)
    have hβ' : (E3.mQuot (conjSubgroup V g) B : ℕ∞) <
        betaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ D.M)) D.M V :=
      lt_of_le_of_lt (by exact_mod_cast hmB) (hbeta _)
    have hcomm := CFSG.LocalAnalysis.WeakClosure81.six_two_three hp125.hyp62 hBM hr' hVgM hβ'
    have hle : V ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm).trans
        (Subgroup.centralizer_le (le_inf hAg hAM))
    exact le_antisymm (le_inf inf_le_left hle)
      (inf_le_inf_left V (Subgroup.centralizer_le hBA))
  have hMst : D.M ≤ stabTil ⊥ V :=
    le_stabTil hp125.pairFacts.le_normalizer (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hAst : A ≤ stabTil ⊥ V := hAM.trans hMst
  have hAel : IsElemAbelian 2 A :=
    CFSG.Quasithin.B2F.isElemAbelian_mono hAg (E3.isElemAbelian_conjSubgroup hV g)
  exact s16c167_barSub_mem_calABar_of_le hV rfl hAM hAst hAel hAbar hall

variable {W : Type} [CommGroup W] [Finite W]

theorem even_mQuot_fixV_of_mem_aSet_two (hK2 : K_OmegaPlusFour_twoNat_scalar)
    (hW : ∀ w : W, w ^ 2 = 1) {X Y A : Subgroup (MulAut W)}
    (hX : IsOmegaPlus ↥X 4 2)
    (hsum : SumOfNat (fun H U Z => NatOmegaPlus H U Z 4 2) X ⊤ ⊥ 2)
    (ht : ∃ t ∈ Subgroup.normalizer (X : Set (MulAut W)), orderOf t = 2 ∧
      E3.mQuot ⊤ (CFSG.Quasithin.fixV (Subgroup.zpowers t)) = 4)
    (hY : Y ≤ Subgroup.normalizer (X : Set (MulAut W)))
    (hA : A ∈ E3.aSet 2 Y) (B : Subgroup (MulAut W)) (hBA : B ≤ A) :
    ∃ ω ∈ Subgroup.centralizer (X : Set (MulAut W)),
      orderOf ω = 3 ∧ (∀ v : W, ω v = v → v = 1) ∧
        Even (E3.mQuot (fixV B) (fixV B ⊓ fixV A)) := by
  obtain ⟨ω, hωC, hωcentral, hω3, hfree, hcenter⟩ := hK2 W hW X hX hsum ht
  have hAω : A ≤ Subgroup.centralizer ({ω} : Set (MulAut W)) :=
    gf4Linear_of_mem_aSet_two_of_omega hW hcenter hωC hωcentral hω3 hY hA
  have hAω' : ∀ a ∈ A, a * ω = ω * a := by
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hAω ha)) ω (Set.mem_singleton ω)).symm
  have hBω : ∀ b ∈ B, b * ω = ω * b := fun b hb => hAω' b (hBA hb)
  have hMω : (fixV B).map ω.toMonoidHom = fixV B := by
    have hstab : (fixV B).map ω.toMonoidHom ≤ fixV B := by
      rintro x ⟨u, hu, rfl⟩
      change u ∈ fixV B at hu
      change ω u ∈ fixV B
      rw [mem_fixV] at hu ⊢
      intro b hb
      have hcomm : b (ω u) = ω (b u) := by
        have h1 := congrArg (fun f : MulAut W => f u) (hBω b hb)
        simpa only [MulAut.mul_apply] using h1
      change b (ω u) = ω u
      rw [hcomm, hu b hb]
    exact Subgroup.eq_of_le_of_card_ge hstab (le_of_eq
      (Subgroup.card_map_of_injective (MulEquiv.injective ω)).symm)
  exact ⟨ω, hωC, hω3, hfree, even_mQuot_fixV_of_gf4 hW
    (by rw [← hω3]; exact pow_orderOf_eq_one ω) hfree (fixV B) hMω A hAω'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
