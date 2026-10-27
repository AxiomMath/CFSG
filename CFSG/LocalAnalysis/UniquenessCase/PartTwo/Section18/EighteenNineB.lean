module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNineProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Ctx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClA
public import CFSG.Goldschmidt.Steps.G55Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU44TwoNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

section Certified


theorem not_p18_6_6_of_eq_bot {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h1742 : S17.R17_42At D V₀ V) (hK : Inputs1719.K_SU44_TwoNat)
    (h : Hyp18 D V₀ V p L) (hV₀ : V₀ = ⊥) : ¬ P18_6_6 D V₀ V p L h := by
  rintro ⟨hSU, hNat⟩
  subst hV₀
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  obtain ⟨hXL, -, -, hcong⟩ := isU4_barSub_cong h h1742 (isU4_of_isSUn_four hSU)
  have hp5 : p = 5 := by
    have h5 : (p : ℤ) ∣ 5 := by
      have := hcong.symm.dvd
      norm_num at this
      exact this
    exact (Nat.prime_dvd_prime_iff_eq h.p_prime (by norm_num)).1 (Int.natCast_dvd_natCast.mp h5)
  have hXY : barSub ⊥ V hV (conjClosure D.M L) ≤ Mbar D.M ⊥ V hV :=
    barSub_mono ⊥ V hV h.X_le_M
  have hYN : Mbar D.M ⊥ V hV ≤
      normalizer (barSub ⊥ V hV (conjClosure D.M L) : Set (MulAut (Vtil ⊥ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).1
      (barSub_subgroupOf_mbar_normal hV h.X_le_M
        (TwelveTwentyThree.le_normalizer_conjClosure D.M L))
  obtain ⟨hm8, hA7, hFF, hZS⟩ :=
    hK (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV) _ _ hXY hYN hSU hNat
  have hV1 : InCalV1 D.M D.T V := by
    rcases h.hyp125.1 with ⟨hW, -⟩ | ⟨h0, -⟩
    · exact hW.1.1
    · exact absurd rfl h0.1.1
  have hm7 : MBarGT D.M ⊥ V 7 := (h.hyp125.mBarGT_iff_lt_mBar 7).2 (by
    show 7 < CFSG.Quasithin.E3.mParam _
    omega)
  have hr : ((7 : ℕ) : ℕ∞) < rMV D.M V :=
    h111 D.M V _ (TwelveShort.setting11_of_inCalV1 D hV1)
      (TwelveShort.mBarGT_mono hm7 (by norm_num)) 7 hm7
  have hβ : ∀ n : ℕ, ((7 : ℕ) : ℕ∞) < betaN n D.M V := by
    intro n
    have h1 := CFSG.LocalAnalysis.WeakClosure81.mParam_autI_top_le_betaN hV
      (normalizer_eq_of_inCalV D hV1.1) n
    have h2 := (TwelveShort.mBarGT_bot_iff_lt_mParam_autI D hV1.1 7).1 hm7
    exact lt_of_lt_of_le (by exact_mod_cast h2) h1
  have step1 : ∀ g : G, CFSG.Quasithin.conjSubgroup V g ≤ D.M →
      ⁅V, CFSG.Quasithin.conjSubgroup V g⁆ = ⊥ := by
    intro g hVgM
    by_cases hVM : V ≤ CFSG.Quasithin.conjSubgroup D.M g
    ·
      by_contra hnc
      have hFF' : ¬ CFSG.Quasithin.IsFFModule (CFSG.Quasithin.autI hV ⊤) := by
        intro hff
        apply hFF
        change CFSG.Quasithin.IsFFModule (barSub ⊥ V hV D.M)
        rw [TwelveTwentyThree.barSub_bot_eq_map_autI V hV D.M,
          ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.autI_top_eq_of_normalizer_eq hV
            (normalizer_eq_of_inCalV D hV1.1)]
        exact CFSG.Quasithin.E3.isFFModule_map_congr (TwelveShort.mkTilEquiv V hV) hff
      have hgN : CFSG.Quasithin.conjSubgroup V g ≤ normalizer (V : Set G) := by
        rw [normalizer_eq_of_inCalV D hV1.1]
        exact hVgM
      have hVN : V ≤ normalizer (CFSG.Quasithin.conjSubgroup V g : Set G) := by
        rw [← CFSG.Quasithin.E3.conjSubgroup_normalizer V g,
          normalizer_eq_of_inCalV D hV1.1]
        exact hVM
      exact CFSG.Quasithin.E3.e3_11 hV hFF' hgN hnc hVN
    ·
      have hP := h.hyp125.pairFacts
      have hAM : CFSG.Quasithin.conjSubgroup V g ≤ D.M := hVgM
      have hAst : CFSG.Quasithin.conjSubgroup V g ≤ stabTil ⊥ V :=
        hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
      have hAel : IsElemAbelian 2 (CFSG.Quasithin.conjSubgroup V g) :=
        CFSG.Quasithin.E3.isElemAbelian_conjSubgroup hV g
      have hall : ∀ B : Subgroup G, B ≤ CFSG.Quasithin.conjSubgroup V g →
          CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B < 8 →
          V ⊓ centralizer (B : Set G) =
            V ⊓ centralizer (CFSG.Quasithin.conjSubgroup V g : Set G) := by
        intro B hB hlt
        have hmB : CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B ≤ 7 := by
          omega
        have hBM : B ≤ CFSG.Quasithin.conjSubgroup V g ⊓ D.M :=
          le_inf hB (hB.trans hVgM)
        have hr' : ((CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B +
            mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
          rw [show mSub (⊥ : Subgroup G) = 0 from CFSG.Quasithin.rk_bot, add_zero]
          exact lt_of_le_of_lt (by exact_mod_cast hmB) hr
        have hβ' : (CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B : ℕ∞) <
            betaN (CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g)
              (CFSG.Quasithin.conjSubgroup V g ⊓ D.M)) D.M V := by
          have h0 : CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g)
              (CFSG.Quasithin.conjSubgroup V g ⊓ D.M) = 0 := by
            rw [inf_eq_left.2 hVgM, CFSG.Quasithin.E3.mQuot_self]
          rw [h0]
          exact lt_of_le_of_lt (by exact_mod_cast hmB) (hβ 0)
        have hcomm := CFSG.LocalAnalysis.WeakClosure81.six_two_three h.hyp125.hyp62
          hBM hr' hVM hβ'
        refine le_antisymm ?_ (inf_le_inf_left V (Subgroup.centralizer_le hB))
        rw [inf_eq_left.2 hVgM] at hcomm
        exact le_inf inf_le_left (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
      by_cases hbar : barSub ⊥ V hV (CFSG.Quasithin.conjSubgroup V g) = ⊥
      ·
        have hC : CFSG.Quasithin.conjSubgroup V g ≤
            F11.CTilde D.M ⊥ V :=
          (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer
            hP.le_normalizer₀ hAM).1 hbar
        rw [uc22p22u_cTilde_bot] at hC
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hC.trans inf_le_right)
      ·
        have hA8 : barSub ⊥ V hV (CFSG.Quasithin.conjSubgroup V g) ∈
            calABar 8 D.M ⊥ V hV :=
          s16c167_barSub_mem_calABar_of_le hV rfl hAM hAst hAel hbar hall
        have hA7mem : barSub ⊥ V hV (CFSG.Quasithin.conjSubgroup V g) ∈
            CFSG.Quasithin.E3.aSet 7 (Mbar D.M ⊥ V hV) :=
          CFSG.Quasithin.E3.aSet_anti (by norm_num) (Mbar D.M ⊥ V hV) hA8
        rw [hA7] at hA7mem
        exact absurd hA7mem (by simp)
  have hstep1 : CFSG.Quasithin.E3.wClos V 0 D.T ≤ centralizer (V : Set G) := by
    refine CFSG.Quasithin.E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := CFSG.Quasithin.E3.mem_gammaSet_iff.1 hA
    have hVg2 : IsPGroup 2 (CFSG.Quasithin.conjSubgroup V g) :=
      (CFSG.Quasithin.E3.isElemAbelian_conjSubgroup hV g).isPGroup
    have hAeq : A = CFSG.Quasithin.conjSubgroup V g :=
      (CFSG.Quasithin.E3.mQuot_eq_zero_iff hVg2 hAg).1 hm
    have hVgM : CFSG.Quasithin.conjSubgroup V g ≤ D.M :=
      hAeq ▸ hAT.trans D.sylowM.le
    rw [hAeq]
    have hcomm' : ⁅CFSG.Quasithin.conjSubgroup V g, V⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact step1 g hVgM
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm'
  have hW0 : normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) ≤ D.M := by
    have hW0eq : CFSG.Quasithin.E3.wClos V 0 D.T =
        CFSG.Quasithin.E3.wClos V 0 (D.T ⊓ centralizer (V : Set G)) := by
      refine le_antisymm ?_ (CFSG.Quasithin.E3.wClos_mono inf_le_left)
      refine CFSG.Quasithin.E3.wClos_le_of_forall fun A hA =>
        CFSG.Quasithin.E3.le_wClos ?_
      obtain ⟨hAT, g, hAg, hm⟩ := CFSG.Quasithin.E3.mem_gammaSet_iff.1 hA
      exact CFSG.Quasithin.E3.mem_gammaSet_iff.2
        ⟨le_inf hAT ((CFSG.Quasithin.E3.le_wClos hA).trans hstep1), g, hAg, hm⟩
    have hN := CFSG.Quasithin.E3.normalizer_le_normalizer_wClos (V := V) (i := 0)
      (D.T ⊓ centralizer (V : Set G))
    rw [← hW0eq] at hN
    refine CFSG.LocalAnalysis.WeakClosure81.normalizer_le_of_uniqueMax hV1.2 ?_ ?_
      (inf_le_right.trans hN)
    · intro hbot
      exact h.hyp125.pairFacts.ne_bot
        (le_bot_iff.1 ((s15_13A_le_wClos h.hyp125).trans_eq hbot))
    · exact D.sylowM.isPGroup.to_le (CFSG.Quasithin.E3.wClos_le 0 D.T)
  have step2 : ∀ A ∈ CFSG.Quasithin.E3.gammaSet V 2 D.T, barSub ⊥ V hV A ≠ ⊥ →
      barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV := by
    intro A hA hAbar
    have hP := h.hyp125.pairFacts
    obtain ⟨hAT, g, hAg, hm⟩ := CFSG.Quasithin.E3.mem_gammaSet_iff.1 hA
    have hAM : A ≤ D.M := hAT.trans D.sylowM.le
    have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
    have hAel : IsElemAbelian 2 A :=
      CFSG.Quasithin.B2F.isElemAbelian_mono hAg
        (CFSG.Quasithin.E3.isElemAbelian_conjSubgroup hV g)
    have hVg : ¬ V ≤ CFSG.Quasithin.conjSubgroup D.M g := by
      intro hVM
      have hVM' : CFSG.Quasithin.conjSubgroup V g⁻¹ ≤ D.M := by
        have h1 := CFSG.Quasithin.E3.conjSubgroup_mono_left g⁻¹ hVM
        rwa [CFSG.Quasithin.E3.conjSubgroup_conj_inv] at h1
      have hcomm := step1 g⁻¹ hVM'
      have hcommg : ⁅V, CFSG.Quasithin.conjSubgroup V g⁆ = ⊥ := by
        have h' := congrArg (fun C => CFSG.Quasithin.conjSubgroup C g) hcomm
        simp only [CFSG.Quasithin.E3.conjSubgroup_commutator,
          CFSG.Quasithin.E3.conjSubgroup_inv_conj,
          CFSG.Quasithin.E3.conjSubgroup_bot] at h'
        rw [Subgroup.commutator_comm]
        exact h'
      have hAC : A ≤ centralizer (V : Set G) := by
        have h1 : ⁅V, A⁆ = ⊥ := by
          exact le_bot_iff.1 ((Subgroup.commutator_mono (le_refl V) hAg).trans
            (le_of_eq hcommg))
        exact Subgroup.le_centralizer_iff.1
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)
      refine hAbar ((CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV
        hP.le_normalizer hP.le_normalizer₀ hAM).2 ?_)
      rw [uc22p22u_cTilde_bot]
      exact le_inf hAM hAC
    have hall : ∀ B : Subgroup G, B ≤ A → CFSG.Quasithin.E3.mQuot A B < 6 →
        V ⊓ centralizer (B : Set G) = V ⊓ centralizer (A : Set G) := by
      intro B hBA hlt
      have hBVg : B ≤ CFSG.Quasithin.conjSubgroup V g := hBA.trans hAg
      have hBM : B ≤ CFSG.Quasithin.conjSubgroup V g ⊓ D.M :=
        le_inf hBVg (hBA.trans hAM)
      have hmB : CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B ≤ 7 := by
        rw [CFSG.Quasithin.E3.mQuot_add hBA hAg, hm]
        omega
      have hr' : ((CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B +
          mSub (⊥ : Subgroup G) : ℕ) : ℕ∞) < rMV D.M V := by
        rw [show mSub (⊥ : Subgroup G) = 0 from CFSG.Quasithin.rk_bot, add_zero]
        exact lt_of_le_of_lt (by exact_mod_cast hmB) hr
      have hβ' : (CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g) B : ℕ∞) <
          betaN (CFSG.Quasithin.E3.mQuot (CFSG.Quasithin.conjSubgroup V g)
            (CFSG.Quasithin.conjSubgroup V g ⊓ D.M)) D.M V :=
        lt_of_le_of_lt (by exact_mod_cast hmB) (hβ _)
      have hcomm := CFSG.LocalAnalysis.WeakClosure81.six_two_three h.hyp125.hyp62
        hBM hr' hVg hβ'
      refine le_antisymm ?_ (inf_le_inf_left V (Subgroup.centralizer_le hBA))
      exact le_inf inf_le_left (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (le_bot_iff.1 ((Subgroup.commutator_mono (le_refl (V ⊓ centralizer (B : Set G)))
          (le_inf hAg hAM)).trans (le_of_eq hcomm))))
    have hA6 : barSub ⊥ V hV A ∈ calABar 6 D.M ⊥ V hV :=
      s16c167_barSub_mem_calABar_of_le hV rfl hAM hAst hAel hAbar hall
    exact CFSG.Quasithin.E3.aSet_anti (by norm_num) (Mbar D.M ⊥ V hV) hA6
  obtain ⟨Z, hZne, hZA, E, hEXZ, hE5, hEcard⟩ :=
    hZS _ (S17.isSylowIn_barSub_sylow D hV fun m hm =>
      ⟨h.hyp125.pairFacts.le_normalizer hm, h.hyp125.pairFacts.le_normalizer₀ hm⟩)
  have hZC : preTil ⊥ V hV Z ≤ CFSG.Quasithin.E3.cClos V 2 D.T := by
    have hVT : V ≤ D.T := uc22p22p_le_T_of_inCalV D hV1.1
    refine le_inf ((preTil_le ⊥ V hV Z).trans hVT) ?_
    have hstep : ∀ A : {A // A ∈ CFSG.Quasithin.E3.gammaSet V 2 D.T},
        preTil ⊥ V hV Z ≤ Subgroup.centralizer (A.1 : Set G) := by
      rintro ⟨A, hA⟩
      have hP := h.hyp125.pairFacts
      obtain ⟨hAT, g, hAg, hm⟩ := CFSG.Quasithin.E3.mem_gammaSet_iff.1 hA
      have hAM : A ≤ D.M := hAT.trans D.sylowM.le
      have hAst : A ≤ stabTil ⊥ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
      by_cases hAbar : barSub ⊥ V hV A = ⊥
      ·
        have hC : A ≤ F11.CTilde D.M ⊥ V :=
          (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV hP.le_normalizer
            hP.le_normalizer₀ hAM).1 hAbar
        rw [uc22p22u_cTilde_bot] at hC
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hxV : x ∈ V := preTil_le ⊥ V hV Z hx
        exact (Subgroup.mem_centralizer_iff.1 ((hC.trans inf_le_right) ha) x hxV).symm
      ·
        have hA2 : barSub ⊥ V hV A ∈ calABar 2 D.M ⊥ V hV := step2 A hA hAbar
        have hAleS : barSub ⊥ V hV A ≤ barSub ⊥ V hV D.T := barSub_mono ⊥ V hV hAT
        have hZfix : Z ≤ CFSG.Quasithin.fixV (barSub ⊥ V hV A) := hZA _ hA2 hAleS
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have hxV : x ∈ V := preTil_le ⊥ V hV Z hx
        have hxZ : mkTil ⊥ V hV (CFSG.Quasithin.IntMod.mk hV ⟨x, hxV⟩) ∈ Z :=
          (mem_preTil_iff_of_mem ⊥ V hV Z hxV).1 hx
        have hfix : mkTil ⊥ V hV (CFSG.Quasithin.IntMod.mk hV ⟨x, hxV⟩) ∈
            CFSG.Quasithin.fixV (barSub ⊥ V hV A) := hZfix hxZ
        have hcomm : a * x * a⁻¹ = x :=
          (s16c7_mem_fixV_barSub_iff V hV hAst (CFSG.Quasithin.IntMod.mk hV ⟨x, hxV⟩)).1 hfix a ha
        have hxa : a * x = x * a := by
          have := congrArg (fun y => y * a) hcomm
          simpa [mul_assoc] using this
        exact hxa
    have h := CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun A : {A // A ∈ CFSG.Quasithin.E3.gammaSet V 2 D.T} => (A.1 : Subgroup G)) hstep
    have hw : (⨆ A : {A // A ∈ CFSG.Quasithin.E3.gammaSet V 2 D.T},
        (A.1 : Subgroup G)) = CFSG.Quasithin.E3.wClos V 2 D.T := by
      rw [CFSG.Quasithin.E3.wClos, iSup_subtype]
    rw [hw] at h
    exact h
  have hNZ : normalizer (preTil ⊥ V hV Z : Set G) ≤ D.M := by
    have hP := h.hyp125.pairFacts
    have hEM : E ≤ Mbar D.M ⊥ V hV :=
      hEXZ.trans (inf_le_left.trans (barSub_mono ⊥ V hV h.X_le_M))
    have hEstab : E ≤ CFSG.Quasithin.stabSub Z := hEXZ.trans inf_le_right
    let C : Subgroup G := preBarSub D.M ⊥ V hV E
    have hCM : C ≤ D.M := fun c hc => (mem_preBarSub D.M ⊥ V hV E).1 hc |>.1
    have hCstab : C ≤ stabTil ⊥ V :=
      hCM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
    let φ : ↥C →* ↥E :=
      ((actTil ⊥ V hV).comp (Subgroup.inclusion hCstab)).codRestrict E (fun c => by
        obtain ⟨-, h, hE⟩ := (mem_preBarSub D.M ⊥ V hV E).1 c.2
        have hEq : (Subgroup.inclusion hCstab c) = (⟨(c : G), h⟩ : stabTil ⊥ V) :=
          Subtype.ext rfl
        change actTil ⊥ V hV (Subgroup.inclusion hCstab c) ∈ E
        rw [hEq]
        exact hE)
    have hφ : Function.Surjective φ := by
      intro e
      obtain ⟨m, hmM, hme⟩ :=
        (mem_barSub ⊥ V hV D.M (e : MulAut (Vtil ⊥ V hV))).1 (hEM e.2)
      have hmC : (m : G) ∈ C := by
        refine (mem_preBarSub D.M ⊥ V hV E).2 ⟨hmM, m.2, ?_⟩
        rw [hme]
        exact e.2
      refine ⟨⟨m, hmC⟩, ?_⟩
      apply Subtype.ext
      show actTil ⊥ V hV (Subgroup.inclusion hCstab ⟨m, hmC⟩) =
        (e : MulAut (Vtil ⊥ V hV))
      rw [show Subgroup.inclusion hCstab ⟨m, hmC⟩ = m from Subtype.ext rfl]
      exact hme
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hEnc : ¬ IsCyclic E :=
      CFSG.Goldschmidt.G55.not_isCyclic_of_isElemAbelian (by norm_num) hE5
        (by rw [hEcard]; norm_num)
    have htop5 : IsPGroup 5 (⊤ : Subgroup ↥E) :=
      hE5.isPGroup.of_equiv (Subgroup.topEquiv.symm : ↥E ≃* ↥(⊤ : Subgroup ↥E))
    have htopnc : ¬ IsCyclic (⊤ : Subgroup ↥E) :=
      fun hc => hEnc ((MulEquiv.isCyclic Subgroup.topEquiv).1 hc)
    obtain ⟨X, -, hXp, hXc⟩ :=
      SpLift.exists_noncyclic_pSubgroup_le φ hφ (p := 5) (K := ⊤) (by simp)
        htop5 htopnc
    let P : Subgroup G := X.map C.subtype
    have hPM : P ≤ D.M := (Subgroup.map_subtype_le X).trans hCM
    have hP5 : IsPGroup 5 P := hXp.map C.subtype
    have hPnc : ¬ IsCyclic P :=
      SpLift.not_isCyclic_map C.subtype (Subgroup.subtype_injective C) hXc
    have hCN : C ≤ normalizer (preTil ⊥ V hV Z : Set G) := by
      have hbarC : barSub ⊥ V hV C = E := by
        rw [show C = preBarSub D.M ⊥ V hV E from rfl, barSub_preBarSub,
          inf_eq_left.2 hEM]
      have hS : StableUnder (Mbar C ⊥ V hV) Z := by
        intro e he u hu
        have he' : e ∈ barSub ⊥ V hV C := he
        exact (CFSG.Quasithin.mem_stabSub.1 (hEstab (hbarC ▸ he')) u).2 hu
      exact TwelveSeventeen.le_normalizer_preTil hV hCstab hS
    have hPN : P ≤ normalizer (preTil ⊥ V hV Z : Set G) :=
      (Subgroup.map_subtype_le X).trans hCN
    have hQne : preTil ⊥ V hV Z ≠ ⊥ := by
      intro hbot
      apply hZne
      have h1 := imgTil_preTil ⊥ V hV Z
      rw [hbot, TwelveSeventeen.imgTil_bot] at h1
      exact h1.symm
    have hQ2 : IsPGroup 2 (preTil ⊥ V hV Z) :=
      hV.isPGroup.to_le (preTil_le ⊥ V hV Z)
    exact normalizer_le_of_noncyclic D h61 (hp5 ▸ h.hp) hPM hP5 hPnc hQne hQ2 hPN
  have hC : centralizer (CFSG.Quasithin.E3.cClos V (D.k + 0) D.T : Set G) ≤ D.M := by
    have hmBar8 : 8 ≤ mBar D.M ⊥ V hV := hm8
    have hrk : 2 < CFSG.Quasithin.rk ↥V := by
      have h1 : mBar D.M ⊥ V hV ≤ CFSG.Quasithin.rk ↥V :=
        CFSG.LocalAnalysis.WeakClosure81.mBar_le_rk hV h.hyp125.pairFacts.le
      omega
    have hk : D.k + 0 ≤ 2 := by
      have : D.k ≤ 2 := TwelveSeven.k_le_two D
      omega
    have hanti : CFSG.Quasithin.E3.cClos V 2 D.T ≤
        CFSG.Quasithin.E3.cClos V (D.k + 0) D.T :=
      CFSG.LocalAnalysis.WeakClosure81.cClos_anti hV hk hrk D.T
    exact (Subgroup.centralizer_le hanti).trans
      ((Subgroup.centralizer_le hZC).trans
        ((Subgroup.centralizer_le_normalizer (preTil ⊥ V hV Z : Set G)).trans hNZ))
  have hm : MBarGT D.M ⊥ V (D.k + 0) := TwelveShort.mBarGT_mono hm7 (by
    have : D.k ≤ 2 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      split_ifs <;> norm_num
    omega)
  rcases twelve_ten_two D hx h61 h126 h111 h.hyp125 rfl hm with h1 | h1
  · exact h1 hW0
  · exact h1 hC

theorem false_of_isU4_two_of_ne_bot {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (h1742 : S17.R17_42At D V₀ V)
    (hKU : Inputs1719.KU4U5CartanQuotient) (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (h : Hyp18 D V₀ V p L) (hV₀ : V₀ ≠ ⊥)
    (hU4 : IsU4 ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) 2) : False := by
  obtain ⟨hXL, -, -, -⟩ := isU4_barSub_cong h h1742 hU4
  have hs : IsSimpleGroup ↥(barSub V₀ V h.hyp125.isElemAbelian (conjClosure D.M L)) :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU4
  obtain ⟨-, ⟨e⟩⟩ := conjClosure_eq_and_bar2_equiv_of_hyp18 h hs
  have hU4L : IsU4 (Bar2 L) 2 := by
    have hU1 := hU4
    rw [hXL] at hU1
    exact LieModel.of_mulEquiv e.symm hU1
  have hLM : L ≤ D.M := (S17.calLp_subset_calC D p h.hL).1.le
  have hLn : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 (by
      rw [← hXL]
      exact TwelveTwentyThree.le_normalizer_conjClosure D.M L)
  have hTM : CFSG.Quasithin.IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hSylL : CFSG.Quasithin.IsSylowIn 2 (D.T ⊓ L) L := hTM.inf_normal hLM hLn
  have hTY : D.T ≤ normalizer (L : Set G) :=
    D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hLn)
  obtain ⟨hQcomm, E9, hE9, hE9card⟩ :=
    S19.cartanQuotient_of_KU4U5 hKU (Or.inr hU4L) le_rfl even_two hSylL
  have hns := S19.not_isStronglyPEmbedded_of_normalizerQuotient h.hyp125 hV₀
    (h171 h.hyp125) hLM hTY hSylL hQcomm.is_comm.comm hE9 hE9card
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  have h8102 : F08.Hyp8102 D L P p 2 :=
    ⟨S17.calLp_subset_calC D p h.hL, Or.inr hU4L, hns, h.hp, hP⟩
  obtain ⟨B, hB⟩ := (h8103 L P p 2 h8102).2.2.2.2.1
  have hbot := h8106 L P p 2 h8102 B hB
  have hV0 : InCalV D.M V₀ := by
    rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact absurd h0 hV₀
    · exact h0.1
  obtain ⟨-, hV0M, hV0N, hV0el⟩ := hV0
  have hcore : V₀ ≤ pCoreOf 2 D.M := by
    have hnorm : (V₀.subgroupOf D.M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hV0M).2 hV0N
    have hp2 : IsPGroup 2 (V₀.subgroupOf D.M) := hV0el.subgroupOf D.M |>.isPGroup
    have hle : V₀.subgroupOf D.M ≤ CFSG.pCore 2 ↥D.M := le_sSup ⟨hnorm, hp2⟩
    calc V₀ = (V₀.subgroupOf D.M).map D.M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hV0M).symm
      _ ≤ (CFSG.pCore 2 ↥D.M).map D.M.subtype := Subgroup.map_mono hle
      _ = pCoreOf 2 D.M := rfl
  have hcard : Nat.card V₀ = 2 := by
    have h1 := (mSub_le_one_iff hV0el).1 h.small
    have h2 := (Subgroup.one_lt_card_iff_ne_bot V₀).2 hV₀
    omega
  have hPL : P ≤ L := by
    obtain ⟨Q, hQ⟩ := hP
    rw [← hQ]
    exact Subgroup.map_subtype_le _
  have hBM : B ≤ D.M := hB.2.1.trans (hPL.trans hLM)
  have hcent : V₀ ≤ centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hw : b * v * b⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 (hV0N (hBM hb)) v).1 hv
    by_cases hv1 : v = 1
    · simp [hv1]
    · have hw1 : b * v * b⁻¹ ≠ 1 := by
        intro h1
        apply hv1
        calc v = b⁻¹ * (b * v * b⁻¹) * b := by group
          _ = 1 := by rw [h1]; group
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥V₀)).1 hcard
      have e1 : (⟨b * v * b⁻¹, hw⟩ : ↥V₀) = y :=
        hy _ (fun h0 => hw1 (congrArg Subtype.val h0))
      have e2 : (⟨v, hv⟩ : ↥V₀) = y := hy _ (fun h0 => hv1 (congrArg Subtype.val h0))
      have e3 : b * v * b⁻¹ = v := congrArg Subtype.val (e1.trans e2.symm)
      calc b * v = b * v * b⁻¹ * b := by group
        _ = v * b := by rw [e3]
  have hle : V₀ ≤ pCoreOf 2 D.M ⊓ centralizer (B : Set G) := le_inf hcore hcent
  rw [hbot] at hle
  exact hV₀ (le_bot_iff.1 hle)

theorem not_p18_6_6_of_ne_bot {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (h1742 : S17.R17_42At D V₀ V)
    (hKU : Inputs1719.KU4U5CartanQuotient) (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (h : Hyp18 D V₀ V p L) (hV₀ : V₀ ≠ ⊥) : ¬ P18_6_6 D V₀ V p L h := by
  rintro ⟨hSU, -⟩
  exact false_of_isU4_two_of_ne_bot h171 h1742 hKU h8103 h8106 h hV₀
    (isU4_of_isSUn_four hSU)

theorem r18_9b {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (h1742 : S17.R17_42At D V₀ V)
    (hKU : Inputs1719.KU4U5CartanQuotient) (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (hK : Inputs1719.K_SU44_TwoNat) (h : Hyp18 D V₀ V p L) : Gap_18_9b D V₀ V p L h := by
  by_cases hV₀ : V₀ = ⊥
  · exact not_p18_6_6_of_eq_bot hx h61 h126 h111 h1742 hK h hV₀
  · exact not_p18_6_6_of_ne_bot h171 h1742 hKU h8103 h8106 h hV₀

theorem eighteen_thirteen_c {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hm : MBarGT D.M V₀ V 3)
    (h6b : R18_6bAt D V₀ V p L h) (h7b : R18_7bAt D V₀ V p L h)
    (h8 : R18_8At D V₀ V p L h) (h9 : R18_9At D V₀ V p L h)
    (h10 : R18_10At D V₀ V p L h) (h11 : R18_11At D V₀ V p L h)
    (h12 : R18_12At D V₀ V p L h)
    (h17_66_1 : S17.R17_66_1At D V₀ V) (h18_4 : R18_4At D V₀ V p L)
    (h117 : C117 D V₀ V) (hH1 : K_18_13_H1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D)
    (h1742 : S17.R17_42At D V₀ V)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h171 : ∀ hV : Hyp125 D V₀ V, S17.R17_1At D V₀ V hV)
    (hKU : Inputs1719.KU4U5CartanQuotient) (h8103 : F08.R8103 D) (h8106 : F08.R8106 D)
    (hK : Inputs1719.K_SU44_TwoNat) :
    R18_13At D V₀ V p L h :=
  eighteen_thirteen_b h hm h6b h7b h8 h9
    (r18_9b hx h61 h126 h111 h171 h1742 hKU h8103 h8106 hK h) h10 h11 h12
    h17_66_1 h18_4 h117 hH1 hx h61 h127 h1214 h1742

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
