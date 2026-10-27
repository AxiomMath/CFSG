module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenThreeHigh
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenOneThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U34ACand
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourCalOOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem barSub_ne_bot_or_19 (D : Data G) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h3 : R19_3At D V₀ V p L K h) :
    barSub V₀ V h.hyp.isElemAbelian L ≠ ⊥ ∨ barSub V₀ V h.hyp.isElemAbelian K ≠ ⊥ := by
  by_contra hc
  simp only [not_or, ne_eq, not_not] at hc
  obtain ⟨hLbot, hKbot⟩ := hc
  have hp125 := h.hyp.hyp125
  have hV := h.hyp.isElemAbelian
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hyp.hL.1.1
  have hKM : K ≤ D.M := CFSG.Quasithin.A3.subnormal_le h.hK.1
  have hLKC₀ : L ⊔ K ≤ centralizer (V₀ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3
  have hLC₀ : L ≤ centralizer (V₀ : Set G) := le_sup_left.trans hLKC₀
  have hKC₀ : K ≤ centralizer (V₀ : Set G) := le_sup_right.trans hLKC₀
  have hLCtilde : L ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV
      hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀ hLM).1 hLbot
  have hKCtilde : K ≤ F11.CTilde D.M V₀ V :=
    (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV
      hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀ hKM).1 hKbot
  have hV₀ab : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hp125.pairFacts.elemAbelian₀.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLC : L ≤ centralizer (V : Set G) :=
    ElevenNine.le_centralizer_of_perfect_of_sub h.hyp.hL.1.2.1 hV₀ab hLC₀ (fun l hl v hv =>
      CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde hV
        hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀ (hLCtilde hl) v hv)
  have hKC : K ≤ centralizer (V : Set G) :=
    ElevenNine.le_centralizer_of_perfect_of_sub h.hK.2.1 hV₀ab hKC₀ (fun k hk v hv =>
      CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde hV
        hp125.pairFacts.le_normalizer hp125.pairFacts.le_normalizer₀ (hKCtilde hk) v hv)
  have hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M :=
    ((calC_commutator_le_of_ne h.hyp.hL.1 h.hK (Ne.symm h.hne)).trans inf_le_left).trans
      (UC22.P22s.pCoreOf_le_of_isSubnormal h.hyp.hL.1.1)
  have hU : UniqueMax D.M (L ⊔ K) :=
    uniqueMax_of_commutator_le_pCoreOf D h61 (h.p_eq ▸ h.hyp.hp) (sup_le hLM hKM) le_sup_left
      le_sup_right hcomm h.hK.2.1 (UC22.InS3.UC49.five_dvd_card_of_isAlt h.hKshape)
      (h.p_eq ▸ h.hyp.hL.2 : 5 ∈ piSet L).2
  have hTI := uc22p22u_isTI_of_uniqueMax D hV hp125.pairFacts.le_normalizer (sup_le hLC hKC) hU
  exact (twelve_nine D h127 hp125).1 hTI

theorem mQuot_dual_eq_of_hyp65
    {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp65 n M V₀ V g) :
    E3.mQuot (conjSubgroup V g) M = E3.mQuot V (conjSubgroup M g) := by
  obtain ⟨l, -, h1, h2⟩ := Hyp65.swapHyp h
  have hUB := h.conjSubgroup_U_eq_B_of_swap h1 h2
  have e1 : E3.mQuot (conjSubgroup V g) M = E3.mQuot (conjSubgroup V g) (BOf M V g) := by
    unfold E3.mQuot BOf
    rw [Subgroup.inf_relIndex_left]
  have e2 : E3.mQuot V (conjSubgroup M g) = E3.mQuot V (UOf M V g) := by
    unfold E3.mQuot UOf
    rw [Subgroup.inf_relIndex_left]
  rw [e1, e2, ← hUB, ← h1, E3.mQuot_conjSubgroup]

theorem false_of_hyp64_of_two_le
    {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h64 : Hyp64 n M V₀ V g) (hV₀ : V₀ ≠ ⊥)
    (h6 : ∀ Y : Subgroup G, Y ≤ M → Odd (Nat.card Y) → ⁅V₀, Y⁆ ≠ ⊥ →
      normalizer (Y : Set G) ≤ M)
    (hd : 2 ≤ E3.mQuot V (conjSubgroup M g)) : False := by
  obtain ⟨Y, ⟨hYle, hYcard, -, -⟩, hYfix⟩ := exists_isFixedPointFreeTorus h64
  have hnotle : ¬ conjSubgroup V g ≤ M := h64.inCalOStar.1.1.1
  have hdU : E3.mQuot V (UOf M V g) = E3.mQuot V (conjSubgroup M g) := by
    unfold E3.mQuot UOf
    rw [Subgroup.inf_relIndex_left]
  set d := E3.mQuot V (conjSubgroup M g) with hd_def
  have hYc : Nat.card Y = 2 ^ d - 1 := by rw [hYcard, hdU]
  have hpow : 4 ≤ 2 ^ d := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hd
    simpa using this
  have hY3 : 3 ≤ Nat.card Y := by omega
  have hYodd : Odd (Nat.card Y) := by
    rw [hYc]
    exact Nat.Even.sub_odd (by omega) (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  set q := (Nat.card Y).minFac with hq_def
  have hq : q.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.Prime := ⟨hq⟩
  have hqY : q ∣ Nat.card Y := Nat.minFac_dvd _
  have hqodd : Odd q := hYodd.of_dvd_nat hqY
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) q hqY
  have hxo : orderOf (x : G) = q := (Subgroup.orderOf_coe x).trans hx
  have hx1 : (x : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxo
    exact hq.one_lt.ne hxo
  set H₀ : Subgroup G := LOf V g ⊓ M ⊓ conjSubgroup M g with hH₀
  have hR₀H : Subgroup.zpowers (x : G) ≤ H₀ := Subgroup.zpowers_le.2 (hYle x.2)
  have hR₀p : IsPGroup q (Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card (show Nat.card (Subgroup.zpowers (x : G)) = q ^ 1 by
      rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨R, hR, hR₀R⟩ := exists_isSylowIn_ge q hR₀H hR₀p
  have hRM : R ≤ M := hR.le.trans (inf_le_left.trans inf_le_right)
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR.isPGroup.exists_card_eq
    rw [hk]
    exact hqodd.pow
  have hcomm : ⁅V₀, R⁆ ≠ ⊥ := by
    intro hbot
    have hV₀C : V₀ ≤ centralizer (R : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
    have hV₀Vg : V₀ ≤ conjSubgroup V g := by
      intro v hv
      have hxv : (x : G) * v * (x : G)⁻¹ = v := by
        have hc := Subgroup.mem_centralizer_iff.1 (hV₀C hv) (x : G)
          (hR₀R (Subgroup.mem_zpowers _))
        rw [hc]
        group
      exact (hYfix (x : G) x.2 hx1 v (h64.le hv) hxv).2.1
    have hVgC : conjSubgroup V g ≤ centralizer (V₀ : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hVg := (h64.elemAbelian).1
      have ha' : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 ha
      have hb' : g * b * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 (hV₀Vg hb)
      have hab : (g * b * g⁻¹) * (g * a * g⁻¹) = (g * a * g⁻¹) * (g * b * g⁻¹) :=
        congrArg Subtype.val (hVg.is_comm.comm ⟨_, hb'⟩ ⟨_, ha'⟩)
      have e1 : (g * b * g⁻¹) * (g * a * g⁻¹) = g * (b * a) * g⁻¹ := by group
      have e2 : (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      rw [e1, e2] at hab
      exact mul_left_cancel (mul_right_cancel hab)
    apply hnotle
    rw [← h64.normalizer₀ hV₀]
    exact hVgC.trans (Subgroup.centralizer_le_normalizer _)
  have hNR : normalizer (R : Set G) ≤ M := h6 R hRM hRodd hcomm
  obtain ⟨l, hlL, h1, h2⟩ := swapHyp_of_hyp64 h64
  have hM : normalizer (V : Set G) = M := h64.normalizer_eq
  have hMl : conjSubgroup M l = conjSubgroup M g := by
    rw [← hM, conjSubgroup_normalizer, conjSubgroup_normalizer, h1]
  have hMgl : conjSubgroup (conjSubgroup M g) l = M := by
    rw [← hM, conjSubgroup_normalizer, conjSubgroup_normalizer, h2]
  have hLl : conjSubgroup (LOf V g) l = LOf V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hlL)
  have hH₀l : conjSubgroup H₀ l = H₀ := by
    rw [hH₀, E3.conjSubgroup_inf, E3.conjSubgroup_inf, hLl, hMl, hMgl, inf_assoc, inf_assoc,
      inf_comm (conjSubgroup M g) M]
  have hlN : l ∈ normalizer (H₀ : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 hH₀l
  obtain ⟨k, hk, m, hm, hlkm⟩ :=
    frattini_argument (p := q) (H := normalizer (H₀ : Set G)) (N := H₀) (P := R)
      Subgroup.le_normalizer Subgroup.normal_in_normalizer hR hlN
  have hlM : l ∈ M := by
    rw [hlkm]
    exact M.mul_mem ((inf_le_left.trans inf_le_right : H₀ ≤ M) hk) (hNR hm.2)
  have hVl : conjSubgroup V l = V := by
    rw [conjSubgroup_eq_iff_mem_normalizer, hM]
    exact hlM
  apply hnotle
  rw [← h1, hVl, ← hM]
  exact Subgroup.le_normalizer

section Certified


theorem inCalO_one_of_hyp65_of_mQuot_le_one {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp65 n M V₀ V g) (hd : E3.mQuot V (conjSubgroup M g) ≤ 1) : InCalO 1 M V₀ V g :=
  ⟨⟨h.inCalO1.1.1.1, hd, h.inCalO1.1.1.2.2⟩,
    ⟨h.inCalO1.1.2.1, (mQuot_dual_eq_of_hyp65 h).trans_le hd, h.inCalO1.1.2.2.2⟩⟩

theorem bBar_conjClosure_le_two_19 (h77 : Inputs1719.W4Lem7_7)
    (hU34 : Inputs1719.K_U34ACand) {D : Data G} {V₀ V : Subgroup G} (hp : Hyp125 D V₀ V)
    {J : Subgroup G} (hJ : J ∈ calC D.M) (hJ1 : barSub V₀ V hp.isElemAbelian J ≠ ⊥)
    (hJs : IsAlt (Bar2 J) 5 ∨ IsU3 (Bar2 J) 2) :
    bBar (UC22.conjClosure D.M J) D.M V₀ V hp.isElemAbelian ≤ 2 := by
  rcases hJs with hA | hU
  · exact S18.bBar_conjClosure_le_two_of_isAlt hp hJ h77 hJ1 hA
  · haveI : IsSimpleGroup (Bar2 J) :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
    obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hJ.2.2 (uc22p21k_center_eq_bot hJ.2.2)
    exact bBar_conjClosure_le_of_aCandLe hp h77 hJ (ACandLe.of_mulEquiv e.symm (hU34 _ hU))

theorem calO_one_empty_19 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h3 : R19_3At D V₀ V p L K h) (h7 : R19_7At D V₀ V p L K h)
    (h77 : Inputs1719.W4Lem7_7) (hU34 : Inputs1719.K_U34ACand) :
    ∀ g : G, ¬ InCalO 1 D.M V₀ V g := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV := h.hyp.isElemAbelian
  have hm : 3 < mBar D.M V₀ V hV := nineteen_seven_gt_three D h h7
  have hLs : IsAlt (Bar2 L) 5 ∨ IsU3 (Bar2 L) 2 := h.shape.imp_left S17.isAlt_five_of_isL2_two
  rcases barSub_ne_bot_or_19 D h61 h127 h h3 with hL1 | hK1
  · have hb := bBar_conjClosure_le_two_19 h77 hU34 h.hyp.hyp125 h.hyp.hL.1 hL1 hLs
    exact twelve_eighteen_empty D hx h61 h127 h1114 h162 hTor h1482 h.hyp.hyp125 hV₀
      (TwelveTwentyThree.conjClosure_le h.hyp.hL.1.1.le)
      (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
      (TwelveTwentyThree.barSub_conjClosure_ne_bot hV hL1) (by omega)
      (TwelveTwentyThree.xCond1218_conjClosure h.hyp.hyp125 hV₀ h.hyp.hL.1.1 h.hyp.hL.1.2.2 1)
  · have hb := bBar_conjClosure_le_two_19 h77 hU34 h.hyp.hyp125 h.hK hK1 (Or.inl h.hKshape)
    exact twelve_eighteen_empty D hx h61 h127 h1114 h162 hTor h1482 h.hyp.hyp125 hV₀
      (TwelveTwentyThree.conjClosure_le h.hK.1.le)
      (TwelveTwentyThree.le_normalizer_conjClosure D.M K)
      (TwelveTwentyThree.barSub_conjClosure_ne_bot hV hK1) (by omega)
      (TwelveTwentyThree.xCond1218_conjClosure h.hyp.hyp125 hV₀ h.hK.1 h.hK.2.2 1)

theorem concl18_1_2_19 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h7 : R19_7At D V₀ V p L K h)
    (hO1 : ∀ g : G, ¬ InCalO 1 D.M V₀ V g) (h6 : R19_6At D V₀ V p L K h) :
    S18.Concl18_1_2 D V₀ V h.hyp.isElemAbelian := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hV := h.hyp.isElemAbelian
  have hP := h.hyp.hyp125.pairFacts
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp.hyp125 hV₀
  have hr := nineteen_eight_one_r D hx h61 h127 h1114 h162 h h7
  intro n hn
  ext X
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨g, rfl, hOg⟩
  have hO : InCalO1 n D.M V₀ V g :=
    (six_six hV hP.le hP.le_normalizer hP.le_normalizer₀ hn g).1 hOg
  have h65 : Hyp65 n D.M V₀ V g := hW.hyp6H.hyp65 hV₀ hO
  by_cases hd : E3.mQuot V (conjSubgroup D.M g) ≤ 1
  · exact hO1 g (inCalO_one_of_hyp65_of_mQuot_le_one h65 hd)
  · have hlt : ((mSub V₀ + n : ℕ) : ℕ∞) < rMV D.M V :=
      lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) hr
    have h64 := hW.hyp6H.hyp64 (h65.inCalOStar_of_lt_rMV hlt)
    exact false_of_hyp64_of_two_le h64 hV₀ h6 (by omega)

theorem nineteen_eight_one (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h3 : R19_3At D V₀ V p L K h) (h6 : R19_6At D V₀ V p L K h) (h7 : R19_7At D V₀ V p L K h)
    (h77 : Inputs1719.W4Lem7_7) (hU34 : Inputs1719.K_U34ACand) : R19_8_1At D V₀ V p L K h := by
  have hV₀ : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.hyp.big
  have hr := nineteen_eight_one_r D hx h61 h127 h1114 h162 h h7
  have h2 := concl18_1_2_19 D hx h61 h127 h1114 h162 h h7
    (calO_one_empty_19 D hx h61 h127 h1114 h162 hTor h1482 h h3 h7 h77 hU34) h6
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h.hyp.hyp125 hV₀
  refine ⟨hr, h2, S18.concl18_1_3_of_no_calO hW.hyp6H hV₀ (fun n hn => ?_) h2⟩
  exact lt_of_lt_of_le (ENat.natCast_lt_natCast.2 (by omega)) hr

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
