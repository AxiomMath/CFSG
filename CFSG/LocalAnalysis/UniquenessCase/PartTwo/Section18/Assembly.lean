module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.GammaTwoBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSixtyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusAset
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusIrr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFifteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenEighteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def R18_standingAt (D : Data G) (V₀ V : Subgroup G) (h : Hyp125 D V₀ V)
    (hsmall : mSub V₀ ≤ 1) (hσ : D.sig.Nonempty) : Prop :=
  ∃ p L, Hyp18 D V₀ V p L

theorem eighteen_standing (D : Data G) (h65 : S17.R17_65 D) :
    ∀ (V₀ V : Subgroup G) (h : Hyp125 D V₀ V) (hsmall : mSub V₀ ≤ 1) (hσ : D.sig.Nonempty),
      R18_standingAt D V₀ V h hsmall hσ := by
  intro V₀ V hV hsmall hσ
  obtain ⟨p, hp⟩ := hσ
  obtain ⟨X, hX⟩ := h65 V₀ V hV p hp
  obtain ⟨L, hL, hXL⟩ :=
    S17.mem_calLpStar.1 (S17.calL0Star_subset D p hX)
  exact ⟨p, L, hV, hp, hL, by rw [← hXL]; exact hX, hsmall⟩

theorem offender_of_not_normalizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) :
    ¬ normalizer (F12.Wi 0 D.T V : Set G) ≤ D.M →
      ∃ A : Subgroup G, A ∈ F12.Gam 0 D.T V ∧
        barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥ := by
  intro hN
  by_contra hcon
  push Not at hcon
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  apply hN
  rw [S17.Wi_eq_wClos 0 D.T V hV]
  refine normalizer_wClos_le_of_le_cTilde D (r129_1_of_r127 D h127) h61 hx.sig_nonempty
    hx.three_le h.hyp125 h.small ?_
  refine E3.wClos_le_of_forall fun A hA => ?_
  have hA' : A ∈ F12.Gam 0 D.T V := by rwa [S17.gam_eq_gammaSet]
  exact (CFSG.LocalAnalysis.WeakClosure81.barSub_eq_bot_iff hV
    h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
    (hA.1.trans D.sylowM.le)).1 (hcon A hA')

theorem not_normalizer_of_r18_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h111 : W3Thm111 G)
    (h183 : W3Thm183 G) (hm : MBarGT D.M V₀ V 3) : R18_23At D V₀ V p L → ¬ normalizer (F12.Wi 0 D.T V : Set G) ≤ D.M := by
  intro h23 hN
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  rw [S17.Wi_eq_wClos 0 D.T V hV] at hN
  by_cases hV₀ : V₀ = ⊥
  · subst hV₀
    have hk2 : D.k ≤ 2 := by
      unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
      split_ifs <;> norm_num
    have hmbar : 3 < mBar D.M ⊥ V hV := (h.hyp125.mBarGT_iff_lt_mBar 3).1 hm
    have hkr : 2 < rk ↥V :=
      lt_of_lt_of_le (by norm_num : (2 : ℕ) < 3)
        (hmbar.le.trans (CFSG.LocalAnalysis.WeakClosure81.mBar_le_rk (M := D.M) hV bot_le))
    have hmk : MBarGT D.M ⊥ V (D.k + 0) := TwelveShort.mBarGT_mono hm (by omega)
    rcases twelve_ten_two D hx h61 h126 h111 h.hyp125 rfl (i := 0) hmk with hN' | hC
    · exact hN' hN
    · apply hC
      have hWk : E3.wClos V (D.k + 0) D.T ≤ E3.wClos V 2 D.T :=
        wClos_le_wClos_of_le hV (by omega) hkr D.T
      have hC2k : E3.cClos V 2 D.T ≤ E3.cClos V (D.k + 0) D.T :=
        inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hWk))
      have h23' : centralizer ((E3.cClos V 2 D.T : Subgroup G) : Set G) ≤ D.M := by
        have := h23
        unfold R18_23At at this
        rwa [S17.Ci_eq_cClos 2 D.T V hV] at this
      exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hC2k)).trans h23'
  · exact twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 h.hyp125 hV₀
      (TwelveShort.mBarGT_mono hm (by omega)) hN

theorem four_mul_n_le_rk_of_not_le_normalizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (h16 : R18_16_2At D V₀ V p L h) (hs : P18_13_2 D V₀ V p L h 1)
    {A : Subgroup G} (hA : A ∈ F12.Gam 0 D.T V) (hVA : ¬ V ≤ normalizer (A : Set G)) :
    4 * S17.nOf L ≤ rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  obtain ⟨hAT, U, g, hUV, hcard, hAeq⟩ := hA
  have hcard' : Nat.card V = Nat.card U := by simpa using hcard
  have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (le_of_eq hcard')
  subst U
  have hAc : A = conjSubgroup V g⁻¹ := by
    rw [hAeq, conjSubgroup, inv_inv]
  have hAM : A ≤ D.M := hAT.trans D.sylowM.le
  set C : Subgroup G := A ⊓ F11.CTilde D.M V₀ V with hCdef
  have hrk : rk ↥(barSub V₀ V hV A) = E3.mQuot A C :=
    CFSG.LocalAnalysis.WeakClosure81.rk_barSub_eq_mQuot_inf_cTilde hV
      h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hAM
  by_contra hlt
  push Not at hlt
  rw [hrk] at hlt
  have h62 := h.hyp125.hyp62
  have hD : C ≤ conjSubgroup V g⁻¹ ⊓ D.M :=
    le_inf (hAc ▸ inf_le_left) (inf_le_left.trans hAM)
  have hr : ((E3.mQuot (conjSubgroup V g⁻¹) C + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V := by
    rw [← hAc]
    have hsm := h.small
    calc ((E3.mQuot A C + mSub V₀ : ℕ) : ℕ∞) < ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) := by
          exact_mod_cast (show E3.mQuot A C + mSub V₀ < 4 * S17.nOf L + 1 by omega)
      _ ≤ rMV D.M V := h16 1 hs
  have hU := CFSG.LocalAnalysis.WeakClosure81.six_two_one h62 hD hr
  have hpre : V ≤ CFSG.LocalAnalysis.WeakClosure81.preCTilde V₀ V C hV := by
    intro v hv
    rw [CFSG.LocalAnalysis.WeakClosure81.mem_preCTilde_iff hV (h62.le_stabTil hD) hv]
    intro d hd
    have hdC : CentralizesMod V₀ V d :=
      CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde hV
        h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hd.2
    have h1 : d * v * d⁻¹ * v⁻¹ ∈ V₀ := hdC v hv
    have h2 : ⁅v, d⁆ = (d * v * d⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact V₀.inv_mem h1
  apply hVA
  rw [hAc, ← E3.conjSubgroup_normalizer, h.hyp125.normalizer_eq]
  exact hpre.trans hU

theorem of_sumOfNat_one {W : Type} [CommGroup W]
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop} {H : Subgroup (MulAut W)}
    (h : SumOfNat N H ⊤ ⊥ 1) : N H ⊤ ⊥ := by
  obtain ⟨I, -, -, hsup, hN⟩ := h
  have hI : I 0 = ⊤ := by
    rw [bot_sup_eq, iSup_unique] at hsup
    exact hsup
  exact hI ▸ hN 0

theorem mem_aSet_of_mQuot_le_one {W : Type} [CommGroup W] [Finite W] {k : ℕ}
    {X Y A B : Subgroup (MulAut W)} (hA : A ∈ E3.aSet (k + 1) X) (hBA : B ≤ A) (hBY : B ≤ Y)
    (hB : B ≠ ⊥) (hAB : E3.mQuot A B ≤ 1) : B ∈ E3.aSet k Y := by
  refine ⟨hBY, hB, ⟨fun a ha b hb => hA.2.2.1.1 a (hBA ha) b (hBA hb),
    fun a ha => hA.2.2.1.2 a (hBA ha)⟩, fun C hCB hm => ?_⟩
  have hadd := E3.mQuot_add hCB hBA
  have hC : fixV C = fixV A := hA.2.2.2 C (hCB.trans hBA) (by omega)
  have hB' : fixV B = fixV A := hA.2.2.2 B hBA (by omega)
  rw [hC, hB']

theorem eighteen_exists_gamma_zero {D : Data G} {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hA : A ∈ F12.Gam 0 D.T V)
    {j : ℕ} (hjV : j ≤ mSub V) :
    ∃ B : Subgroup G, B ∈ F12.Gam (j - 1) A V := by
  obtain ⟨-, U, g, hUV, hcard, hAeq⟩ := hA
  have hcard' : Nat.card V = Nat.card U := by simpa using hcard
  have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (le_of_eq hcard')
  subst U
  have hV2 : IsPGroup 2 V := hV.isPGroup
  have hcardV : Nat.card V = 2 ^ mSub V := card_eq_two_pow_mSub hV2
  have hex : ∃ U' : Subgroup G, U' ≤ V ∧ Nat.card V = 2 ^ (j - 1) * Nat.card U' := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥V) 2
      (n := mSub V - (j - 1)) (by
        rw [hcardV]
        exact pow_dvd_pow 2 (Nat.sub_le _ _))
    refine ⟨K.map V.subtype, Subgroup.map_subtype_le K, ?_⟩
    rw [Subgroup.card_map_of_injective V.subtype_injective, hK, hcardV, ← pow_add]
    congr 1
    omega
  obtain ⟨U', hU'V, hU'card⟩ := hex
  refine ⟨U'.map (MulAut.conj g).toMonoidHom, ?_, U', g, hU'V, hU'card, rfl⟩
  rw [hAeq]
  exact Subgroup.map_mono hU'V

theorem eighteen_membership_b (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hs : P18_13_2 D V₀ V p L h 1)
    (h16 : R18_16_2At D V₀ V p L h) (h17 : R18_17_2At D V₀ V p L h)
    (h18 : R18_18bAt D V₀ V p L h) (hn : 1 ≤ S17.nOf L) {A : Subgroup G}
    (hA : A ∈ F12.Gam 0 D.T V)
    (hAne : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) :
    barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar (2 * S17.nOf L) D.M V₀ V h.hyp125.isElemAbelian := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  have hr : ((4 * S17.nOf L + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := h16 1 hs
  have hδ : ((2 * S17.nOf L : ℕ) : ℕ∞) ≤ deltaInf D.M V := by simpa using h17 1 hs
  have h0 : mSub V₀ ≤ 1 := h.small
  have hr' : ((2 * S17.nOf L - 1 + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : 2 * S17.nOf L - 1 + mSub V₀ <
      4 * S17.nOf L + 1)) hr
  have hrV : rMV D.M V ≤ (mSub V : ℕ∞) := by
    have hMne : D.M ≠ ⊤ := uc22p20a_M_ne_top D
    have hCbot : ¬ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) ≤ D.M := by
      rw [show Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ by simp]
      exact fun hle => hMne (top_le_iff.mp hle)
    have h := CFSG.LocalAnalysis.WeakClosure81.rMV_le_mQuot D.M V ⊥ bot_le hCbot
    rwa [CFSG.Quasithin.E3.mQuot_bot_eq_rk] at h
  have hjV : 2 * S17.nOf L ≤ mSub V := by
    have : ((2 * S17.nOf L : ℕ) : ℕ∞) ≤ (mSub V : ℕ∞) :=
      le_trans (by exact_mod_cast (by omega : 2 * S17.nOf L ≤ 4 * S17.nOf L + 1))
        (hr.trans hrV)
    exact_mod_cast this
  obtain ⟨B, hB⟩ := eighteen_exists_gamma_zero (D := D) hV hA hjV
  have hAgam : A ∈ F12.Gam 0 D.M V := ⟨hA.1.trans D.sylowM.le, hA.2⟩
  have hmem := (h18 0 A hAgam hAne (2 * S17.nOf L) hδ hr' B hB).1
  simpa using hmem

theorem commSub_barSub_le_imgTil {V₀ V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVA : V ≤ normalizer (A : Set G)) :
    commSub ⊤ (barSub V₀ V hV A) ≤ imgTil V₀ V hV (A ⊓ V) := by
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, -, rfl⟩
  obtain ⟨a, haA, rfl⟩ := (mem_barSub V₀ V hV A x).1 hx
  obtain ⟨v, rfl⟩ := mkTil_surjective V₀ V hV w
  rw [actTil_mk, ← map_inv, ← map_mul]
  refine (mem_imgTil V₀ V hV (A ⊓ V) _).2 ⟨actStab V₀ V hV a v * v⁻¹, ⟨?_, ?_⟩, rfl⟩
  · rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
    have h1 : v.val * (a : G)⁻¹ * v.val⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 (hVA v.val_mem) _).1 (A.inv_mem haA)
    have h2 : (a : G) * v.val * (a : G)⁻¹ * v.val⁻¹ =
        (a : G) * (v.val * (a : G)⁻¹ * v.val⁻¹) := by group
    rw [h2]
    exact A.mul_mem haA h1
  · exact (actStab V₀ V hV a v * v⁻¹).val_mem

theorem barSub_self_eq_bot {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) :
    barSub V₀ V hV V = ⊥ := by
  refine le_bot_iff.1 fun φ hφ => ?_
  obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV V φ).1 hφ
  rw [Subgroup.mem_bot, actTil_eq_one_iff]
  intro v hv
  have hc : (g : G) * v = v * (g : G) := by
    have := hV.1.is_comm.comm (⟨g, hg⟩ : V) ⟨v, hv⟩
    simpa using congrArg Subtype.val this
  have : (g : G) * v * (g : G)⁻¹ * v⁻¹ = 1 := by rw [hc]; group
  rw [this]
  exact V₀.one_mem

theorem mem_M_of_centralizer_le (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) (h15 : R18_15At D V₀ V p L)
    {g w : G} (hwV : g⁻¹ * w * g ∈ V) (hw1 : w ≠ 1)
    (hC : centralizer ({w} : Set G) ≤ D.M) : g ∈ D.M := by
  by_contra hg
  have hu1 : g⁻¹ * w * g ≠ 1 := by
    intro hu
    apply hw1
    have : w = g * (g⁻¹ * w * g) * g⁻¹ := by group
    rw [this, hu]
    group
  obtain ⟨hpp, hpd⟩ := h15 _ hwV hu1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(D.M ⊓ centralizer ({g⁻¹ * w * g} : Set G))) p hpd
  have hyM : (y : G) ∈ D.M := y.2.1
  have hyC : (y : G) ∈ centralizer ({g⁻¹ * w * g} : Set G) := y.2.2
  have hc : (g⁻¹ * w * g) * (y : G) = (y : G) * (g⁻¹ * w * g) :=
    (Subgroup.mem_centralizer_iff.1 hyC) _ rfl
  have hzC : g * (y : G) * g⁻¹ ∈ centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro x rfl
    calc x * (g * (y : G) * g⁻¹) = g * ((g⁻¹ * x * g) * (y : G)) * g⁻¹ := by group
      _ = g * ((y : G) * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = g * (y : G) * g⁻¹ * x := by group
  have hzM : g * (y : G) * g⁻¹ ∈ D.M := hC hzC
  have hzconj : g * (y : G) * g⁻¹ ∈ CFSG.Quasithin.conjSubgroup D.M g⁻¹ :=
    ⟨y, hyM, by simp [MulAut.conj_apply]⟩
  have hord : orderOf (g * (y : G) * g⁻¹) = p := by
    have e : g * (y : G) * g⁻¹ = MulAut.conj g (y : G) := rfl
    rw [e, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  have hdvd : p ∣ Nat.card (D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g⁻¹ : Subgroup G) := by
    have := Subgroup.orderOf_dvd_natCard (D.M ⊓ CFSG.Quasithin.conjSubgroup D.M g⁻¹)
      (x := g * (y : G) * g⁻¹) ⟨hzM, hzconj⟩
    rwa [hord] at this
  exact h.p_not_dvd_card_inf hSg (fun hgi => hg (by simpa using D.M.inv_mem hgi)) hdvd

theorem exists_noncyclic_of_isSp4 {W : Type} [CommGroup W] [Finite W] {Y : Subgroup (MulAut W)}
    {n p : ℕ} (hY : IsSp4 (Bar2 Y) n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ (2 ^ n) ^ 2 - 1) :
    ∃ E : Subgroup (MulAut W), E ≤ Y ∧ IsPGroup p E ∧ ¬ IsCyclic E := by
  have h2 := P2214R.two_le_pRank_sp4 hY hp hpd
  have h2' : 2 ≤ CFSG.Open.pRank p Y :=
    uc22p2214_two_le_pRank_of_surj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
      (QuotientGroup.mk'_surjective _) hp hp2 h2
  obtain ⟨E, hEY, hEab, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp Y
  refine ⟨E, hEY, IsPGroup.of_card hcard, uc22p22n_not_isCyclic_of_card hp hEab ?_⟩
  rw [hcard]
  exact Nat.pow_le_pow_right hp.pos h2'

@[expose] def R18_fieldOmega (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L) (f : ℕ),
    IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 f →
      S17.nOf L = f ∧ 1 < f ∧ (2 : ℤ) ^ f ≡ -1 [ZMOD (p : ℤ)]

theorem commSub_singular_of_le_normalizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L : Subgroup G} (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h142 : R18_14_2At D V₀ V p L h) (h15 : R18_15At D V₀ V p L)
    (hs : P18_13_2 D V₀ V p L h 1) {n : ℕ} (hn : 2 ≤ n)
    (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])
    (hO : IsOmegaMinus ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) 6 n)
    (hN : NatOmegaMinus (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤ ⊥ 6 n)
    {F : Type} [Field F] [Finite F] {b c : F} (hF : Nat.card F = 2 ^ n)
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ε : ↥(barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ≃*
      ↥(StatedOmega (StatedQuadMinus 3 F b c)))
    (ψ : ↥(⊤ : Subgroup (Vtil V₀ V h.hyp125.isElemAbelian)) ≃*
      Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F))
    (hψ : NatCoordsOmegaMinusOn (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) ⊤
      (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ)
    {A : Subgroup G} (hA : A ∈ F12.Gam 0 D.T V)
    (hAne : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥) (hVA : V ≤ normalizer (A : Set G)) :
    ∀ w ∈ commSub ⊤ (barSub V₀ V h.hyp125.isElemAbelian A),
      StatedQuadMinus 3 F b c (Multiplicative.toAdd (ψ ⟨w, Subgroup.mem_top w⟩)) = 0 := by
  have hV : IsElemAbelian 2 V := h.hyp125.isElemAbelian
  intro w hw
  obtain ⟨x, ⟨hxA, hxV⟩, rfl⟩ :=
    (mem_imgTil V₀ V hV (A ⊓ V) w).1 (commSub_barSub_le_imgTil hV hVA hw)
  by_cases hx0 : x.val ∈ V₀
  · have h1 : mkTil V₀ V hV x = 1 := (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 hx0
    have h2 : (⟨mkTil V₀ V hV x, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup (Vtil V₀ V hV))) = 1 :=
      Subtype.ext h1
    rw [h2, map_one, toAdd_one]
    simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  by_contra hQ
  have hxt : tilOf V₀ V hV x.val x.val_mem = mkTil V₀ V hV x := rfl
  have hSp : IsSp4
      (Bar2 (Opp p (centVec (barSub V₀ V hV (UC22.conjClosure D.M L))
        (mkTil V₀ V hV x)))) n := by
    have := ((h142 ⟨1, hs⟩ n hn hO).2 ⊤ (fun _ _ s _ => Subgroup.mem_top s) hN F b c hF hbc
      ε ψ hψ x.val x.val_mem hx0 (Subgroup.mem_top _)).2 hQ
    exact this
  have hpp : p.Prime := h.p_prime
  have hp2 : p ≠ 2 := h.p_ne_two
  have hpd : p ∣ (2 ^ n) ^ 2 - 1 := P2214R.dvd_sq_sub_one (P2214R.dvd_of_cong hcong)
  obtain ⟨E, hEY, hEp, hEc⟩ := exists_noncyclic_of_isSp4 hSp hpp hp2 hpd
  have hEpt : E ≤ ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    intro e he
    have he' := hEY he
    have he'' : e ∈ centVec (barSub V₀ V hV (UC22.conjClosure D.M L))
        (mkTil V₀ V hV x) :=
      (show Opp p (centVec (barSub V₀ V hV (UC22.conjClosure D.M L))
          (mkTil V₀ V hV x)) ≤
          centVec (barSub V₀ V hV (UC22.conjClosure D.M L)) (mkTil V₀ V hV x) from
        (Subgroup.closure_le _).mpr fun _ hy => hy.1) he'
    obtain ⟨he1, he2⟩ := he''
    exact ⟨barSub_mono V₀ V hV h.X_le_M he1, he2⟩
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases h.hyp125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4 : Nat.card V₀ ≤ 4 := by
    have := (mSub_le_one_iff h.hyp125.pairFacts.elemAbelian₀).1 h.small
    omega
  have hCx : centralizer ({x.val} : Set G) ≤ D.M :=
    centralizer_le_of_noncyclic_bar D h61 hpp hp2 h.hp hV h.hyp125.pairFacts hcase h4 x hx0
      hEpt hEp hEc
  obtain ⟨hAT, U, g, hUV, hcard, hAeq⟩ := hA
  have hcard' : Nat.card V = Nat.card U := by simpa using hcard
  have hUV' : U = V := Subgroup.eq_of_le_of_card_ge hUV (le_of_eq hcard')
  subst U
  have hxg : g⁻¹ * x.val * g ∈ V := by
    rw [hAeq] at hxA
    obtain ⟨v, hv, hve⟩ := hxA
    rw [← hve]
    simpa [MulAut.conj_apply, mul_assoc] using hv
  have hx1 : x.val ≠ 1 := fun h1 => hx0 (h1 ▸ V₀.one_mem)
  have hgM : g ∈ D.M := mem_M_of_centralizer_le D h hSg h15 hxg hx1 hCx
  apply hAne
  have hAV : A = V := by
    rw [hAeq]
    have hgN := h.hyp125.pairFacts.le_normalizer hgM
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgN
    exact hgN
  rw [hAV]
  exact barSub_self_eq_bot hV

theorem rk_lt_four_mul (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hs : P18_13_2 D V₀ V p L h 1) (hfield : R18_fieldOmega D)
    {A : Subgroup G}
    (hAM : A ≤ D.M)
    (hAQ : barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar (2 * S17.nOf L) D.M V₀ V h.hyp125.isElemAbelian) :
    rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) < 4 * S17.nOf L := by
  obtain ⟨-, -, f, hO, hsum⟩ := id hs
  have hNat := of_sumOfNat_one hsum
  obtain ⟨hnf, hf1, -⟩ := hfield V₀ V p L h f hO
  have hAbN : barSub V₀ V h.hyp125.isElemAbelian A ≤
      normalizer (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :
        Set (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) :=
    (barSub_mono _ _ _ hAM).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (barSub_mono V₀ V h.hyp125.isElemAbelian h.X_le_M)).1
        (barSub_subgroupOf_mbar_normal h.hyp125.isElemAbelian h.X_le_M
          (TwelveTwentyThree.le_normalizer_conjClosure D.M L)))
  have hel := hAQ.2.2.1
  have hidx := k_Omega6Minus_outIndex _ f (by omega) hO hNat _ hAbN hel
  have hrkA : 2 * f ≤ rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) := by
    have h1 := E3.le_mQuot_bot_of_mem_aSet hAQ
    rw [E3.mQuot_bot_eq_rk, hnf] at h1
    exact h1
  have hsplit : rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) =
      rk ↥(barSub V₀ V h.hyp125.isElemAbelian A ⊓
        barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) +
      E3.mQuot (barSub V₀ V h.hyp125.isElemAbelian A)
        (barSub V₀ V h.hyp125.isElemAbelian A ⊓
          barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) := by
    rw [← E3.mQuot_bot_eq_rk, ← E3.mQuot_bot_eq_rk]
    exact E3.mQuot_add bot_le inf_le_left
  have hne : barSub V₀ V h.hyp125.isElemAbelian A ⊓
      barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hsplit hidx
    have : rk ↥(⊥ : Subgroup (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) = 0 := by
      rw [← E3.mQuot_bot_eq_rk, E3.mQuot_self]
    omega
  have hmem := mem_aSet_of_mQuot_le_one (k := 2 * f - 1)
    (X := Mbar D.M V₀ V h.hyp125.isElemAbelian)
    (by rw [show 2 * f - 1 + 1 = 2 * S17.nOf L by omega]; exact hAQ)
    inf_le_left inf_le_right hne hidx
  have hle2 := k_Omega6Minus_aSet_rank _ f (by omega) hNat _ (E3.aSet_anti (by omega) _ hmem)
  omega

theorem not_le_normalizer_of_mem (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Hyp18 D V₀ V p L) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h142 : R18_14_2At D V₀ V p L h) (h15 : R18_15At D V₀ V p L)
    (hs : P18_13_2 D V₀ V p L h 1) (hfield : R18_fieldOmega D)
    {A : Subgroup G}
    (hA : A ∈ F12.Gam 0 D.T V) (hAne : barSub V₀ V h.hyp125.isElemAbelian A ≠ ⊥)
    (hAQ : barSub V₀ V h.hyp125.isElemAbelian A ∈
      calABar (2 * S17.nOf L) D.M V₀ V h.hyp125.isElemAbelian) :
    ¬ V ≤ normalizer (A : Set G) := by
  intro hVA
  obtain ⟨-, -, f, hO, hsum⟩ := id hs
  have hNat := of_sumOfNat_one hsum
  obtain ⟨hnf, hf1, hcong⟩ := hfield V₀ V p L h f hO
  have hAM : A ≤ D.M := hA.1.trans D.sylowM.le
  have hAbN : barSub V₀ V h.hyp125.isElemAbelian A ≤
      normalizer (barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L) :
        Set (MulAut (Vtil V₀ V h.hyp125.isElemAbelian))) :=
    (barSub_mono _ _ _ hAM).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (barSub_mono V₀ V h.hyp125.isElemAbelian h.X_le_M)).1
        (barSub_subgroupOf_mbar_normal h.hyp125.isElemAbelian h.X_le_M
          (TwelveTwentyThree.le_normalizer_conjClosure D.M L)))
  have hel := hAQ.2.2.1
  have hidx := k_Omega6Minus_outIndex _ f (by omega) hO hNat _ hAbN hel
  have hrkA : 2 * f ≤ rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) := by
    have h1 := E3.le_mQuot_bot_of_mem_aSet hAQ
    rw [E3.mQuot_bot_eq_rk, hnf] at h1
    exact h1
  have hsplit : rk ↥(barSub V₀ V h.hyp125.isElemAbelian A) =
      rk ↥(barSub V₀ V h.hyp125.isElemAbelian A ⊓
        barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) +
      E3.mQuot (barSub V₀ V h.hyp125.isElemAbelian A)
        (barSub V₀ V h.hyp125.isElemAbelian A ⊓
          barSub V₀ V h.hyp125.isElemAbelian (UC22.conjClosure D.M L)) := by
    rw [← E3.mQuot_bot_eq_rk, ← E3.mQuot_bot_eq_rk]
    exact E3.mQuot_add bot_le inf_le_left
  obtain ⟨F, _, _, b, c, hF, hbc, ε, ψ, hψ⟩ := exists_natCoords_of_natOmegaMinus hNat
  have hsing := commSub_singular_of_le_normalizer D h hSg h61 h142 h15 hs (by omega) hcong hO
    hNat hF hbc ε ψ hψ hA hAne hVA
  have hle1 := k_Omega6Minus_singComm_rank _ f F b c (by omega) hF hbc ε ψ hψ _ inf_le_right
    ⟨fun a ha b hb => hel.1 a ha.1 b hb.1, fun a ha => hel.2 a ha.1⟩
    (fun w hw => hsing w (commSub_mono le_rfl inf_le_left hw))
  omega

theorem eighteen_twentyfour_of1669_g (D : Data G)
    (h65 : S17.R17_65 D)
    (h14 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_14_2At D V₀ V p L h)
    (h16 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_16_2At D V₀ V p L h)
    (h17 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_17_2At D V₀ V p L h)
    (h22 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_22At D V₀ V p L h)
    (h23 : ∀ V₀ V p L (_h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_23At D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G) (hSg : UC6S846.SigmaStd D)
    (hfield : R18_fieldOmega D) : R18_24Of1669 D := by
  intro V₀ V hV hm
  by_contra hle
  have hsmall : mSub V₀ ≤ 1 := Nat.le_of_not_lt hle
  obtain ⟨p, L, h⟩ := eighteen_standing D h65 V₀ V hV hsmall hx.sig_nonempty
  have hP132 : P18_13_2 D V₀ V p L h 1 := h22 V₀ V p L h hm
  obtain ⟨-, -, f, hO, -⟩ := id hP132
  obtain ⟨hnf, hf1, -⟩ := hfield V₀ V p L h f hO
  have h142 := h14 V₀ V p L h hm
  have h15 : R18_15At D V₀ V p L := r18_15_of_case2 D h h142 hP132 (f := f) (by omega) hO
  have hN := not_normalizer_of_r18_23 D h hx h61 h126 h66 h127 h1114 h111 h183 hm
    (h23 V₀ V p L h hm)
  obtain ⟨A, hA, hAne⟩ := offender_of_not_normalizer D h hx h61 h127 hN
  have h16_2 := h16 V₀ V p L h hm
  have hAQ := eighteen_membership_b D h hP132 h16_2 (h17 V₀ V p L h hm)
    (eighteen_eighteen_b D hSg h h15) (by omega) hA hAne
  have hVA := not_le_normalizer_of_mem D h hSg h61 h142 h15 hP132 hfield hA hAne hAQ
  exact absurd (four_mul_n_le_rk_of_not_le_normalizer D h h16_2 hP132 hA hVA)
    (not_le_of_gt (rk_lt_four_mul D h hP132 hfield (hA.1.trans D.sylowM.le) hAQ))

section Certified

theorem r18_fieldOmega (D : Data G) (h1742 : S17.R17_42 D) : R18_fieldOmega D := by
  intro V₀ V p L h f hO
  obtain ⟨-, h1, h2, h3⟩ := isU4_barSub_cong h (h1742 V₀ V h.hyp125) (isU4_of_isOmegaMinus hO)
  exact ⟨h1, h2, h3⟩

theorem eighteen_twentyfour_of1669_loc (D : Data G)
    (h65 : ∀ V₀ V, Hyp125 D V₀ V → MBarGT D.M V₀ V 3 → S17.R17_65At D V₀ V)
    (h1742 : ∀ V₀ V, Hyp125 D V₀ V → MBarGT D.M V₀ V 3 → S17.R17_42At D V₀ V)
    (h14 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_14_2At D V₀ V p L h)
    (h16 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_16_2At D V₀ V p L h)
    (h17 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_17_2At D V₀ V p L h)
    (h22 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_22At D V₀ V p L h)
    (h23 : ∀ V₀ V p L (_h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_23At D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G) (hSg : UC6S846.SigmaStd D) :
    R18_24Of1669 D := by
  intro V₀ V hV hm
  exact eighteen_twentyfour_of1669_g D (fun _ _ _ => h65 V₀ V hV hm) h14 h16 h17 h22 h23
    hx h61 h126 h66 h127 h1114 h111 h183 hSg
    (r18_fieldOmega D (fun _ _ _ => h1742 V₀ V hV hm)) V₀ V hV hm

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
