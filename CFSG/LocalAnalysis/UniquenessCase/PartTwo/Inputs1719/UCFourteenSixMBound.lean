module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFiveMinimal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3Modules
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubBar2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

theorem iSup_conjSet_eq_of_le_normalizer {A : Type*} [Group A] {K N : Subgroup A}
    (hN : N ≤ normalizer (K : Set A)) : (⨆ X ∈ conjSet K N, X) = K := by
  refine le_antisymm (iSup₂_le fun X hX => ?_) ?_
  · obtain ⟨n, hn, rfl⟩ := hX
    exact le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hn))
  · exact le_iSup₂_of_le (f := fun X (_ : X ∈ conjSet K N) => X) K
      (s15_T7_mem_conjSet_self K N) le_rfl

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem actTil_bot_sq_eq_one_of_commutator_le {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀V : V₀ ≤ V) (hV₀Y : V₀ ≤ centralizer (Y : Set G)) {k : G} (hkY : k ∈ Y)
    (hks : k ∈ stabTil (⊥ : Subgroup G) V)
    (hk : ∀ v ∈ V, k * v * k⁻¹ * v⁻¹ ∈ V₀) :
    (actTil (⊥ : Subgroup G) V hV ⟨k, hks⟩) ^ 2 = 1 := by
  have hk₀ : ∀ d ∈ V₀, k * d * k⁻¹ = d := by
    intro d hd
    have hcomm : k * d = d * k := Subgroup.mem_centralizer_iff.1 (hV₀Y hd) k hkY
    rw [hcomm]
    group
  rw [← map_pow, actTil_eq_one_iff]
  intro v hv
  rw [Subgroup.mem_bot, Subgroup.coe_pow]
  set d : G := k * v * k⁻¹ * v⁻¹ with hd
  have hd₀ : d ∈ V₀ := hk v hv
  have hdv : k * v * k⁻¹ = d * v := by rw [hd]; group
  have hkd : k * d * k⁻¹ = d := hk₀ d hd₀
  have hd2 : d ^ 2 = 1 := hV.2 d (hV₀V hd₀)
  have hd2' : d * d = 1 := by rw [← pow_two]; exact hd2
  rw [pow_two]
  calc k * k * v * (k * k)⁻¹ * v⁻¹
      = k * (k * v * k⁻¹) * k⁻¹ * v⁻¹ := by group
    _ = k * (d * v) * k⁻¹ * v⁻¹ := by rw [hdv]
    _ = (k * d * k⁻¹) * (k * v * k⁻¹) * v⁻¹ := by group
    _ = d * (d * v) * v⁻¹ := by rw [hkd, hdv]
    _ = (d * d) * (v * v⁻¹) := by group
    _ = 1 := by rw [hd2', mul_inv_cancel, mul_one]

section

variable {D : Data G} {Y V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem imgTil_eq_bot_of_le {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) :
    imgTil V₀ V hV V₀ = ⊥ := by
  refine le_bot_iff.1 fun q hq => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV V₀ q).1 hq
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).2 ((mem_modNull V₀ V hV x).2 hx)

omit [Finite G] in
theorem preTil_fixV_barSub_eq {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = V ⊓ centralizer (Y : Set G)) (hperf : ⁅Y, Y⁆ = Y)
    (hYs : Y ≤ stabTil V₀ V) :
    preTil V₀ V hV (fixV (barSub V₀ V hV Y)) = V₀ := by
  have hV₀Y : V₀ ≤ centralizer (Y : Set G) := by rw [hV₀]; exact inf_le_right
  have hYV₀ : ⁅V₀, Y⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hV₀Y
  have hV₀V : V₀ ≤ V := by rw [hV₀]; exact inf_le_left
  set W : Subgroup G := preTil V₀ V hV (fixV (barSub V₀ V hV Y)) with hW
  have hWV : W ≤ V := preTil_le _ _ _ _
  have hcomm : ⁅Y, W⁆ ≤ V₀ := by
    refine Subgroup.commutator_le.mpr ?_
    rintro y hy w hw
    obtain ⟨x, rfl, hx⟩ := (mem_preTil V₀ V hV _).1 hw
    have h1 := (mem_fixV.1 hx) _ (actTil_mem_barSub V₀ V hV hy (hYs hy))
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
    rw [commutatorElement_def]
    exact h1
  have h1 : ⁅W, Y⁆ ≤ V₀ := (Subgroup.commutator_comm W Y).le.trans hcomm
  have h2 : ⁅⁅W, Y⁆, Y⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅W, Y⁆, Y⁆ ≤ ⁅V₀, Y⁆ := Subgroup.commutator_mono h1 le_rfl
      _ = ⊥ := hYV₀
  have hbot : ⁅W, Y⁆ = ⊥ :=
    CFSG.ComponentClassification.Asc76.Sec5.commutator_eq_bot_of_commutator_commutator_eq_bot
      hperf h2
  have hWC : W ≤ centralizer (Y : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [hV₀]
    exact Subgroup.mem_inf.2 ⟨hWV hg, hWC hg⟩
  · intro g hg
    have hgV : g ∈ V := hV₀V hg
    rw [mem_preTil_iff_of_mem V₀ V hV _ hgV, mem_fixV]
    intro y hy
    obtain ⟨y₀, hy₀, hyy⟩ := (mem_barSub V₀ V hV Y y).1 hy
    rw [← hyy, actTil_mk, mkTil_eq_iff, actStab_apply_val]
    change (y₀ : G) * g * (y₀ : G)⁻¹ * g⁻¹ ∈ V₀
    have hgC : g ∈ centralizer (Y : Set G) := by
      have hg' : g ∈ V ⊓ centralizer (Y : Set G) := hV₀ ▸ hg
      exact hg'.2
    have hcomm' : (y₀ : G) * g = g * (y₀ : G) := Subgroup.mem_centralizer_iff.1 hgC _ hy₀
    rw [hcomm', mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

theorem stableUnder_eq_bot_or_top_of_min {D : Data G} {Y V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMY : D.M ≤ normalizer (Y : Set G))
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G))
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ normalizer (W : Set G) → W ≤ V →
      ⁅Y, W⁆ ≠ ⊥ → W = V)
    {U : Subgroup (Vtil (V ⊓ centralizer (Y : Set G)) V hV)}
    (hU : StableUnder (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) U) :
    U = ⊥ ∨ U = ⊤ := by
  have hMs : D.M ≤ stabTil (V ⊓ centralizer (Y : Set G)) V :=
    le_stabTil hMV ((fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm)))
  have hWV : preTil (V ⊓ centralizer (Y : Set G)) V hV U ≤ V := preTil_le _ _ _ _
  have hWM : D.M ≤ normalizer (preTil (V ⊓ centralizer (Y : Set G)) V hV U : Set G) :=
    TwelveSeventeen.le_normalizer_preTil hV hMs hU
  by_cases hW : preTil (V ⊓ centralizer (Y : Set G)) V hV U = V
  · right
    rw [← imgTil_preTil (V ⊓ centralizer (Y : Set G)) V hV U, hW,
      s15_Infra_imgTil_top (V ⊓ centralizer (Y : Set G)) V hV]
  · left
    have hcomm : ⁅Y, preTil (V ⊓ centralizer (Y : Set G)) V hV U⁆ = ⊥ := by
      by_contra hne
      exact hW (hmin _ (hWV.trans hVU) hWM hWV hne)
    have hle : preTil (V ⊓ centralizer (Y : Set G)) V hV U ≤
        V ⊓ centralizer (Y : Set G) :=
      le_inf hWV (fun w hw => Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm (preTil (V ⊓ centralizer (Y : Set G)) V hV U) Y]
            exact hcomm) hw)
    rw [← imgTil_preTil (V ⊓ centralizer (Y : Set G)) V hV U]
    exact le_bot_iff.mp ((s15_LP_imgTil_mono hV hle).trans (le_of_eq
      (imgTil_eq_bot_of_le (V₀ := V ⊓ centralizer (Y : Set G)) hV)))

end


omit [Finite G] in
theorem barSub_ne_bot_of_min {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = V ⊓ centralizer (Y : Set G)) (hperf : ⁅Y, Y⁆ = Y)
    (hYs : Y ≤ stabTil V₀ V) (hYV : ⁅Y, V⁆ ≠ ⊥) :
    barSub V₀ V hV Y ≠ ⊥ := by
  intro hbot
  apply hYV
  have htop : fixV (barSub V₀ V hV Y) = ⊤ := by
    rw [hbot]
    exact eq_top_iff.2 fun v _ x hx => by rw [Subgroup.mem_bot.1 hx]; rfl
  have hpre : preTil V₀ V hV (fixV (barSub V₀ V hV Y)) = V := by
    rw [htop, preTil_top]
  rw [preTil_fixV_barSub_eq hV hV₀ hperf hYs] at hpre
  have hYV₀ : ⁅Y, V₀⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hV₀ ▸ inf_le_right)
  rw [← hpre]
  exact hYV₀

theorem isBasicModule_mbar_of_min {D : Data G} {Y V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hY : Y ∈ calC D.M) (hMY : D.M ≤ normalizer (Y : Set G))
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ normalizer (W : Set G) → W ≤ V →
      ⁅Y, W⁆ ≠ ⊥ → W = V) :
    IsBasicModule (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) := by
  have hMs : D.M ≤ stabTil (V ⊓ centralizer (Y : Set G)) V :=
    le_stabTil hMV ((fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm)))
  have hYbar : barSub (V ⊓ centralizer (Y : Set G)) V hV Y ≤
      Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV :=
    barSub_mono _ _ _ hY.1.le
  have hYbar_ne : barSub (V ⊓ centralizer (Y : Set G)) V hV Y ≠ ⊥ :=
    barSub_ne_bot_of_min hV rfl hY.2.1 (hY.1.le.trans hMs) hYV
  have hMbar_ne : Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV ≠ ⊥ := fun hbot =>
    hYbar_ne (le_bot_iff.1 (hYbar.trans hbot.le))
  refine Thm14_5.isBasicModule_of_isIrrOn hMbar_ne ⟨?_, fun _ _ _ _ => Subgroup.mem_top _,
    fun _ _ u hu => ?_, fun U hU _ _ => stableUnder_eq_bot_or_top_of_min hV hMY hVU hMV hmin hU⟩
  · refine bot_lt_iff_ne_bot.2 fun h => hMbar_ne (eq_bot_iff.2 fun y _ => ?_)
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun w => ?_
    have hw : w ∈ (⊥ : Subgroup _) := h ▸ Subgroup.mem_top w
    rw [Subgroup.mem_bot] at hw
    simp [hw]
  · rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]

omit [Finite G] in
theorem fixV_barSub_eq_bot_of_min {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = V ⊓ centralizer (Y : Set G)) (hperf : ⁅Y, Y⁆ = Y)
    (hYs : Y ≤ stabTil V₀ V) :
    fixV (barSub V₀ V hV Y) = ⊥ := by
  have h := preTil_fixV_barSub_eq hV hV₀ hperf hYs
  rw [← imgTil_preTil V₀ V hV (fixV (barSub V₀ V hV Y)), h,
    imgTil_eq_bot_of_le (V₀ := V₀) hV]

theorem odd_card_center_barSub {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYs : Y ≤ stabTil (⊥ : Subgroup G) V)
    (hYq : CFSG.Open.IsQuasisimple (Bar2 Y))
    (h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 Y) = ⊥)
    (hY1 : barSub (⊥ : Subgroup G) V hV Y ≠ ⊥) :
    Odd (Nat.card (Subgroup.center ↥(barSub (⊥ : Subgroup G) V hV Y))) := by
  let q : Bar2 Y →* ↥(barSub (⊥ : Subgroup G) V hV Y) :=
    barSubBar2Hom (V₀ := ⊥) hV hYs h2
  have hq : Function.Surjective q := barSubBar2Hom_surjective hV hYs h2
  have hker : q.ker ≤ Subgroup.center (Bar2 Y) := by
    have : q.ker.Normal := MonoidHom.normal_ker q
    refine CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hYq q.ker ?_
    intro htop
    apply hY1
    refine le_bot_iff.1 fun x hx => ?_
    obtain ⟨y, hy⟩ := hq ⟨x, hx⟩
    have hy' : y ∈ q.ker := htop ▸ Subgroup.mem_top y
    rw [MonoidHom.mem_ker] at hy'
    have : (⟨x, hx⟩ : ↥(barSub (⊥ : Subgroup G) V hV Y)) = 1 := by rw [← hy, hy']
    simpa using congrArg Subtype.val this
  have : Group.IsPerfect (Bar2 Y) := ⟨hYq.1⟩
  have hcenter :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel q hq hker
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 Y))) := uc22p20p_odd_center_bar2 Y
  have hdvd : Nat.card (Subgroup.center ↥(barSub (⊥ : Subgroup G) V hV Y)) ∣
      Nat.card (Subgroup.center (Bar2 Y)) := by
    rw [← hcenter]
    exact Subgroup.card_map_dvd (H := Subgroup.center (Bar2 Y)) q
  exact Odd.of_dvd_nat hodd hdvd


theorem inf_cTilde_le_centralizer {D : Data G} {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hY : Y ∈ calC D.M) (hMY : D.M ≤ normalizer (Y : Set G))
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥) :
    Y ⊓ F11.CTilde D.M (V ⊓ centralizer (Y : Set G)) V ≤ centralizer (V : Set G) := by
  set V₀ : Subgroup G := V ⊓ centralizer (Y : Set G) with hV₀
  have hV₀V : V₀ ≤ V := hV₀ ▸ inf_le_left
  have hV₀Y : V₀ ≤ centralizer (Y : Set G) := hV₀ ▸ inf_le_right
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hV₀ ▸ (fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm))
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hM₀ : D.M ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hYs : Y ≤ stabTil (⊥ : Subgroup G) V :=
    le_inf (hY.1.le.trans hMV) (by rw [Subgroup.normalizer_eq_top]; exact le_top)
  have hYp : pCoreOf 2 Y ≤ centralizer (V : Set G) :=
    S17.seventeen_fiftyfive_min_pCore_le_centralizer hY hVU
  have hp_le : pCoreOf 2 Y ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hY.1.le
  have hpCoreC : pCoreOf 2 Y ≤ F11.CTilde D.M V₀ V := by
    intro x hx
    rw [mem_cTilde_iff hV hMV]
    refine ⟨hp_le hx, ⟨?_, ?_⟩⟩
    · exact ⟨(hY.1.le.trans hMV) (CFSG.LieType.BorelTits.pCoreOf_le 2 Y hx),
        hMV₀ (hp_le hx)⟩
    · refine (actTil_eq_one_iff V₀ V hV _).2 fun v hv => ?_
      change x * v * x⁻¹ * v⁻¹ ∈ V₀
      have hc : v * x = x * v := Subgroup.mem_centralizer_iff.1 (hYp hx) v hv
      have hcx : x * v * x⁻¹ * v⁻¹ = 1 := by rw [hc.symm]; group
      rw [hcx]
      exact V₀.one_mem
  have hpCoreCbot : pCoreOf 2 Y ≤ F11.CTilde D.M (⊥ : Subgroup G) V := by
    intro x hx
    rw [mem_cTilde_iff hV hMV]
    refine ⟨hp_le hx, ⟨hYs (CFSG.LieType.BorelTits.pCoreOf_le 2 Y hx), ?_⟩⟩
    refine (actTil_eq_one_iff (⊥ : Subgroup G) V hV _).2 fun v hv => ?_
    rw [Subgroup.mem_bot]
    change x * v * x⁻¹ * v⁻¹ = 1
    have hc : v * x = x * v := Subgroup.mem_centralizer_iff.1 (hYp hx) v hv
    rw [hc.symm]
    group
  have h2 : barSub (⊥ : Subgroup G) V hV (pCoreOf 2 Y) = ⊥ :=
    (WeakClosure81.barSub_eq_bot_iff (V₀ := ⊥) hV hMV hM₀ hp_le).2 hpCoreCbot
  have hY1 : barSub (⊥ : Subgroup G) V hV Y ≠ ⊥ := by
    intro hbot
    have hYle := (WeakClosure81.barSub_eq_bot_iff (V₀ := ⊥) hV hMV hM₀ hY.1.le).1 hbot
    apply hYV
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun y hy => ?_
    obtain ⟨-, h, h1⟩ := (mem_cTilde_iff hV hMV).1 (hYle hy)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h2' : y * v = v * y := by
      have h2c : y * v * y⁻¹ * v⁻¹ = 1 := by
        simpa using (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨y, h⟩).1 h1 v hv
      calc y * v = (y * v * y⁻¹ * v⁻¹) * (v * y) := by group
        _ = v * y := by rw [h2c, one_mul]
    exact h2'.symm
  have hYq : CFSG.Open.IsQuasisimple (Bar2 Y) := hY.2.2
  have hYbarq : CFSG.Open.IsQuasisimple ↥(barSub (⊥ : Subgroup G) V hV Y) :=
    TwelveTwentyThree.isQuasisimple_barSub (V₀ := ⊥) hV hYs hYq (by simpa using h2) hY1
  set K : Subgroup G := Y ⊓ F11.CTilde D.M V₀ V with hK
  have hKY : K ≤ Y := hK ▸ inf_le_left
  have hKN : Y ≤ normalizer (K : Set G) := by
    have hCn : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
    have hC_le : F11.CTilde D.M V₀ V ≤ D.M := by
      intro x hx
      exact ((mem_cTilde_iff hV hMV).1 hx).1
    have hYnormC : Y ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
      hY.1.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hC_le).1 hCn)
    exact (le_inf Subgroup.le_normalizer hYnormC).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hLnorm : ((barSub (⊥ : Subgroup G) V hV K).subgroupOf
      (barSub (⊥ : Subgroup G) V hV Y)).Normal :=
    barSub_subgroupOf_mbar_normal (V₀ := ⊥) hV hKY hKN
  have hL2 : IsPGroup 2 ↥(barSub (⊥ : Subgroup G) V hV K) := by
    have hsq : ∀ φ : ↥(barSub (⊥ : Subgroup G) V hV K),
        (φ : MulAut (Vtil (⊥ : Subgroup G) V hV)) ^ 2 = 1 := by
      intro φ
      obtain ⟨k, hkK, hkφ⟩ := (mem_barSub (⊥ : Subgroup G) V hV K
        (φ : MulAut (Vtil (⊥ : Subgroup G) V hV))).1 φ.2
      have hkY : (k : G) ∈ Y := (Subgroup.mem_inf.1 hkK).1
      have hkC : (k : G) ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.1 hkK).2
      obtain ⟨-, hks, hk1⟩ := (mem_cTilde_iff hV hMV).1 hkC
      have hkc : ∀ v ∈ V, (k : G) * v * (k : G)⁻¹ * v⁻¹ ∈ V₀ :=
        fun v hv => (actTil_eq_one_iff V₀ V hV ⟨(k : G), hks⟩).1 hk1 v hv
      rw [← hkφ]
      exact actTil_bot_sq_eq_one_of_commutator_le (V₀ := V₀) hV hV₀V hV₀Y hkY k.2 hkc
    exact CFSG.Quasithin.isPGroup_two_of_sq_eq_one fun φ => Subtype.ext (hsq φ)
  have hLbot : barSub (⊥ : Subgroup G) V hV K = ⊥ := by
    have := hLnorm
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hYbarq
      ((barSub (⊥ : Subgroup G) V hV K).subgroupOf
        (barSub (⊥ : Subgroup G) V hV Y)) with hLc | hLtop
    ·
      have hLp : IsPGroup 2 ↥((barSub (⊥ : Subgroup G) V hV K).subgroupOf
          (barSub (⊥ : Subgroup G) V hV Y)) :=
        hL2.of_equiv (Subgroup.subgroupOfEquivOfLe
          (barSub_mono (⊥ : Subgroup G) V hV hKY)).symm
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hLp
      have hdvd : Nat.card ↥((barSub (⊥ : Subgroup G) V hV K).subgroupOf
          (barSub (⊥ : Subgroup G) V hV Y)) ∣
          Nat.card (Subgroup.center ↥(barSub (⊥ : Subgroup G) V hV Y)) :=
        Subgroup.card_dvd_of_le hLc
      have hodd := odd_card_center_barSub hV hYs hYq (by simpa using h2) hY1
      have hm0 : m = 0 := by
        by_contra hm0
        have h2dvd : 2 ∣ Nat.card ↥((barSub (⊥ : Subgroup G) V hV K).subgroupOf
            (barSub (⊥ : Subgroup G) V hV Y)) := by
          rw [hm]; exact dvd_pow_self 2 hm0
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2dvd.trans hdvd))
      have hsub : (barSub (⊥ : Subgroup G) V hV K).subgroupOf
          (barSub (⊥ : Subgroup G) V hV Y) = ⊥ := by
        refine Subgroup.eq_bot_of_card_eq (H := (barSub (⊥ : Subgroup G) V hV K).subgroupOf
          (barSub (⊥ : Subgroup G) V hV Y)) ?_
        rw [hm, hm0, pow_zero]
      rw [eq_bot_iff]
      intro x hx
      have hLY : barSub (⊥ : Subgroup G) V hV K ≤ barSub (⊥ : Subgroup G) V hV Y :=
        barSub_mono (⊥ : Subgroup G) V hV hKY
      have hx' : (⟨x, hLY hx⟩ : ↥(barSub (⊥ : Subgroup G) V hV Y)) ∈
          (barSub (⊥ : Subgroup G) V hV K).subgroupOf (barSub (⊥ : Subgroup G) V hV Y) := hx
      rw [hsub, Subgroup.mem_bot] at hx'
      exact congrArg Subtype.val hx'
    ·
      have hLeq : barSub (⊥ : Subgroup G) V hV K = barSub (⊥ : Subgroup G) V hV Y := by
        rw [← Subgroup.map_subgroupOf_eq_of_le (barSub_mono (⊥ : Subgroup G) V hV hKY), hLtop]
        exact le_antisymm
          (Subgroup.map_subtype_le (⊤ : Subgroup ↥(barSub (⊥ : Subgroup G) V hV Y)))
          (fun x hx => ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩)
      have htop2 : IsPGroup 2 ↥(barSub (⊥ : Subgroup G) V hV Y) := hLeq ▸ hL2
      have : Group.IsPerfect ↥(barSub (⊥ : Subgroup G) V hV Y) := ⟨hYbarq.1⟩
      have : Group.IsNilpotent ↥(barSub (⊥ : Subgroup G) V hV Y) := htop2.isNilpotent
      have : Nontrivial ↥(barSub (⊥ : Subgroup G) V hV Y) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hY1
      exact ((Group.IsPerfect.not_isNilpotent (G := ↥(barSub (⊥ : Subgroup G) V hV Y)))
        inferInstance).elim
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hks : k ∈ stabTil (⊥ : Subgroup G) V :=
    Subgroup.mem_inf.2 ⟨(hY.1.le.trans hMV) (Subgroup.mem_inf.1 hk).1,
      by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top k⟩
  have hmem : actTil (⊥ : Subgroup G) V hV ⟨k, hks⟩ ∈ barSub (⊥ : Subgroup G) V hV K :=
    actTil_mem_barSub (⊥ : Subgroup G) V hV hk hks
  rw [hLbot, Subgroup.mem_bot] at hmem
  have h1 : k * v = v * k := by
    have h1c : k * v * k⁻¹ * v⁻¹ = 1 := by
      simpa using (actTil_eq_one_iff (⊥ : Subgroup G) V hV ⟨k, hks⟩).1 hmem v hv
    calc k * v = (k * v * k⁻¹ * v⁻¹) * (v * k) := by group
      _ = v * k := by rw [h1c, one_mul]
  exact h1.symm


theorem cTilde_eq_inf_centralizer {D : Data G} {V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hY : Y ∈ calC D.M) (hMY : D.M ≤ normalizer (Y : Set G))
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥)
    (hVY : ⁅V, Y⁆ = V) :
    F11.CTilde D.M (V ⊓ centralizer (Y : Set G)) V = D.M ⊓ centralizer (V : Set G) := by
  set V₀ : Subgroup G := V ⊓ centralizer (Y : Set G) with hV₀
  set C : Subgroup G := F11.CTilde D.M V₀ V with hCdef
  have hV₀V : V₀ ≤ V := hV₀ ▸ inf_le_left
  have hV₀Y : V₀ ≤ centralizer (Y : Set G) := hV₀ ▸ inf_le_right
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hV₀ ▸ (fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm))
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hCM : D.M ≤ normalizer (C : Set G) := by
    have hC_le : C ≤ D.M := by
      intro x hx
      exact ((mem_cTilde_iff hV hMV).1 hx).1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le).1
      (s15_Three_cTilde_normal hV hMs)
  have hYV₀ : ⁅V₀, Y⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hV₀Y
  have hYC_Y : ⁅Y, C⁆ ≤ Y := by
    refine Subgroup.commutator_le.mpr ?_
    intro y hy c hc
    have hcM : c ∈ D.M := ((mem_cTilde_iff hV hMV).1 hc).1
    have hcy : c * y * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.1 (hMY hcM) y).1 hy
    rw [commutatorElement_def, show y * c * y⁻¹ * c⁻¹ = y * (c * y * c⁻¹)⁻¹ by group]
    exact Y.mul_mem hy (Y.inv_mem hcy)
  have hYC_C : ⁅Y, C⁆ ≤ C := by
    refine Subgroup.commutator_le.mpr ?_
    intro y hy c hc
    have hyM : y ∈ D.M := hY.1.le hy
    rw [commutatorElement_def]
    exact C.mul_mem ((Subgroup.mem_normalizer_iff.1 (hCM hyM) c).1 hc) (C.inv_mem hc)
  have hYC_cent : ⁅Y, C⁆ ≤ centralizer (V : Set G) :=
    (le_inf hYC_Y hYC_C).trans
      (inf_cTilde_le_centralizer (D := D) (V := V) (Y := Y) hV hY hMY hVU hMV hYV)
  have hCV : ⁅C, V⁆ ≤ V₀ := by
    refine Subgroup.commutator_le.mpr ?_
    intro c hc v hv
    obtain ⟨-, hcs, hc1⟩ := (mem_cTilde_iff hV hMV).1 hc
    rw [commutatorElement_def]
    exact (actTil_eq_one_iff V₀ V hV ⟨c, hcs⟩).1 hc1 v hv
  have h1 : ⁅⁅Y, C⁆, V⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅Y, C⁆, V⁆ ≤ ⁅centralizer (V : Set G), V⁆ :=
        Subgroup.commutator_mono hYC_cent le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
  have h2 : ⁅⁅C, V⁆, Y⁆ = ⊥ := by
    refine eq_bot_iff.mpr ?_
    calc ⁅⁅C, V⁆, Y⁆ ≤ ⁅V₀, Y⁆ := Subgroup.commutator_mono hCV le_rfl
      _ = ⊥ := hYV₀
  have h3 : ⁅⁅V, Y⁆, C⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := V) (H₂ := Y) (H₃ := C) h1 h2
  rw [hVY] at h3
  have hVC : ⁅V, C⁆ = ⊥ := h3
  refine le_antisymm ?_ ?_
  · intro c hc
    rw [Subgroup.mem_inf]
    refine ⟨((mem_cTilde_iff hV hMV).1 hc).1, ?_⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm C V]; exact hVC)) hc
  · intro m hm
    rw [Subgroup.mem_inf] at hm
    obtain ⟨hmM, hmC⟩ := hm
    rw [mem_cTilde_iff hV hMV]
    refine ⟨hmM, ⟨Subgroup.mem_inf.2 ⟨hMV hmM, hMV₀ hmM⟩, ?_⟩⟩
    · refine (actTil_eq_one_iff V₀ V hV _).2 fun v hv => ?_
      change m * v * m⁻¹ * v⁻¹ ∈ V₀
      have hcomm : v * m = m * v := Subgroup.mem_centralizer_iff.1 hmC v hv
      have h1 : m * v * m⁻¹ * v⁻¹ = 1 := by rw [hcomm.symm]; group
      rw [hV₀, h1]
      exact Subgroup.mem_inf.2 ⟨V.one_mem, Subgroup.one_mem _⟩


theorem o2Trivial_mbar_of_min {D : Data G} {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = V ⊓ centralizer (Y : Set G)) (hY : Y ∈ calC D.M)
    (hMY : D.M ≤ normalizer (Y : Set G))
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥)
    (hVY : ⁅V, Y⁆ = V) (hTwo : TwoReduced D.M V) :
    O2Trivial (Mbar D.M V₀ V hV) := by
  intro P hPM hPN hP2
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hV₀ ▸ (fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm))
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hCeq : F11.CTilde D.M V₀ V = D.M ⊓ centralizer (V : Set G) := by
    rw [hV₀]
    exact cTilde_eq_inf_centralizer hV hY hMY hVU hMV hYV hVY
  set K : Subgroup G := preBarSub D.M V₀ V hV P with hKdef
  have hKM : K ≤ D.M := inf_le_left
  have hKleN : K ≤ normalizer (V : Set G) := hKM.trans hMV
  have hKnormal : (K.subgroupOf D.M).Normal := by
    refine Subgroup.Normal.mk ?_
    intro m hm k
    obtain ⟨hmK, hmS, hmP⟩ := (mem_preBarSub D.M V₀ V hV P).1 hm
    have hkS : (k : G) ∈ stabTil V₀ V := hMs k.2
    have hconjS : (k : G) * (m : G) * (k : G)⁻¹ ∈ stabTil V₀ V :=
      (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem hkS hmS) ((stabTil V₀ V).inv_mem hkS)
    change ((k : G) * (m : G) * (k : G)⁻¹) ∈ K
    refine (mem_preBarSub D.M V₀ V hV P).2
      ⟨D.M.mul_mem (D.M.mul_mem k.2 hmK) (D.M.inv_mem k.2), hconjS, ?_⟩
    have hφ : actTil V₀ V hV ⟨(k : G) * (m : G) * (k : G)⁻¹, hconjS⟩ =
        actTil V₀ V hV ⟨(k : G), hkS⟩ * actTil V₀ V hV ⟨(m : G), hmS⟩ *
          (actTil V₀ V hV ⟨(k : G), hkS⟩)⁻¹ := by
      rw [show (⟨(k : G) * (m : G) * (k : G)⁻¹, hconjS⟩ : ↥(stabTil V₀ V)) =
        ⟨(k : G), hkS⟩ * ⟨(m : G), hmS⟩ * ⟨(k : G), hkS⟩⁻¹ from Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc])]
      rw [map_mul, map_mul, map_inv]
    rw [hφ]
    have hmMbar : actTil V₀ V hV ⟨(m : G), hmS⟩ ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV hmK hmS
    have hkMbar : actTil V₀ V hV ⟨(k : G), hkS⟩ ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV k.2 hkS
    have hconj := hPN.conj_mem ⟨actTil V₀ V hV ⟨(m : G), hmS⟩, hmMbar⟩
      (Subgroup.mem_subgroupOf.mpr hmP) ⟨actTil V₀ V hV ⟨(k : G), hkS⟩, hkMbar⟩
    simpa using (Subgroup.mem_subgroupOf.mp hconj)
  have hMN : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hKnormal
  have hCK : D.M ⊓ centralizer (V : Set G) ≤ K := by
    have h1 : F11.CTilde D.M V₀ V ≤ K := by
      have hbot : F11.CTilde D.M V₀ V = preBarSub D.M V₀ V hV ⊥ :=
        cTilde_eq_preBarSub_bot hV hMV
      rw [hbot]
      intro x hx
      obtain ⟨hxM, hxs, hx1⟩ := (mem_preBarSub D.M V₀ V hV ⊥).1 hx
      exact (mem_preBarSub D.M V₀ V hV P).2 ⟨hxM, hxs, by rw [hx1]; exact Subgroup.one_mem P⟩
    rwa [hCeq] at h1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
  have hbarK : barSub V₀ V hV K = P := by
    rw [hKdef, barSub_preBarSub, inf_eq_left.mpr hPM]
  have hidx : ((Subgroup.centralizer (V : Set G)).subgroupOf K).index = 2 ^ n := by
    have hcard : Nat.card (barSub V₀ V hV K) =
        (K ⊓ F11.CTilde D.M V₀ V).relIndex K :=
      WeakClosure81.card_barSub_eq_relIndex hV hMV hMV₀ hKM
    rw [hbarK, hCeq, ← inf_assoc, inf_eq_left.mpr hKM, hn] at hcard
    have hrel : (K ⊓ centralizer (V : Set G)).relIndex K =
        ((K ⊓ centralizer (V : Set G)).subgroupOf K).index := rfl
    rw [← Subgroup.inf_subgroupOf_left (centralizer (V : Set G)) K, ← hrel]
    exact hcard.symm
  have hKcent : K ≤ Subgroup.centralizer (V : Set G) := hTwo K hKM hMN hCK ⟨n, hidx⟩
  refine le_bot_iff.1 ?_
  intro p hp
  obtain ⟨m, hmM, hmp⟩ := (mem_barSub V₀ V hV D.M p).1 (hPM hp)
  have hmK : (m : G) ∈ K := by
    refine (mem_preBarSub D.M V₀ V hV P).2 ⟨hmM, m.2, ?_⟩
    rwa [hmp]
  have hmC : (m : G) ∈ Subgroup.centralizer (V : Set G) := hKcent hmK
  rw [Subgroup.mem_bot, ← hmp, actTil_eq_one_iff]
  intro v hv
  have hcomm : v * (m : G) = (m : G) * v := Subgroup.mem_centralizer_iff.1 hmC v hv
  have h1 : (m : G) * v * (m : G)⁻¹ * v⁻¹ = 1 := by rw [hcomm.symm]; group
  rw [h1]
  exact V₀.one_mem


omit [Finite G] in
theorem inf_centralizer_le_cTilde {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G)) :
    M ⊓ centralizer (V : Set G) ≤ F11.CTilde M V₀ V := by
  rintro m ⟨hmM, hmC⟩
  rw [mem_cTilde_iff hV hM]
  refine ⟨hmM, ⟨Subgroup.mem_inf.2 ⟨hM hmM, hM₀ hmM⟩, ?_⟩⟩
  refine (actTil_eq_one_iff V₀ V hV _).2 fun v hv => ?_
  change m * v * m⁻¹ * v⁻¹ ∈ V₀
  have hcomm : v * m = m * v := Subgroup.mem_centralizer_iff.1 hmC v hv
  have h1 : m * v * m⁻¹ * v⁻¹ = 1 := by rw [hcomm.symm]; group
  rw [h1]
  exact V₀.one_mem

theorem isComponentOf_barSub_of_min {D : Data G} {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = V ⊓ centralizer (Y : Set G)) (hY : Y ∈ calC D.M)
    (hMY : D.M ≤ normalizer (Y : Set G)) (hVU : V ≤ D.U)
    (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥) :
    IsComponentOf (barSub V₀ V hV Y) (Mbar D.M V₀ V hV) := by
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hV₀ ▸ (fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm))
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hYs : Y ≤ stabTil V₀ V := hY.1.le.trans hMs
  have hperf : ⁅Y, Y⁆ = Y := hY.2.1
  have hYp : pCoreOf 2 Y ≤ centralizer (V : Set G) :=
    S17.seventeen_fiftyfive_min_pCore_le_centralizer hY hVU
  have hp_le : pCoreOf 2 Y ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hY.1.le
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ := by
    refine (WeakClosure81.barSub_eq_bot_iff (M := D.M) hV hMV hMV₀ hp_le).2 ?_
    intro x hx
    exact inf_centralizer_le_cTilde hV hMV hMV₀ ⟨hp_le hx, hYp hx⟩
  have hY1 : barSub V₀ V hV Y ≠ ⊥ :=
    barSub_ne_bot_of_min hV hV₀ hperf hYs hYV
  refine ⟨barSub_mono V₀ V hV hY.1.le, ?_,
    TwelveTwentyThree.isQuasisimple_barSub hV hYs hY.2.2 h2 hY1⟩
  exact TwelveTwentyThree.isSubnormal_barSub hV hY.1

theorem isSU3_barSub_of_min {D : Data G} {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀ : V₀ = V ⊓ centralizer (Y : Set G)) (hY : Y ∈ calC D.M)
    (hMY : D.M ≤ normalizer (Y : Set G))
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥)
    {n : ℕ} (hSU : IsSU3 (Bar2 Y) n) :
    IsSU3 ↥(barSub V₀ V hV Y) n := by
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hV₀ ▸ (fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm))
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hYs : Y ≤ stabTil V₀ V := hY.1.le.trans hMs
  have hYp : pCoreOf 2 Y ≤ centralizer (V : Set G) :=
    S17.seventeen_fiftyfive_min_pCore_le_centralizer hY hVU
  have hp_le : pCoreOf 2 Y ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hY.1.le
  have h2 : barSub V₀ V hV (pCoreOf 2 Y) = ⊥ := by
    refine (WeakClosure81.barSub_eq_bot_iff (M := D.M) hV hMV hMV₀ hp_le).2 ?_
    intro x hx
    exact inf_centralizer_le_cTilde hV hMV hMV₀ ⟨hp_le hx, hYp hx⟩
  have hY1 : barSub V₀ V hV Y ≠ ⊥ :=
    barSub_ne_bot_of_min hV hV₀ hY.2.1 hYs hYV
  let q := barSubBar2Hom (V₀ := V₀) hV hYs h2
  have hq : Function.Surjective q := barSubBar2Hom_surjective hV hYs h2
  have hnt : ∃ k : Bar2 Y, q k ≠ 1 := by
    have : Nontrivial ↥(barSub V₀ V hV Y) := (Subgroup.nontrivial_iff_ne_bot _).2 hY1
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(barSub V₀ V hV Y))
    obtain ⟨k, hk⟩ := hq g
    exact ⟨k, fun h1 => hg (by rw [← hk, h1])⟩
  have hqC : CFSG.IsQuasisimple (Bar2 Y) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 Y)).2.2.1.mpr hSU.1
  have hker : q.ker ≤ Subgroup.center (Bar2 Y) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hqC hnt
  refine ⟨TwelveTwentyThree.isQuasisimple_barSub hV hYs hY.2.2 h2 hY1,
    CFSG.Blueprint.LieModel.of_mulEquiv
      (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hqC hq hker) hSU.2⟩

theorem fixV_conjSet_barSub_eq_bot {D : Data G} {V₀ V Y : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV₀ : V₀ = V ⊓ centralizer (Y : Set G))
    (hY : Y ∈ calC D.M) (hMY : D.M ≤ normalizer (Y : Set G))
    (hMV : D.M ≤ normalizer (V : Set G)) :
    fixV (⨆ X ∈ conjSet (barSub V₀ V hV Y) (Mbar D.M V₀ V hV), X) = ⊥ := by
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hV₀ ▸ (fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm))
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hle : barSub V₀ V hV Y ≤ Mbar D.M V₀ V hV := barSub_mono V₀ V hV hY.1.le
  have hN : ((barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    barSub_subgroupOf_mbar_normal (V₀ := V₀) hV hY.1.le hMY
  rw [iSup_conjSet_eq_of_le_normalizer
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hN)]
  exact fixV_barSub_eq_bot_of_min hV hV₀ hY.2.1 (hY.1.le.trans hMs)


theorem rkIdx_le_of_map_le {W₁ W₂ : Type*} [CommGroup W₁] [CommGroup W₂]
    [Finite W₁] [Finite W₂] (q : W₁ →* W₂) (hq : Function.Surjective q)
    {H₁ : Subgroup W₁} {H₂ : Subgroup W₂} (h : H₁.map q ≤ H₂) :
    rkIdx H₂ ≤ rkIdx H₁ := by
  have hW : rk W₁ = rk W₂ + rk ↥q.ker := by
    have h1 := CFSG.Quasithin.B1More.card_map_mul_card_inf_ker (⊤ : Subgroup W₁) q
    rw [Subgroup.map_top_of_surjective q hq, top_inf_eq, Subgroup.card_top] at h1
    have h1' : Nat.card W₁ = Nat.card W₂ * Nat.card q.ker := by
      simpa using h1.symm
    unfold rk
    rw [h1', padicValNat.mul (Nat.card_pos (α := W₂)).ne'
      (Nat.card_pos (α := ↥(q.ker))).ne']
  have hH : rk H₁ = rk ↥(H₁.map q) + rk ↥(H₁ ⊓ q.ker) := by
    have h1 := CFSG.Quasithin.B1More.card_map_mul_card_inf_ker H₁ q
    have h1' : Nat.card ↥H₁ = Nat.card ↥(H₁.map q) * Nat.card ↥(H₁ ⊓ q.ker) := h1.symm
    unfold rk
    rw [h1', padicValNat.mul (Nat.card_pos (α := ↥(H₁.map q))).ne'
      (Nat.card_pos (α := ↥(H₁ ⊓ q.ker))).ne']
  have h1 : rk ↥H₁ + rkIdx H₁ = rk W₁ := rk_add_rkIdx H₁
  have h2 : rk ↥H₂ + rkIdx H₂ = rk W₂ := rk_add_rkIdx H₂
  have h3 : rk ↥(H₁.map q) + rkIdx (H₁.map q) = rk W₂ := rk_add_rkIdx (H₁.map q)
  have h4 : rk ↥(H₁.map q) ≤ rk ↥H₂ := rk_mono h
  have h5 : rk ↥(H₁ ⊓ q.ker) ≤ rk ↥q.ker := rk_mono inf_le_right
  omega

theorem rkIdx_fixV_zpowers_le_of_quotient {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {m : G} (hms : m ∈ stabTil V₀ V) (hm : m ∈ stabTil (⊥ : Subgroup G) V) :
    rkIdx (fixV (Subgroup.zpowers (actTil V₀ V hV ⟨m, hms⟩))) ≤
      rkIdx (fixV (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨m, hm⟩))) := by
  let q : Vtil (⊥ : Subgroup G) V hV →* Vtil V₀ V hV :=
    (mkTil V₀ V hV).comp (TwelveShort.mkTilEquiv V hV).symm.toMonoidHom
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV y
    exact ⟨(TwelveShort.mkTilEquiv V hV) x, by
      show mkTil V₀ V hV ((TwelveShort.mkTilEquiv V hV).symm
        ((TwelveShort.mkTilEquiv V hV) x)) = mkTil V₀ V hV x
      rw [(TwelveShort.mkTilEquiv V hV).symm_apply_apply]⟩
  have hq_act (x : Vtil (⊥ : Subgroup G) V hV) :
      q (actTil (⊥ : Subgroup G) V hV ⟨m, hm⟩ x) =
        actTil V₀ V hV ⟨m, hms⟩ (q x) := by
    obtain ⟨y, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV x
    have hq_mkTil : ∀ z : IntMod V hV, q (mkTil (⊥ : Subgroup G) V hV z) =
        mkTil V₀ V hV z := by
      intro z
      have hsymm : (TwelveShort.mkTilEquiv V hV).symm (mkTil (⊥ : Subgroup G) V hV z) = z := by
        rw [← TwelveShort.mkTilEquiv_apply V hV z]
        exact (TwelveShort.mkTilEquiv V hV).symm_apply_apply z
      show mkTil V₀ V hV ((TwelveShort.mkTilEquiv V hV).symm (mkTil (⊥ : Subgroup G) V hV z)) =
        mkTil V₀ V hV z
      rw [hsymm]
    rw [actTil_mk, hq_mkTil, hq_mkTil, actTil_mk]
    congr 1
  have hmap : (fixV (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV ⟨m, hm⟩))).map
      q ≤ fixV (Subgroup.zpowers (actTil V₀ V hV ⟨m, hms⟩)) := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_fixV_zpowers_iff] at hx ⊢
    rw [← hq_act x, hx]
  exact rkIdx_le_of_map_le q hq hmap

theorem mParam_mbar_eq_two_mul_of_le (hK : K_SU3NaturalModule) {D : Data G} {V Y : Subgroup G}
    {n : ℕ} (hV : IsElemAbelian 2 V) (hY : Y ∈ calC D.M)
    (hMY : D.M ≤ normalizer (Y : Set G)) (hSU : IsSU3 (Bar2 Y) n) (hn : 3 ≤ n)
    (hVU : V ≤ D.U) (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ normalizer (W : Set G) → W ≤ V →
      ⁅Y, W⁆ ≠ ⊥ → W = V)
    (hTwo : TwoReduced D.M V)
    (hsmall : E3.mParam (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) ≤ 2 * n + 2) :
    E3.mParam (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) = 2 * n := by
  have hVY : ⁅V, Y⁆ = V := by
    rw [Subgroup.commutator_comm]
    exact S17.seventeen_fiftyfive_min_commutator_eq hY hVU hMY hMV hYV hmin
  have hMs : D.M ≤ stabTil (V ⊓ centralizer (Y : Set G)) V :=
    le_stabTil hMV ((fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm)))
  have hcomp : IsComponentOf (barSub (V ⊓ centralizer (Y : Set G)) V hV Y)
      (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) :=
    isComponentOf_barSub_of_min hV rfl hY hMY hVU hMV hYV
  have hne : barSub (V ⊓ centralizer (Y : Set G)) V hV Y ≠ ⊥ :=
    barSub_ne_bot_of_min hV rfl hY.2.1 (hY.1.le.trans hMs) hYV
  have hSU' : IsSU3 ↥(barSub (V ⊓ centralizer (Y : Set G)) V hV Y) n :=
    isSU3_barSub_of_min hV rfl hY hMY hVU hMV hYV hSU
  have hO2 : O2Trivial (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) :=
    o2Trivial_mbar_of_min (V₀ := V ⊓ centralizer (Y : Set G)) hV rfl hY hMY hVU hMV hYV hVY hTwo
  have hbasic : IsBasicModule (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) :=
    isBasicModule_mbar_of_min hV hY hMY hVU hMV hYV hmin
  have hfix : fixV (⨆ X ∈ conjSet (barSub (V ⊓ centralizer (Y : Set G)) V hV Y)
      (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV), X) = ⊥ :=
    fixV_conjSet_barSub_eq_bot hV rfl hY hMY hMV
  exact (hK (Vtil (V ⊓ centralizer (Y : Set G)) V hV)
    (s15_Infra_vtil_sq_eq_one _ _ hV)
    (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV)
    (barSub (V ⊓ centralizer (Y : Set G)) V hV Y) n
    (barSub_mono _ _ _ hY.1.le) hcomp hne hSU' hn hO2 hbasic hfix hsmall).2

theorem two_mul_le_mBar_of_min (hK : K_SU3NaturalModule) {D : Data G} {Y V : Subgroup G}
    (hV : IsElemAbelian 2 V) {n : ℕ} (hY : Y ∈ calC D.M) (hMY : D.M ≤ normalizer (Y : Set G))
    (hSU : IsSU3 (Bar2 Y) n) (hn : 3 ≤ n) (hVU : V ≤ D.U)
    (hMV : D.M ≤ normalizer (V : Set G)) (hYV : ⁅Y, V⁆ ≠ ⊥)
    (hmin : ∀ W : Subgroup G, W ≤ D.U → D.M ≤ normalizer (W : Set G) → W ≤ V →
      ⁅Y, W⁆ ≠ ⊥ → W = V)
    (hTwo : TwoReduced D.M V) : 2 * n ≤ mBar D.M ⊥ V hV := by
  let V₀ : Subgroup G := V ⊓ centralizer (Y : Set G)
  have hV₀ : V₀ = V ⊓ centralizer (Y : Set G) := rfl
  have hV₀V : V₀ ≤ V := inf_le_left
  have hMV₀ : D.M ≤ normalizer (V₀ : Set G) :=
    fun _ hm => CFSG.GroupTheory.mem_normalizer_inf_centralizer (hMY hm) (hMV hm)
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hMV hMV₀
  have hVY : ⁅V, Y⁆ = V := by
    rw [Subgroup.commutator_comm]
    exact S17.seventeen_fiftyfive_min_commutator_eq hY hVU hMY hMV hYV hmin
  have h2n : 2 * n ≤ E3.mParam (Mbar D.M V₀ V hV) := by
    by_cases hsmall : E3.mParam (Mbar D.M V₀ V hV) ≤ 2 * n + 2
    · have hsmall' : E3.mParam (Mbar D.M (V ⊓ centralizer (Y : Set G)) V hV) ≤ 2 * n + 2 := by
        simpa [hV₀] using hsmall
      have h := mParam_mbar_eq_two_mul_of_le hK hV hY hMY hSU hn hVU hMV hYV hmin hTwo hsmall'
      rw [show E3.mParam (Mbar D.M V₀ V hV) = 2 * n from by simpa [hV₀] using h]
    · omega
  have hbound : ∀ (t : MulAut (Vtil (⊥ : Subgroup G) V hV)), t ∈ Mbar D.M (⊥ : Subgroup G) V hV →
      orderOf t = 2 → 2 * n ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t ht ht2
    obtain ⟨m, hm, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV D.M t).1 ht
    have hmV : (m : G) ∈ stabTil (⊥ : Subgroup G) V := m.2
    have hms : (m : G) ∈ stabTil V₀ V := hMs hm
    let t' : MulAut (Vtil V₀ V hV) := actTil V₀ V hV ⟨(m : G), hms⟩
    have ht'mem : t' ∈ Mbar D.M V₀ V hV := actTil_mem_barSub V₀ V hV hm hms
    have hstab : actStab V₀ V hV ⟨(m : G), hms⟩ = actStab (⊥ : Subgroup G) V hV ⟨(m : G), hmV⟩ :=
      rfl
    have ht'2 : t' * t' = 1 := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV y
      show t' (t' (mkTil V₀ V hV x)) = mkTil V₀ V hV x
      have ht2' : (actTil (⊥ : Subgroup G) V hV ⟨(m : G), hmV⟩) ^ 2 = 1 := by
        rw [← ht2]; exact pow_orderOf_eq_one _
      have hx : actStab (⊥ : Subgroup G) V hV ⟨(m : G), hmV⟩
          (actStab (⊥ : Subgroup G) V hV ⟨(m : G), hmV⟩ x) = x := by
        have h := congrArg (fun f : MulAut (Vtil (⊥ : Subgroup G) V hV) =>
          f (mkTil (⊥ : Subgroup G) V hV x)) ht2'
        rw [pow_two, MulAut.mul_apply, MulAut.one_apply, actTil_mk, actTil_mk] at h
        apply (TwelveShort.mkTilEquiv V hV).injective
        simpa [TwelveShort.mkTilEquiv_apply] using h
      simp only [t', actTil_mk]
      rw [hstab, hx]
    have ht'ne : t' ≠ 1 := by
      intro h1
      have hmC : (m : G) ∈ F11.CTilde D.M V₀ V := by
        rw [mem_cTilde_iff hV hMV]
        exact ⟨hm, ⟨hms, h1⟩⟩
      rw [cTilde_eq_inf_centralizer hV hY hMY hVU hMV hYV hVY] at hmC
      have hmc : (m : G) ∈ centralizer (V : Set G) := hmC.2
      have ht1 : actTil (⊥ : Subgroup G) V hV ⟨(m : G), hmV⟩ = 1 := by
        refine MulEquiv.ext fun y => ?_
        obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV y
        rw [actTil_mk, MulAut.one_apply]
        congr 1
        apply IntMod.val_injective
        rw [actStab_apply_val]
        show (m : G) * x.val * (m : G)⁻¹ = x.val
        have hcomm : x.val * (m : G) = (m : G) * x.val :=
          Subgroup.mem_centralizer_iff.1 hmc x.val x.val_mem
        rw [hcomm.symm]; group
      rw [ht1, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have ht'ord : orderOf t' = 2 := orderOf_eq_prime (by rwa [pow_two]) ht'ne
    have hP2 : IsPGroup 2 (Subgroup.zpowers t') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'ord]; norm_num)
    have hz : Subgroup.zpowers t' ≠ ⊥ := by
      intro hbot
      apply ht'ne
      have hmem : t' ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
        rw [← hbot]; exact Subgroup.mem_zpowers t'
      simpa using hmem
    have hle1 : E3.mParam (Mbar D.M V₀ V hV) ≤ rkIdx (fixV (Subgroup.zpowers t')) :=
      E3.mParam_le_rkIdx_fixV (Subgroup.zpowers_le.mpr ht'mem) hP2 hz
    have hle2 : rkIdx (fixV (Subgroup.zpowers t')) ≤
        rkIdx (fixV (Subgroup.zpowers (actTil (⊥ : Subgroup G) V hV m))) :=
      rkIdx_fixV_zpowers_le_of_quotient hV hms hmV
    omega
  unfold mBar
  rw [E3.mParam]
  split_ifs with heven
  · refine le_csInf ?_ ?_
    · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Mbar D.M (⊥ : Subgroup G) V hV) 2
        (even_iff_two_dvd.mp heven)
      exact ⟨_, ⟨t, t.2, (Subgroup.orderOf_coe t).trans ht, rfl⟩⟩
    · rintro k ⟨t, ht, ht2, rfl⟩
      exact hbound t ht ht2
  ·
    have h1 : E3.mParam (Mbar D.M V₀ V hV) ≤ rk (Vtil V₀ V hV) := E3.mParam_le_rk _
    have h2 : rk (Vtil V₀ V hV) ≤ rk (Vtil (⊥ : Subgroup G) V hV) := by
      have hcard1 : Nat.card (Vtil (⊥ : Subgroup G) V hV) = Nat.card ↥V :=
        (Nat.card_congr (TwelveShort.mkTilEquiv V hV).toEquiv).symm
      have hcard2 : Nat.card ↥V = Nat.card ↥V₀ * Nat.card (Vtil V₀ V hV) :=
        card_Vtil_eq V₀ V hV hV₀V
      unfold rk
      refine padicValNat_two_le_of_dvd (Nat.card_pos.ne') ?_
      rw [hcard1, hcard2]
      exact dvd_mul_left _ _
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
