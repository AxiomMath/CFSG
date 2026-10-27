module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubComponent
public import CFSG.LocalAnalysis.UniquenessCase.UCKP1
public import CFSG.LocalAnalysis.WeakClosure81.W16Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3NaturalModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyEight

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem uc2_17_39_rMV_ge (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G)
    {V₀ V L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (h17_35 : R17_35At D V₀ V) (h0 : V₀ ≠ ⊥) :
    ((2 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V := by
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 c.hyp125 h0
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UCK.u3Range (Bar2 L) n c.shape
  have hm : mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := (h17_35.1 L n c).2
  have hm1 : 2 < mBar D.M V₀ V c.hyp125.isElemAbelian := by rw [hm]; omega
  have h := h162 D V₀ V hW h0 hm1
  have hmV0 : 1 ≤ mSub V₀ := by
    have hpos : 0 < CFSG.Quasithin.rk ↥V₀ := by
      by_contra h
      have hz : CFSG.Quasithin.rk ↥V₀ = 0 := by omega
      exact h0 ((CFSG.Quasithin.rk_eq_zero_iff_of_isPGroup
        c.hyp125.pairFacts.elemAbelian₀.isPGroup).1 hz)
    change 1 ≤ CFSG.Quasithin.rk ↥V₀
    omega
  rw [hm] at h
  refine le_trans ?_ h
  exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * n + mSub V₀)

theorem uc2_17_39_mbar_le_normalizer {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (h17_36a : R17_36aAt D V₀ V) :
    Mbar D.M V₀ V c.hyp125.isElemAbelian ≤
      Subgroup.normalizer
        (barSub V₀ V c.hyp125.isElemAbelian L :
          Set (MulAut (Vtil V₀ V c.hyp125.isElemAbelian))) := by
  have hLM : L ≤ D.M := c.mem_calC.1.le
  have hLbM : barSub V₀ V c.hyp125.isElemAbelian L ≤
      Mbar D.M V₀ V c.hyp125.isElemAbelian :=
    barSub_mono V₀ V c.hyp125.isElemAbelian hLM
  have hnormal := barSub_subgroupOf_mbar_normal (V₀ := V₀) (V := V)
    c.hyp125.isElemAbelian hLM (uc2_17_36a_normal c h17_36a)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLbM).1 hnormal

theorem uc2_17_39_conj_inf_conj_eq_bot {D : Data G} {V₀ V : Subgroup G}
    (hs : WeakClosureSetting D V₀ V) (h0 : V₀ ≠ ⊥) {g : G} (hgM : g ∉ D.M) :
    V₀ ⊓ conjSubgroup V₀ g = ⊥ :=
  inf_conjSubgroup_eq_bot_of_isTI (hs.ti₀ h0).1 fun heq =>
    hgM (hs.normalizer₀ h0 ▸ conjSubgroup_eq_iff_mem_normalizer.1 heq)

theorem s17_commutator_of_add_lt {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (hs : WeakClosureSetting D V₀ V) (h0 : V₀ ≠ ⊥)
    (hrMV : ((mBar D.M V₀ V hV.isElemAbelian + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V)
    {g : G} (hgM : g ∉ D.M) (hAgT : conjSubgroup V g ≤ D.T)
    {B : Subgroup G} (hBA : B ≤ conjSubgroup V g)
    (hlt : E3.mQuot (conjSubgroup V g) B + mSub V₀ < mBar D.M V₀ V hV.isElemAbelian)
    {u : G} (hu : u ∈ preCTilde V₀ V B hV.isElemAbelian) :
    u ∈ conjSubgroup D.M g ∧
      (∀ v ∈ conjSubgroup V g, u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V₀ g) ∧
      ⁅B, Subgroup.zpowers u⁆ = ⊥ := by
  have hP := hV.pairFacts
  have hAM : conjSubgroup V g ≤ D.M := hAgT.trans D.sylowM.le
  have hAgTil : conjSubgroup V g ≤ stabTil V₀ V :=
    hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hBTil : B ≤ stabTil V₀ V := hBA.trans hAgTil
  have huV : u ∈ V := preCTilde_le V₀ V B hV.isElemAbelian hu
  have huB : ∀ b ∈ B, ⁅u, b⁆ ∈ V₀ :=
    (mem_preCTilde_iff hV.isElemAbelian hBTil huV).1 hu
  have hBT : B ≤ D.T := hBA.trans hAgT
  set D₀ : Subgroup G := B ⊓ Subgroup.centralizer ({u} : Set G) with hD₀
  have hD₀B : D₀ ≤ B := inf_le_left
  have hD₀A : D₀ ≤ conjSubgroup V g := hD₀B.trans hBA
  have hBV : B ≤ normalizer (V : Set G) := (hBT.trans D.sylowM.le).trans hP.le_normalizer
  have hV₀N : V ≤ normalizer (V₀ : Set G) := hP.le_M.trans hP.le_normalizer₀
  have hmD₀ : E3.mQuot B D₀ ≤ mSub V₀ := by
    simpa [hD₀] using
      mQuot_inf_centralizer_le_mSub hV.isElemAbelian hBV hP.le hV₀N huV huB
  have hquot : E3.mQuot (conjSubgroup V g) D₀ ≤
      E3.mQuot (conjSubgroup V g) B + mSub V₀ := by
    calc E3.mQuot (conjSubgroup V g) D₀
        = E3.mQuot B D₀ + E3.mQuot (conjSubgroup V g) B := E3.mQuot_add hD₀B hBA
      _ ≤ mSub V₀ + E3.mQuot (conjSubgroup V g) B := Nat.add_le_add_right hmD₀ _
      _ = E3.mQuot (conjSubgroup V g) B + mSub V₀ := Nat.add_comm _ _
  have hD₀lt : E3.mQuot (conjSubgroup V g) D₀ < mBar D.M V₀ V hV.isElemAbelian :=
    lt_of_le_of_lt hquot hlt
  have h62 : Hyp62 D.M V₀ V := Hyp125.hyp62 hV
  have hr : ((E3.mQuot (conjSubgroup V g) D₀ + mSub V₀ : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast Nat.add_lt_add_right hD₀lt (mSub V₀)) hrMV
  have hfix : fixV (barSub V₀ V hV.isElemAbelian B) ≤
      fixV (barSub V₀ V hV.isElemAbelian D₀) := by
    intro x hx
    rw [mem_fixV] at hx ⊢
    intro φ hφ
    exact hx φ (barSub_mono V₀ V hV.isElemAbelian hD₀B hφ)
  have huPreD : u ∈ preCTilde V₀ V D₀ hV.isElemAbelian := by
    rw [preCTilde] at hu ⊢
    rw [mem_preTil] at hu ⊢
    obtain ⟨y, hy, hmem⟩ := hu
    exact ⟨y, hy, hfix hmem⟩
  have huMg : u ∈ conjSubgroup D.M g :=
    six_two_one h62 (le_inf hD₀A (hD₀A.trans hAM)) (by simpa [hD₀] using hr) huPreD
  have hVg := E3.isElemAbelian_conjSubgroup hV.isElemAbelian g
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hP.le
  have hMg : conjSubgroup D.M g ≤ normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact E3.conjSubgroup_mono_left g hP.le_normalizer
  have hM₀g : conjSubgroup D.M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← E3.conjSubgroup_normalizer]
    exact E3.conjSubgroup_mono_left g hP.le_normalizer₀
  set C : Subgroup G := conjSubgroup V g ⊓ Subgroup.centralizer ({u} : Set G) with hC
  have hD₀C : D₀ ≤ C := by
    rw [hC, hD₀]
    exact inf_le_inf hBA (le_rfl : Subgroup.centralizer ({u} : Set G) ≤ _)
  have hCV : C ≤ conjSubgroup V g := inf_le_left
  have hCu : C ≤ Subgroup.centralizer ({u} : Set G) := inf_le_right
  have hu2 : u ^ 2 = 1 := by
    have := hV.isElemAbelian.2 u huV
    simpa using this
  have huord : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.2 hu2
  have huord2 : ∃ k : ℕ, orderOf u = 2 ^ k := by
    rcases (Nat.dvd_prime Nat.prime_two).1 huord with h1 | h2
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h2, pow_one]⟩
  have hmBconj : mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg =
      mBar D.M V₀ V hV.isElemAbelian :=
    mBar_conj D.M V₀ V hV.isElemAbelian hP.le hP.le_normalizer hP.le_normalizer₀ g
  have hltC : (E3.mQuot (conjSubgroup V g) C : ℕ∞) <
      mBar (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg := by
    rw [hmBconj]
    have h1 : E3.mQuot (conjSubgroup V g) C ≤ E3.mQuot (conjSubgroup V g) D₀ :=
      E3.mQuot_mono hD₀C
    have h2 : (E3.mQuot (conjSubgroup V g) C : ℕ∞) ≤
        (E3.mQuot (conjSubgroup V g) B + mSub V₀ : ℕ) := by
      exact_mod_cast le_trans h1 hquot
    exact lt_of_le_of_lt h2 (by exact_mod_cast hlt)
  have huCtilde : u ∈ F11.CTilde (conjSubgroup D.M g) (conjSubgroup V₀ g) (conjSubgroup V g) :=
    mem_cTilde_of_mQuot_lt hVg hV₀g hMg hM₀g huMg huord2 hCV hCu hltC
  have huTil : ∀ v ∈ conjSubgroup V g, u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V₀ g := by
    obtain ⟨-, hgs, hact⟩ := (mem_cTilde_iff hVg hMg).1 huCtilde
    intro v hv
    have := (actTil_eq_one_iff (conjSubgroup V₀ g) (conjSubgroup V g) hVg ⟨u, hgs⟩).1 hact v hv
    simpa [mul_assoc] using this
  refine ⟨huMg, huTil, ?_⟩
  have hV₀g_bot : V₀ ⊓ conjSubgroup V₀ g = ⊥ :=
    uc2_17_39_conj_inf_conj_eq_bot hs h0 hgM
  have hbu : ∀ b ∈ B, b * u = u * b := by
    intro b hb
    have hbA : b ∈ conjSubgroup V g := hBA hb
    have h1 : ⁅b, u⁆ ∈ V₀ := by
      have h := V₀.inv_mem (huB b hb)
      rwa [show ⁅u, b⁆⁻¹ = ⁅b, u⁆ by
        rw [commutatorElement_def, commutatorElement_def]; group] at h
    have h2 : ⁅b, u⁆ ∈ conjSubgroup V₀ g := by
      have h := (conjSubgroup V₀ g).inv_mem (huTil b hbA)
      rwa [show (u * b * u⁻¹ * b⁻¹)⁻¹ = ⁅b, u⁆ by
        rw [commutatorElement_def]; group] at h
    have hmem : ⁅b, u⁆ ∈ V₀ ⊓ conjSubgroup V₀ g := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [hV₀g_bot] at hmem
    have hcomm : ⁅b, u⁆ = 1 := Subgroup.mem_bot.1 hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 hcomm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
    Subgroup.zpowers_le]
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact hbu b hb

theorem uc2_17_39_commutator_general {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n) (hs : WeakClosureSetting D V₀ V)
    (h17_35 : R17_35At D V₀ V) (h17_38 : R17_38At D V₀ V) (h0 : V₀ ≠ ⊥)
    (hrMV : ((2 * n + 1 : ℕ) : ℕ∞) ≤ rMV D.M V)
    {g : G} (hgM : g ∉ D.M) (hAgT : conjSubgroup V g ≤ D.T)
    {B : Subgroup G} (hBA : B ≤ conjSubgroup V g) {m : ℕ}
    (hmB : E3.mQuot (conjSubgroup V g) B = m) (hmn : m ≤ n)
    {u : G} (hu : u ∈ preCTilde V₀ V B c.hyp125.isElemAbelian) :
    u ∈ conjSubgroup D.M g ∧
      (∀ v ∈ conjSubgroup V g, u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V₀ g) ∧
      ⁅B, Subgroup.zpowers u⁆ = ⊥ := by
  have hV := c.hyp125.isElemAbelian
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UCK.u3Range (Bar2 L) n c.shape
  have hmBar2n : mBar D.M V₀ V hV = 2 * n := (h17_35.1 L n c).2
  have hmSub : mSub V₀ ≤ 1 := h17_38 L n c
  have hrMV' : ((mBar D.M V₀ V hV + mSub V₀ : ℕ) : ℕ∞) ≤ rMV D.M V := by
    rw [hmBar2n]
    have h : 2 * n + mSub V₀ ≤ 2 * n + 1 := by omega
    exact (by exact_mod_cast h :
      ((2 * n + mSub V₀ : ℕ) : ℕ∞) ≤ ((2 * n + 1 : ℕ) : ℕ∞)).trans hrMV
  have hlt : E3.mQuot (conjSubgroup V g) B + mSub V₀ < mBar D.M V₀ V hV := by
    rw [hmB, hmBar2n]
    omega
  exact s17_commutator_of_add_lt c.hyp125 hs h0 hrMV' hgM hAgT hBA hlt hu

theorem uc2_17_39_commutator_eq_bot_of_w16One (h161 : W16One G) {D : Data G} {V₀ V : Subgroup G}
    (h : WeakClosureSetting D V₀ V) (h0 : V₀ ≠ ⊥)
    (hm1 : 1 < mBar D.M V₀ V h.isElemAbelian) {g : G} {B : Subgroup G}
    (hBA : B ≤ conjSubgroup V g)
    (hlt : E3.mQuot (conjSubgroup V g) B < mBar D.M V₀ V h.isElemAbelian)
    (hVM : V ≤ conjSubgroup D.M g) (hVB : V ≤ centralizer (B : Set G)) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  set U : Subgroup G := conjSubgroup B g⁻¹ with hU
  have hUV : U ≤ V := by
    have := E3.conjSubgroup_mono_left g⁻¹ hBA
    rwa [E3.conjSubgroup_conj_inv] at this
  have hlt' : E3.mQuot V (U ⊔ V₀) < mBar D.M V₀ V h.isElemAbelian := by
    refine lt_of_le_of_lt (E3.mQuot_mono le_sup_left) ?_
    have := E3.mQuot_conjSubgroup (conjSubgroup V g) B g⁻¹
    rw [E3.conjSubgroup_conj_inv] at this
    rw [hU, this]
    exact hlt
  have hAg : conjSubgroup V g⁻¹ ≤ D.M ⊓ centralizer (U : Set G) := by
    refine le_inf ?_ ?_
    · have := E3.conjSubgroup_mono_left g⁻¹ hVM
      rwa [E3.conjSubgroup_conj_inv] at this
    · have := E3.conjSubgroup_mono_left g⁻¹ hVB
      rwa [E3.conjSubgroup_centralizer] at this
  have hW : conjSubgroup V g⁻¹ ≤ E3.wClos V 0 (D.M ⊓ centralizer (U : Set G)) :=
    E3.le_wClos ⟨hAg, g⁻¹, le_rfl, E3.mQuot_self _⟩
  have hC : conjSubgroup V g⁻¹ ≤ centralizer (V : Set G) :=
    hW.trans (h161 (Std15.of_data D) (Hyp15.of_setting h h0) hm1 hUV hlt')
  have h1 : ⁅conjSubgroup V g⁻¹, V⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2 hC
  have h2 := congrArg (fun X => conjSubgroup X g) h1
  simp only [E3.conjSubgroup_commutator, E3.conjSubgroup_inv_conj, E3.conjSubgroup_bot] at h2
  exact h2

theorem uc2_17_39_final_step (h161 : W16One G) {D : Data G} {V₀ V : Subgroup G}
    (h : WeakClosureSetting D V₀ V) (h0 : V₀ ≠ ⊥)
    (hm1 : 1 < mBar D.M V₀ V h.isElemAbelian) {g : G}
    (hlt : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ F11.CTilde D.M V₀ V) <
      mBar D.M V₀ V h.isElemAbelian)
    (hBu : ∀ u ∈ V, ∀ b ∈ conjSubgroup V g ⊓ F11.CTilde D.M V₀ V, b * u = u * b)
    (hAu : ∀ u ∈ V, ∀ a ∈ conjSubgroup V g, ⁅a, u⁆ ∈ conjSubgroup V₀ g) :
    ⁅V, conjSubgroup V g⁆ = ⊥ := by
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g h.pair.le
  have hVN : V ≤ normalizer (conjSubgroup V g : Set G) := by
    intro u hu
    have hfwd : ∀ a ∈ conjSubgroup V g, u * a * u⁻¹ ∈ conjSubgroup V g := by
      intro a ha
      have hc : ⁅a, u⁆ ∈ conjSubgroup V g := hV₀g (hAu u hu a ha)
      have : u * a * u⁻¹ = (⁅a, u⁆)⁻¹ * a := by
        rw [commutatorElement_def]; group
      rw [this]
      exact (conjSubgroup V g).mul_mem ((conjSubgroup V g).inv_mem hc) ha
    exact Subgroup.mem_normalizer_fintype hfwd
  have hVM : V ≤ conjSubgroup D.M g := by
    rw [← h.normalizer_eq, E3.conjSubgroup_normalizer]
    exact hVN
  have hVB : V ≤ centralizer ((conjSubgroup V g ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBu u hu b hb
  exact uc2_17_39_commutator_eq_bot_of_w16One h161 h h0 hm1 inf_le_left hlt hVM hVB

theorem s17_exists_conj_not_le_cTilde_of_add_lt (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h0 : V₀ ≠ ⊥)
    (hm2 : 2 < mBar D.M V₀ V hV.isElemAbelian)
    (hV0 : ∀ g : G, g ∉ D.M → conjSubgroup V g ≤ D.T →
      mSub V₀ < mBar D.M V₀ V hV.isElemAbelian)
    (hN : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) :
    ∃ g : G, g ∉ D.M ∧ conjSubgroup V g ≤ D.T ∧ ¬ conjSubgroup V g ≤ F11.CTilde D.M V₀ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 hV h0
  have hP := hV.pairFacts
  have hrMV := h162 D V₀ V hs h0 hm2
  by_contra hcon
  push Not at hcon
  have hW : E3.wClos V 0 D.T ≤ centralizer (V : Set G) := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm0⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff
        (E3.isPGroup_conjSubgroup hV.isElemAbelian.isPGroup g) hAg).1 hm0
    subst hAeq
    by_cases hgM : g ∈ D.M
    · have hVg : conjSubgroup V g = V :=
        conjSubgroup_eq_iff_mem_normalizer.2 (hs.normalizer_eq ▸ hgM)
      rw [hVg]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact hV.isElemAbelian.comm hu ha
    · have hAC := hcon g hgM hAT
      have hAM : conjSubgroup V g ≤ D.M := hAT.trans D.sylowM.le
      have hAst : conjSubgroup V g ≤ stabTil V₀ V :=
        hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hupre : u ∈ preCTilde V₀ V (conjSubgroup V g) hV.isElemAbelian := by
        rw [mem_preCTilde_iff hV.isElemAbelian hAst hu]
        intro d hd
        have h1 := (FourteenTwo.mem_cTilde_iff_comm.1 (hAC hd)).2.2 u hu
        have h2 : ⁅u, d⁆ = (d * u * d⁻¹ * u⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [h2]
        exact V₀.inv_mem h1
      have hlt : E3.mQuot (conjSubgroup V g) (conjSubgroup V g) + mSub V₀ <
          mBar D.M V₀ V hV.isElemAbelian := by
        rw [E3.mQuot_self, Nat.zero_add]
        exact hV0 g hgM hAT
      have hcomm := (s17_commutator_of_add_lt hV hs h0 hrMV hgM hAT (le_refl _) hlt
        hupre).2.2
      have hC : conjSubgroup V g ≤ centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hcomm
      have := (Subgroup.mem_centralizer_iff.1 (hC ha)) u (Subgroup.mem_zpowers u)
      exact this
  set Q : Subgroup G := D.T ⊓ (D.M ⊓ centralizer (V : Set G)) with hQ
  have hNH : D.M ⊓ centralizer (V : Set G) ≤ D.M := inf_le_left
  have hnormal : ((D.M ⊓ centralizer (V : Set G)).subgroupOf D.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
    intro x hxM
    have hxV : x ∈ normalizer (V : Set G) := hs.normalizer_eq ▸ hxM
    have hxC : x ∈ normalizer (centralizer (V : Set G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer] at hxV ⊢
      rw [E3.conjSubgroup_centralizer, hxV]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hxM, hxC⟩
  have hTsyl : IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  have hSyl : IsSylowIn 2 Q (D.M ⊓ centralizer (V : Set G)) := hTsyl.inf_normal hNH hnormal
  have hWQ : E3.wClos V 0 D.T ≤ Q :=
    le_inf (E3.wClos_le 0 D.T) (le_inf ((E3.wClos_le 0 D.T).trans D.sylowM.le) hW)
  have heq : E3.wClos V 0 D.T = E3.wClos V 0 Q :=
    le_antisymm (E3.wClos_le_of_forall fun A hA =>
      E3.le_wClos ⟨(E3.le_wClos hA).trans hWQ, hA.2⟩)
      (E3.wClos_mono (inf_le_left : Q ≤ D.T))
  have hNQ : normalizer (Q : Set G) ≤ normalizer (E3.wClos V 0 D.T : Set G) := by
    rw [heq]
    exact E3.normalizer_le_normalizer_wClos Q
  have hU : InCalU D.M (D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G)) :=
    InCalU.mono D.maxLocal (hs.v1 Q ((CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).2 hSyl))
      (inf_le_inf_left D.M hNQ) inf_le_left
  have hVT : V ≤ D.T := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22p_le_T_of_inCalV D
    hV.inCalV
  have hVW : V ≤ E3.wClos V 0 D.T :=
    E3.le_wClos ⟨hVT, 1, by rw [conjSubgroup_one], by
      rw [conjSubgroup_one]; exact E3.mQuot_self V⟩
  have hWne : E3.wClos V 0 D.T ≠ ⊥ := by
    intro hb
    rw [hb] at hVW
    exact hP.ne_bot (le_bot_iff.1 hVW)
  have hW2 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    (D.sylowM.isPGroup).to_le (E3.wClos_le 0 D.T)
  exact hN (normalizer_le_of_inCalU hU inf_le_right hWne hW2)

theorem exists_conj_not_le_cTilde (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G)
    {V₀ V L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (h17_35 : R17_35At D V₀ V) (h17_38 : R17_38At D V₀ V) (h0 : V₀ ≠ ⊥)
    (hN : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M) :
    ∃ g : G, g ∉ D.M ∧ conjSubgroup V g ≤ D.T ∧ ¬ conjSubgroup V g ≤ F11.CTilde D.M V₀ V := by
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UCK.u3Range (Bar2 L) n c.shape
  have hmBar2n : mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := (h17_35.1 L n c).2
  have hm2 : 2 < mBar D.M V₀ V c.hyp125.isElemAbelian := by rw [hmBar2n]; omega
  have hmSub : mSub V₀ ≤ 1 := h17_38 L n c
  have hV0 : ∀ g : G, g ∉ D.M → conjSubgroup V g ≤ D.T →
      mSub V₀ < mBar D.M V₀ V c.hyp125.isElemAbelian := by
    intro g _ _
    rw [hmBar2n]
    omega
  exact s17_exists_conj_not_le_cTilde_of_add_lt D hx h61 h127 h1114 h162 c.hyp125 h0 hm2 hV0 hN

theorem mkTil_commutator_eq {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (αs : stabTil V₀ V) (x : IntMod V hV) :
    mkTil V₀ V hV (actStab V₀ V hV αs x * x⁻¹) =
      actTil V₀ V hV αs (mkTil V₀ V hV x) * (mkTil V₀ V hV x)⁻¹ := by
  rw [map_mul, map_inv, actTil_mk]

theorem uc2_17_39_exists_commutator_notMem {D : Data G} {V₀ V L : Subgroup G} {n : ℕ}
    (c : Ctx17_33 D V₀ V L n)
    {Lb : Subgroup (MulAut (Vtil V₀ V c.hyp125.isElemAbelian))}
    {A : Subgroup G}
    {Ab : Subgroup (MulAut (Vtil V₀ V c.hyp125.isElemAbelian))}
    (hAb : Ab = barSub V₀ V c.hyp125.isElemAbelian A)
    (hβ : CFSG.Quasithin.commSub (CFSG.Quasithin.fixV (Ab ⊓ Lb)) Ab ≠ ⊥) :
    ∃ a ∈ A, ∃ u ∈ preCTilde V₀ V
      (preBarSub A V₀ V c.hyp125.isElemAbelian (Ab ⊓ Lb)) c.hyp125.isElemAbelian,
      ⁅a, u⁆ ∉ V₀ := by
  have hV := c.hyp125.isElemAbelian
  set B : Subgroup G := preBarSub A V₀ V hV (Ab ⊓ Lb) with hB
  have hbarB : barSub V₀ V hV B = Ab ⊓ Lb := by
    rw [hB, barSub_preBarSub]
    have hM : Mbar A V₀ V hV = Ab := hAb.symm
    rw [hM]
    exact inf_eq_left.mpr inf_le_left
  have hex : ∃ a ∈ Ab, ∃ w ∈ CFSG.Quasithin.fixV (Ab ⊓ Lb), a w * w⁻¹ ≠ 1 := by
    by_contra hcon
    apply hβ
    rw [CFSG.Quasithin.commSub, Subgroup.closure_eq_bot_iff]
    rintro y ⟨a, ha, w, hw, rfl⟩
    by_contra hy
    exact hcon ⟨a, ha, w, hw, hy⟩
  obtain ⟨a, ha, w, hw, hne⟩ := hex
  rw [hAb] at ha
  obtain ⟨αs, hαA, hαa⟩ := (mem_barSub V₀ V hV A a).1 ha
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hxB : x.val ∈ preCTilde V₀ V B hV := by
    rw [preCTilde, mem_preTil]
    exact ⟨x, rfl, by rwa [hbarB]⟩
  refine ⟨αs.1, hαA, x.val, hxB, ?_⟩
  intro hmem
  apply hne
  have himg : mkTil V₀ V hV (actStab V₀ V hV αs x * x⁻¹) =
      a (mkTil V₀ V hV x) * (mkTil V₀ V hV x)⁻¹ := by
    rw [mkTil_commutator_eq, ← hαa]
  have hval : (actStab V₀ V hV αs x * x⁻¹).val = ⁅αs.1, x.val⁆ := by
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, commutatorElement_def]
  have himg1 : mkTil V₀ V hV (actStab V₀ V hV αs x * x⁻¹) = 1 := by
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) _).2 (by
      rw [mem_modNull, hval]
      exact hmem)
  rw [himg] at himg1
  exact himg1

theorem uc2_17_39_isQuadratic_of_commutator {D : Data G} {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) {A : Subgroup G}
    (hcomm : ⁅⁅V, A⁆, A⁆ = ⊥) :
    CFSG.Quasithin.IsQuadratic (barSub V₀ V h.isElemAbelian A) := by
  have hV := h.isElemAbelian
  set Ab : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV A with hAb
  rw [CFSG.Quasithin.isQuadratic_iff_commSeries_two]
  rw [show CFSG.Quasithin.commSeries Ab 2 = CFSG.Quasithin.commSub (CFSG.Quasithin.commV Ab) Ab by
    simp [CFSG.Quasithin.commSeries, CFSG.Quasithin.commIter, CFSG.Quasithin.commV_eq_commSub]]
  rw [CFSG.Quasithin.commSub_eq_bot_iff]
  intro w hw
  rw [CFSG.Quasithin.commV_eq_commSub] at hw
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨a, ha, x, hxgen, hyw⟩ := hy
      subst hyw
      obtain ⟨x0, rfl⟩ := mkTil_surjective V₀ V hV x
      obtain ⟨αs, hαA, hαa⟩ := (mem_barSub V₀ V hV A a).1 ha
      rw [CFSG.Quasithin.mem_fixV]
      intro b hb
      obtain ⟨βs, hβA, hβb⟩ := (mem_barSub V₀ V hV A b).1 hb
      have hcommV : ⁅αs.1, x0.val⁆ ∈ ⁅V, A⁆ := by
        have h1 : ⁅αs.1, x0.val⁆ = ⁅x0.val, αs.1⁆⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [h1]
        exact (⁅V, A⁆).inv_mem (Subgroup.commutator_mem_commutator x0.val_mem hαA)
      have hcomm2 : ⁅⁅αs.1, x0.val⁆, βs.1⁆ = 1 := by
        have hmem : ⁅⁅αs.1, x0.val⁆, βs.1⁆ ∈ ⁅⁅V, A⁆, A⁆ :=
          Subgroup.commutator_mem_commutator hcommV hβA
        rw [hcomm] at hmem
        exact Subgroup.mem_bot.1 hmem
      have hfix : βs.1 * (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) * βs.1⁻¹ =
          αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹ := by
        have hcval : ⁅αs.1, x0.val⁆ = αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹ :=
          commutatorElement_def _ _
        rw [hcval, commutatorElement_def] at hcomm2
        have hcm : (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) * βs.1 =
            βs.1 * (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) := by
          calc (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) * βs.1
              = ((αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) * βs.1 *
                  (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹)⁻¹ * βs.1⁻¹) *
                  (βs.1 * (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹)) := by group
            _ = βs.1 * (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) := by rw [hcomm2]; group
        calc βs.1 * (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) * βs.1⁻¹
            = (αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹) * βs.1 * βs.1⁻¹ := by rw [hcm]
          _ = αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹ := by group
      have hval : (actStab V₀ V hV αs x0 * x0⁻¹).val =
          αs.1 * x0.val * αs.1⁻¹ * x0.val⁻¹ := by
        rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
      have himg : mkTil V₀ V hV (actStab V₀ V hV αs x0 * x0⁻¹) =
          a (mkTil V₀ V hV x0) * (mkTil V₀ V hV x0)⁻¹ := by
        rw [mkTil_commutator_eq, ← hαa]
      have hact : b (mkTil V₀ V hV (actStab V₀ V hV αs x0 * x0⁻¹)) =
          mkTil V₀ V hV (actStab V₀ V hV αs x0 * x0⁻¹) := by
        rw [← hβb, actTil_mk]
        apply congrArg (mkTil V₀ V hV)
        apply IntMod.val_injective
        rw [actStab_apply_val, hval]
        exact hfix
      rw [himg] at hact
      exact hact
  | one => exact (CFSG.Quasithin.fixV Ab).one_mem
  | mul x y hx hy ihx ihy => exact (CFSG.Quasithin.fixV Ab).mul_mem ihx ihy
  | inv x hx ih => exact (CFSG.Quasithin.fixV Ab).inv_mem ih

theorem s17_false_of_conj_rk_add_lt (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G) (h161 : W16One G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h0 : V₀ ≠ ⊥)
    (hm2 : 2 < mBar D.M V₀ V hV.isElemAbelian)
    {g : G} (hgM : g ∉ D.M) (hAgT : conjSubgroup V g ≤ D.T)
    (hAgne : ¬ conjSubgroup V g ≤ F11.CTilde D.M V₀ V)
    (hlt : CFSG.Quasithin.rk ↥(barSub V₀ V hV.isElemAbelian (conjSubgroup V g)) + mSub V₀ <
      mBar D.M V₀ V hV.isElemAbelian) :
    False := by
  have hP := hV.pairFacts
  have hs := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 hV h0
  have hrMV := h162 D V₀ V hs h0 hm2
  have hm1 : 1 < mBar D.M V₀ V hV.isElemAbelian := by omega
  have hAM : conjSubgroup V g ≤ D.M := hAgT.trans D.sylowM.le
  set A : Subgroup G := conjSubgroup V g with hA
  set B : Subgroup G := A ⊓ F11.CTilde D.M V₀ V with hB
  have hBA : B ≤ A := by rw [hB]; exact inf_le_left
  have hBA' : B ≤ conjSubgroup V g := by rw [← hA]; exact hBA
  have hquot : E3.mQuot (conjSubgroup V g) B =
      CFSG.Quasithin.rk ↥(barSub V₀ V hV.isElemAbelian (conjSubgroup V g)) := by
    rw [hB, hA]
    exact (rk_barSub_eq_mQuot_inf_cTilde hV.isElemAbelian hP.le_normalizer hP.le_normalizer₀
      hAM).symm
  have hltB : E3.mQuot (conjSubgroup V g) B + mSub V₀ <
      mBar D.M V₀ V hV.isElemAbelian := by
    rw [hquot]
    exact hlt
  have hlt' : E3.mQuot (conjSubgroup V g) B < mBar D.M V₀ V hV.isElemAbelian :=
    lt_of_le_of_lt (Nat.le_add_right _ _) hltB
  have hpreV : ∀ u ∈ V, u ∈ preCTilde V₀ V B hV.isElemAbelian := by
    intro u hu
    have hAst : B ≤ stabTil V₀ V :=
      (hBA.trans hAM).trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
    rw [mem_preCTilde_iff hV.isElemAbelian hAst hu]
    intro b hb
    have hbC : b ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_inf.1 (hB ▸ hb)).2
    obtain ⟨-, hbs, hact⟩ := (mem_cTilde_iff hV.isElemAbelian hP.le_normalizer).1 hbC
    have h1 := (actTil_eq_one_iff V₀ V hV.isElemAbelian ⟨b, hbs⟩).1 hact u hu
    have h2 : ⁅u, b⁆ = (b * u * b⁻¹ * u⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [h2]
    exact V₀.inv_mem h1
  have hdata : ∀ u ∈ V, u ∈ conjSubgroup D.M g ∧
      (∀ v ∈ A, u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V₀ g) ∧
      ⁅B, Subgroup.zpowers u⁆ = ⊥ := by
    intro u hu
    have h := s17_commutator_of_add_lt hV hs h0 hrMV hgM hAgT hBA' hltB (hpreV u hu)
    simpa [hA] using h
  have hBu : ∀ u ∈ V, ∀ b ∈ B, b * u = u * b := by
    intro u hu b hb
    have hcomm : ⁅B, Subgroup.zpowers u⁆ = ⊥ := (hdata u hu).2.2
    have hcen : b ∈ Subgroup.centralizer (Subgroup.zpowers u : Set G) := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      exact hcomm hb
    have h := (Subgroup.mem_centralizer_iff.1 hcen) u (Subgroup.mem_zpowers u)
    exact h.symm
  have hAu : ∀ u ∈ V, ∀ a ∈ A, ⁅a, u⁆ ∈ conjSubgroup V₀ g := by
    intro u hu a ha
    have h := (hdata u hu).2.1 a ha
    have hinv : (u * a * u⁻¹ * a⁻¹)⁻¹ ∈ conjSubgroup V₀ g :=
      (conjSubgroup V₀ g).inv_mem h
    rwa [show (u * a * u⁻¹ * a⁻¹)⁻¹ = ⁅a, u⁆ by
      rw [commutatorElement_def]; group] at hinv
  have hVA : ⁅V, A⁆ = ⊥ :=
    uc2_17_39_final_step h161 hs h0 hm1 (by simpa [hB, hA] using hlt') (by
      intro u hu b hb
      exact hBu u hu b (by rw [hB]; exact hb)) (by
      intro u hu a ha
      exact hAu u hu a (by rw [hA]; exact ha))
  have hAV : A ≤ Subgroup.centralizer (V : Set G) := by
    have hcent : V ≤ Subgroup.centralizer (A : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hVA
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact ((Subgroup.mem_centralizer_iff.1 (hcent hv)) a ha).symm
  apply hAgne
  intro a ha
  rw [mem_cTilde_iff hV.isElemAbelian hP.le_normalizer]
  have hAst : A ≤ stabTil V₀ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  refine ⟨hAM (hA ▸ ha), hAst (hA ▸ ha), ?_⟩
  refine (actTil_eq_one_iff V₀ V hV.isElemAbelian ⟨a, hAst (hA ▸ ha)⟩).2 ?_
  intro v hv
  have h : a * v = v * a := (Subgroup.mem_centralizer_iff.1 (hAV (hA ▸ ha)) v hv).symm
  have h1 : a * v * a⁻¹ * v⁻¹ = 1 := by
    calc a * v * a⁻¹ * v⁻¹ = v * a * a⁻¹ * v⁻¹ := by rw [h]
      _ = 1 := by group
  rw [h1]
  exact V₀.one_mem

theorem uc2_17_39_case_le (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G) (h161 : W16One G)
    {V₀ V L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (h17_35 : R17_35At D V₀ V) (h17_38 : R17_38At D V₀ V) (h0 : V₀ ≠ ⊥)
    {g : G} (hgM : g ∉ D.M) (hAgT : conjSubgroup V g ≤ D.T)
    (hAgne : ¬ conjSubgroup V g ≤ F11.CTilde D.M V₀ V)
    (hle : CFSG.Quasithin.rk ↥(barSub V₀ V c.hyp125.isElemAbelian (conjSubgroup V g)) ≤ n) :
    False := by
  have hV := c.hyp125.isElemAbelian
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UCK.u3Range (Bar2 L) n c.shape
  have hmBar2n : mBar D.M V₀ V hV = 2 * n := (h17_35.1 L n c).2
  have hm2 : 2 < mBar D.M V₀ V hV := by rw [hmBar2n]; omega
  have hmSub : mSub V₀ ≤ 1 := h17_38 L n c
  have hlt : CFSG.Quasithin.rk ↥(barSub V₀ V hV (conjSubgroup V g)) + mSub V₀ <
      mBar D.M V₀ V hV := by
    rw [hmBar2n]
    omega
  exact s17_false_of_conj_rk_add_lt D hx h61 h127 h1114 h162 h161 c.hyp125 h0 hm2 hgM hAgT
    hAgne hlt

theorem uc2_17_39_case_succ (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G)
    {V₀ V L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (h17_35 : R17_35At D V₀ V) (h17_36a : R17_36aAt D V₀ V)
    (h17_38 : R17_38At D V₀ V) (h0 : V₀ ≠ ⊥)
    {g : G} (hgM : g ∉ D.M) (hAgT : conjSubgroup V g ≤ D.T)
    (hgt : n < CFSG.Quasithin.rk ↥(barSub V₀ V c.hyp125.isElemAbelian (conjSubgroup V g))) :
    False := by
  have hV := c.hyp125.isElemAbelian
  have hP := c.hyp125.pairFacts
  have hs := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 c.hyp125 h0
  have hrMV := uc2_17_39_rMV_ge D hx h61 h127 h1114 h162 c h17_35 h0
  have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UCK.u3Range (Bar2 L) n c.shape
  have hAM : conjSubgroup V g ≤ D.M := hAgT.trans D.sylowM.le
  set A : Subgroup G := conjSubgroup V g with hA
  set Ab : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV A with hAb
  set Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L with hLb
  set X : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV with hX
  have hLnat : CNatModSU3 (Vtil V₀ V hV) Lb n := by
    rw [hLb]
    exact uc2_17_38_cNatModSU3 c h17_35 h17_36a h0
  have hXnorm : X ≤ Subgroup.normalizer (Lb : Set (MulAut (Vtil V₀ V hV))) := by
    rw [hX, hLb]
    exact uc2_17_39_mbar_le_normalizer c h17_36a
  have hAbX : Ab ≤ X := by
    rw [hAb, hX, hA]
    exact barSub_mono V₀ V hV hAM
  have hAel : IsElemAbelian 2 Ab := by
    have hAelG : IsElemAbelian 2 A := by
      rw [hA]
      exact E3.isElemAbelian_conjSubgroup hV g
    rw [hAb, hA]
    exact IsElemAbelian.map
      (IsElemAbelian.comap hAelG (stabTil V₀ V).subtype_injective) (actTil V₀ V hV)
  have hAelA : IsElemAbelian 2 A := by
    rw [hA]; exact E3.isElemAbelian_conjSubgroup hV g
  have hpRank : CFSG.Open.pRank 2 Ab ≤ n + 1 :=
    rank_of_cNatModSU3 hLnat hXnorm hAbX
  have hrk : CFSG.Quasithin.rk ↥Ab = n + 1 := by
    have hle : CFSG.Quasithin.rk ↥Ab ≤ CFSG.Open.pRank 2 Ab := by
      refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl hAel ?_
      rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup hAel.isPGroup]
    have hgt' : n < CFSG.Quasithin.rk ↥Ab := by
      rw [hAb, hA]; exact hgt
    omega
  have hcardAb : Nat.card ↥Ab = 2 ^ (n + 1) := by
    rw [CFSG.Quasithin.card_eq_two_pow_of_isPGroup hAel.isPGroup, hrk]
  have hindex : Nat.card ↥Ab ≤ 2 * Nat.card ↥(Ab ⊓ Lb) :=
    index_of_cNatModSU3 hLnat hXnorm hAbX hAel
  have hquot_le : E3.mQuot Ab (Ab ⊓ Lb) ≤ 1 := by
    have hrel_le : (Ab ⊓ Lb).relIndex Ab ≤ 2 := by
      have hmul := Subgroup.relIndex_mul_card (H := Ab ⊓ Lb) (K := Ab)
      rw [inf_eq_left.mpr (inf_le_left : Ab ⊓ Lb ≤ Ab)] at hmul
      have h1 : (Ab ⊓ Lb).relIndex Ab * Nat.card ↥(Ab ⊓ Lb) ≤
          2 * Nat.card ↥(Ab ⊓ Lb) := by rw [hmul]; exact hindex
      exact Nat.le_of_mul_le_mul_right h1 (Nat.card_pos)
    have hrel_pos : 0 < (Ab ⊓ Lb).relIndex Ab :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    have hrel_cases : (Ab ⊓ Lb).relIndex Ab = 1 ∨ (Ab ⊓ Lb).relIndex Ab = 2 := by omega
    rcases hrel_cases with h1 | h2
    · simp [E3.mQuot, h1]
    · simp [E3.mQuot, h2]
  set B : Subgroup G := preBarSub A V₀ V hV (Ab ⊓ Lb) with hB
  have hAst : A ≤ stabTil V₀ V := hAM.trans (le_stabTil hP.le_normalizer hP.le_normalizer₀)
  have hC_le : Ab ⊓ Lb ≤ Ab := inf_le_left
  have hBquot : E3.mQuot A B = E3.mQuot Ab (Ab ⊓ Lb) := by
    rw [hB, hAb, hA]
    exact (mQuot_barSub_preBarSub_gen hV hAst hC_le).symm
  have hBmn : E3.mQuot A B ≤ n := by rw [hBquot]; omega
  have hdata : ∀ u ∈ preCTilde V₀ V B hV, u ∈ conjSubgroup D.M g ∧
      (∀ v ∈ A, u * v * u⁻¹ * v⁻¹ ∈ conjSubgroup V₀ g) ∧
      ⁅B, Subgroup.zpowers u⁆ = ⊥ := by
    intro u hu
    have hBA : B ≤ A := by rw [hB]; exact inf_le_left
    exact uc2_17_39_commutator_general c hs h17_35 h17_38 h0 hrMV hgM hAgT
      hBA (m := E3.mQuot A B) rfl hBmn hu
  have hnotL : ¬ Ab ≤ Lb := by
    intro hle
    have hAbLel : IsElemAbelian 2 (Ab ⊓ Lb) := by
      have : IsMulCommutative ↥Ab := hAel.1
      refine ⟨?_, ?_⟩
      · infer_instance
      · intro x hx
        exact hAel.2 x ((inf_le_left : Ab ⊓ Lb ≤ Ab) hx)
    have hcard : Nat.card ↥(Ab ⊓ Lb) = 2 ^ CFSG.Quasithin.rk ↥(Ab ⊓ Lb) :=
      CFSG.Quasithin.card_eq_two_pow_of_isPGroup hAbLel.isPGroup
    have hlin_le : CFSG.Open.pRank 2 (Ab ⊓ Lb) ≤ n :=
      linear_rank_of_cNatModSU3 hLnat hXnorm hAbX
    have hrank_le : CFSG.Quasithin.rk ↥(Ab ⊓ Lb) ≤ n := by
      have h := CFSG.SectionRank.le_pRank (p := 2) (by norm_num) le_rfl hAbLel hcard
      omega
    have hrk_le : CFSG.Quasithin.rk ↥Ab ≤ n := by
      calc CFSG.Quasithin.rk ↥Ab = CFSG.Quasithin.rk ↥(Ab ⊓ Lb) := by
            rw [inf_eq_left.mpr hle]
        _ ≤ n := hrank_le
    omega
  have hβ' : CFSG.Quasithin.commSub (CFSG.Quasithin.fixV (Ab ⊓ Lb)) Ab ≠ ⊥ :=
    nontrivial_comm_of_cNatModSU3 hLnat hXnorm hAbX hAel hnotL
  obtain ⟨a, haA, u, huU, hcomm_not⟩ :=
    uc2_17_39_exists_commutator_notMem c (Ab := Ab) hAb hβ'
  have huV : u ∈ V := preCTilde_le V₀ V B hV huU
  have hdatau := hdata u huU
  have hcommV₀g : ⁅a, u⁆ ∈ conjSubgroup V₀ g := by
    have h := hdatau.2.1 a haA
    have hinv : (u * a * u⁻¹ * a⁻¹)⁻¹ ∈ conjSubgroup V₀ g :=
      (conjSubgroup V₀ g).inv_mem h
    rwa [show (u * a * u⁻¹ * a⁻¹)⁻¹ = ⁅a, u⁆ by
      rw [commutatorElement_def]; group] at hinv
  have hcommV : ⁅a, u⁆ ∈ V := by
    have haN : a ∈ normalizer (V : Set G) := hP.le_normalizer (hAM haA)
    rw [commutatorElement_def]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 haN u).1 huV) (V.inv_mem huV)
  have hV₀g_le_V : conjSubgroup V₀ g ≤ V := by
    have hne : ⁅a, u⁆ ≠ 1 := fun h1 => hcomm_not (h1 ▸ V₀.one_mem)
    have hrk0 : CFSG.Quasithin.rk ↥V₀ = 1 := by
      have hle1 : CFSG.Quasithin.rk ↥V₀ ≤ 1 := h17_38 L n c
      have hpos : 0 < CFSG.Quasithin.rk ↥V₀ := by
        by_contra h
        have hz : CFSG.Quasithin.rk ↥V₀ = 0 := by omega
        exact h0 ((CFSG.Quasithin.rk_eq_zero_iff_of_isPGroup hP.elemAbelian₀.isPGroup).1 hz)
      omega
    have hcard : Nat.card ↥(conjSubgroup V₀ g) = 2 := by
      rw [E3.card_conjSubgroup,
        CFSG.Quasithin.card_eq_two_pow_of_isPGroup hP.elemAbelian₀.isPGroup, hrk0]
      norm_num
    have hsub : Subgroup.zpowers ⁅a, u⁆ ≤ conjSubgroup V₀ g := Subgroup.zpowers_le.2 hcommV₀g
    have hcardz : Nat.card ↥(Subgroup.zpowers ⁅a, u⁆) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by simpa [pow_two] using hV.2 ⁅a, u⁆ hcommV) hne
    have heq : Subgroup.zpowers ⁅a, u⁆ = conjSubgroup V₀ g :=
      Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hcardz])
    rw [← heq]
    exact Subgroup.zpowers_le.2 hcommV
  have hVleC : V ≤ Subgroup.centralizer (conjSubgroup V₀ g : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (@mul_comm' ↥V _ hV.1 ⟨w, hV₀g_le_V hw⟩ ⟨v, hv⟩)
  have hVleMg : V ≤ conjSubgroup D.M g := by
    have hN : Subgroup.normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup D.M g := by
      rw [← E3.conjSubgroup_normalizer, hs.normalizer₀ h0]
    exact hVleC.trans ((Subgroup.centralizer_le_normalizer _).trans (le_of_eq hN))
  have hcommVA_le_A : ⁅V, A⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have hVA : Subgroup.normalizer (A : Set G) = conjSubgroup D.M g := by
      rw [hA, ← E3.conjSubgroup_normalizer, hs.normalizer_eq]
    have hvN : v ∈ normalizer (A : Set G) := by
      rw [hVA]; exact hVleMg hv
    rw [commutatorElement_def]
    exact A.mul_mem ((Subgroup.mem_normalizer_iff.1 hvN a).1 ha) (A.inv_mem ha)
  have hAA : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (@mul_comm' ↥A _ hAelA.1 ⟨b, hb⟩ ⟨a, ha⟩)
  have hcommVAA : ⁅⁅V, A⁆, A⁆ = ⊥ := by
    refine le_bot_iff.1 ?_
    calc ⁅⁅V, A⁆, A⁆ ≤ ⁅A, A⁆ := Subgroup.commutator_mono hcommVA_le_A le_rfl
      _ = ⊥ := hAA
  have hAnz : Ab ⊓ Lb ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(Ab ⊓ Lb) = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 := index_of_cNatModSU3 hLnat hXnorm hAbX hAel
    rw [h1] at h2
    rw [hcardAb] at h2
    norm_num at h2
    have h3 : 8 ≤ 2 ^ (n + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hquad : CFSG.Quasithin.IsQuadratic Ab := by
    rw [hAb, hA]
    exact uc2_17_39_isQuadratic_of_commutator c.hyp125 hcommVAA
  exact not_quadratic_of_cNatModSU3 hLnat hXnorm hAbX hAel hnotL hAnz hquad

theorem uc2_17_39_not_normalizer (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h183 : W3Thm183 G)
    {V₀ V L : Subgroup G} {n : ℕ} (c : Ctx17_33 D V₀ V L n)
    (h17_35 : R17_35At D V₀ V) (h0 : V₀ ≠ ⊥) :
    ¬ Subgroup.normalizer (CFSG.Quasithin.E3.wClos V 0 D.T : Set G) ≤ D.M := by
  have hm2 : MBarGT D.M V₀ V 2 := by
    refine (c.hyp125.mBarGT_iff_lt_mBar 2).2 ?_
    have hn : 2 ≤ n := CFSG.LocalAnalysis.UniquenessCase.UCK.u3Range (Bar2 L) n c.shape
    have hm : mBar D.M V₀ V c.hyp125.isElemAbelian = 2 * n := (h17_35.1 L n c).2
    rw [hm]
    omega
  exact twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 c.hyp125 h0 hm2

theorem seventeen_thirtynine (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G)
    (h183 : W3Thm183 G) (h161 : W16One G)
    {V₀ V : Subgroup G} (h17_35 : R17_35At D V₀ V) (h17_36a : R17_36aAt D V₀ V)
    (h17_38 : R17_38At D V₀ V) :
    R17_39At D V₀ V := by
  intro L n c
  by_contra h0
  have hN := uc2_17_39_not_normalizer D hx h61 h66 h127 h1114 h183 c h17_35 h0
  obtain ⟨g, hgM, hAgT, hAgne⟩ :=
    exists_conj_not_le_cTilde D hx h61 h127 h1114 h162 c h17_35 h17_38 h0 hN
  by_cases hle : CFSG.Quasithin.rk ↥(barSub V₀ V c.hyp125.isElemAbelian
      (conjSubgroup V g)) ≤ n
  · exact uc2_17_39_case_le D hx h61 h127 h1114 h162 h161 c h17_35 h17_38 h0 hgM hAgT
      hAgne hle
  · exact uc2_17_39_case_succ D hx h61 h127 h1114 h162 c h17_35 h17_36a
      h17_38 h0 hgM hAgT (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
