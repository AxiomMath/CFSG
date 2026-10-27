module

public import CFSG.Quasithin.Background.D1Statement
public import CFSG.Quasithin.Background.A4Defs
import CFSG.Quasithin.Background.SimsD1Twelve
import CFSG.Quasithin.EmptyFaithfulMultiple.InputD14Proof

public section

namespace CFSG.Quasithin.SimsD1.Four

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

theorem not_pCoreOf_le_pCoreOf (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    ¬ pCoreOf 2 G₁ ≤ pCoreOf 2 G₂ := by
  intro hle
  have hC := D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  rw [inf_eq_left.mpr hle] at hC
  have hR : pCoreOf 2 G₁ = ⊥ := h.no_normal _ le_rfl
    ((Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 G₁).trans le_sup_left)).mpr
      (sup_le (le_normalizer_pCoreOf 2 G₁) hC))
  exact h.nontrivial (le_bot_iff.mp (hR ▸ A4.le_pCoreOf_of_isTwoReducedIn h.reduced))

theorem minParabolic (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    MinParabolic G₂ T M₂ := by
  refine ⟨h.sylow₂, fun hN => not_pCoreOf_le_pCoreOf h hVR₂ hchief hdual
    (h.pCoreOf_le_T.trans ?_), h.unique_max⟩
  exact le_pCoreOf_of_le_normalizer 2 h.sylow₂.1 hN h.sylow₂.2.1

theorem not_thompsonJ_le_pCoreOf (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    ¬ thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₂ := by
  intro hle
  have hC := D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  have hJR : thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₁ := B6.thompsonJ_le _
  have hJ : thompsonJ (pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂) = thompsonJ (pCoreOf 2 G₁) :=
    B6.thompsonJ_eq_of_le (le_inf hJR hle) inf_le_left
  have h2 : G₂ ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 G₁) : Set G) := by
    rw [← hJ]
    exact hC.trans (normalizer_le_normalizer_thompsonJ _)
  have h1 : G₁ ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 G₁) : Set G) :=
    (le_normalizer_pCoreOf 2 G₁).trans (normalizer_le_normalizer_thompsonJ _)
  have hnorm : ((thompsonJ (pCoreOf 2 G₁)).subgroupOf (G₁ ⊔ G₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hJR.trans ((pCoreOf_le 2 G₁).trans le_sup_left))).mpr (sup_le h1 h2)
  have hR : pCoreOf 2 G₁ ≠ ⊥ := fun hR =>
    h.nontrivial (le_bot_iff.mp (hR ▸ A4.le_pCoreOf_of_isTwoReducedIn h.reduced))
  exact thompsonJ_ne_bot_of_isPGroup (pCoreOf_isPGroup 2 G₁) hR (h.no_normal _ hJR hnorm)

theorem isElemAbelian_conjClosure (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    IsElemAbelian 2 (conjClosure V G₂) := by
  have hC := D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  have hV := h.reduced.2.2.1
  have hVR := A4.le_pCoreOf_of_isTwoReducedIn h.reduced
  have hUQ : conjClosure V G₂ ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hC hg) v).mp ⟨hVR hv, hVR₂ hv⟩
  have hQU := D15Proof.le_centralizer_conjClosure h hC
  refine B2F.isElemAbelian_closure ?_ ?_
  · rintro _ ⟨k, hk, z, hz, rfl⟩ _ ⟨k', hk', z', hz', rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hQU (hUQ (mem_conjClosure hk hz))) _
      (mem_conjClosure hk' hz')).symm
  · rintro _ ⟨k, hk, z, hz, rfl⟩
    rw [conj_pow, hV.2 z hz]
    group

theorem commutator_le_centerOf (h : D11Hyp G₁ G₂ T V M₂) (hmp : MinParabolic G₂ T M₂)
    (hRR₂ : ¬ pCoreOf 2 G₁ ≤ pCoreOf 2 G₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) := by
  have hC := D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  set R := pCoreOf 2 G₁
  set R₂ := pCoreOf 2 G₂
  set U := conjClosure V G₂
  set P := oTwoUpper G₂ with hPdef
  rw [F6.twoResidual_eq_oTwoUpper G₂]
  have hR₂P : ⁅R₂, P⁆ ≤ R ⊓ R₂ := D15Proof.commutator_pCoreOf_le h hmp hRR₂ hC
  have hQU : R ⊓ R₂ ≤ Subgroup.centralizer (U : Set G) :=
    D15Proof.le_centralizer_conjClosure h hC
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUG₂ : U ≤ G₂ := hUR₂.trans (pCoreOf_le 2 G₂)
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 G₂).to_le hUR₂
  have hPG₂ : P ≤ G₂ := oTwoUpper_le G₂
  set I := ⁅U, P⁆
  have hIU : I ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp (hPG₂.trans hG₂U)
  have hG₂I : G₂ ≤ Subgroup.normalizer (I : Set G) :=
    D14.le_normalizer_commutator hG₂U (le_normalizer_oTwoUpper G₂)
  set W := I ⊓ Subgroup.centralizer (R₂ : Set G)
  have hWU : W ≤ U := inf_le_left.trans hIU
  have hG₂W : G₂ ≤ Subgroup.normalizer (W : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hG₂I hg, B6.le_normalizer_centralizer hG₂R₂ hg⟩
  have hWP : ⁅W, P⁆ ≠ ⊥ := by
    intro hbot
    let ρ : G₂ →* MulAut I := I.normalizerMonoidHom.comp (Subgroup.inclusion hG₂I)
    have hρ : ∀ (g : G₂) (y : I), ((ρ g y : I) : G) = (g : G) * y * (g : G)⁻¹ := fun g y =>
      Subgroup.normalizerMonoidHom_apply_apply_coe I (Subgroup.inclusion hG₂I g) y
    have hρ1 : ∀ g : G₂, (g : G) ∈ Subgroup.centralizer (I : Set G) → ρ g = 1 := by
      intro g hg
      ext y
      rw [hρ, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.mp hg y y.2
      rw [← this, mul_inv_cancel_right]
    have hI2 : IsPGroup 2 I := hU2.to_le hIU
    set B : Subgroup G₂ := R₂.subgroupOf G₂
    have hB2 : IsPGroup 2 (B.map ρ) :=
      IsPGroup.map ((pCoreOf_isPGroup 2 G₂).comap_of_injective G₂.subtype
        G₂.subtype_injective) ρ
    have hodd : ∀ x ∈ G₂, Odd (orderOf x) → x ∈ Subgroup.centralizer (I : Set G) := by
      intro x hx hxo
      have hxP : x ∈ P := mem_oTwoUpper_of_odd hx hxo
      have ha : (orderOf (⟨x, hx⟩ : G₂)).Coprime 2 := by
        rw [Subgroup.orderOf_mk]
        exact Nat.coprime_two_right.mpr hxo
      have hcomm : ∀ b ∈ B, ρ ⟨x, hx⟩ * ρ b = ρ b * ρ ⟨x, hx⟩ := by
        intro b hb
        have hbR : (b : G) ∈ R₂ := hb
        have hmem : ⁅x, (b : G)⁆ ∈ Subgroup.centralizer (I : Set G) := by
          have h1 : ⁅x, (b : G)⁆ ∈ ⁅P, R₂⁆ := Subgroup.commutator_mem_commutator hxP hbR
          rw [Subgroup.commutator_comm] at h1
          exact Subgroup.centralizer_le (fun y hy => hIU hy) (hQU (hR₂P h1))
        have e : ((⁅(⟨x, hx⟩ : G₂), b⁆ : G₂) : G) = ⁅x, (b : G)⁆ := by
          simp [commutatorElement_def]
        have h2 : ρ ⁅(⟨x, hx⟩ : G₂), b⁆ = 1 := hρ1 _ (by rw [e]; exact hmem)
        rw [map_commutatorElement] at h2
        exact (commutatorElement_eq_one_iff_mul_comm).mp h2
      have hfix : ∀ y : I, (∀ b ∈ B, ρ b y = y) → ρ ⟨x, hx⟩ y = y := by
        intro y hy
        have hyC : (y : G) ∈ Subgroup.centralizer (R₂ : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro r hr
          have h1 := congrArg (fun z : I => (z : G)) (hy ⟨r, pCoreOf_le 2 G₂ hr⟩ hr)
          simp only [hρ] at h1
          calc r * y = r * y * r⁻¹ * r := by group
            _ = y * r := by rw [h1]
        have hyW : (y : G) ∈ W := ⟨y.2, hyC⟩
        have h1 : ⁅(y : G), x⁆ = 1 := by
          have := Subgroup.commutator_mem_commutator hyW hxP
          rwa [hbot, Subgroup.mem_bot] at this
        apply Subtype.ext
        rw [hρ]
        rw [commutatorElement_eq_one_iff_mul_comm] at h1
        show x * y * x⁻¹ = y
        rw [← h1, mul_inv_cancel_right]
      have hρx := thompson_AxB_element hI2 ρ hB2 ha hcomm hfix
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun z : I => (z : G)) (congrArg (fun φ : MulAut I => φ ⟨y, hy⟩) hρx)
      simp only [hρ, MulAut.one_apply] at h1
      calc y * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    have hPI : P ≤ Subgroup.centralizer (I : Set G) := by
      rw [hPdef, oTwoUpper, Subgroup.closure_le]
      exact fun x hx => hodd x hx.1 hx.2
    have hIP : ⁅I, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp hPI
    have hUP := D14.commutator_le_commutator_commutator hU2 hUG₂ hG₂U
    exact D15Proof.commutator_ne_bot h (le_bot_iff.mp (hIP ▸ hUP))
  have hIW : I ≤ W := D14.commutator_le_of_ne_bot hU2 hUG₂ hG₂U hchief hWU hG₂W hWP
  exact le_inf (hIU.trans hUR₂) (hIW.trans inf_le_right)

theorem twoResidual_eq_commutator_thompsonJ (h : D11Hyp G₁ G₂ T V M₂)
    (hmp : MinParabolic G₂ T M₂) (hJR₂ : ¬ thompsonJ (pCoreOf 2 G₁) ≤ pCoreOf 2 G₂) :
    twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ := by
  have hJT : thompsonJ (pCoreOf 2 G₁) ≤ T := (B6.thompsonJ_le _).trans h.pCoreOf_le_T
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 G₁) : Set G) :=
    h.sylow₁.1.trans ((le_normalizer_pCoreOf 2 G₁).trans (normalizer_le_normalizer_thompsonJ _))
  have hnlt := (hmp.commutator_lt_iff_le_pCoreOf hJT hTJ).not.mpr hJR₂
  have hle : ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ≤ twoResidual G₂ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hJT.trans h.sylow₂.1).trans (le_normalizer_twoResidual G₂))
  exact (eq_of_le_of_not_lt hle hnlt).symm

theorem exists_isFFInt (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    ∃ (I : Subgroup G) (hI : IsTwoReducedIn G₂ I),
      I ≤ conjClosure V G₂ ∧ IsFFInt G₂ I hI.2.2.1 := by
  have hC := D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  have hmp := minParabolic h hVR₂ hchief hdual
  have hZ := commutator_le_centerOf h hmp (not_pCoreOf_le_pCoreOf h hVR₂ hchief hdual) hVR₂
    hchief hdual
  have hPJ := twoResidual_eq_commutator_thompsonJ h hmp
    (not_thompsonJ_le_pCoreOf h hVR₂ hchief hdual)
  have hUE := isElemAbelian_conjClosure h hVR₂ hchief hdual
  have hVR := A4.le_pCoreOf_of_isTwoReducedIn h.reduced
  have hRG₂ : pCoreOf 2 G₁ ≤ G₂ := h.pCoreOf_le_T.trans h.sylow₂.1
  have hUQ : conjClosure V G₂ ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hC hg) v).mp ⟨hVR hv, hVR₂ hv⟩
  have hUR₂ : conjClosure V G₂ ≤ pCoreOf 2 G₂ := hUQ.trans inf_le_right
  have hUG₂ : conjClosure V G₂ ≤ G₂ := hUR₂.trans (pCoreOf_le 2 G₂)
  have hG₂U := le_normalizer_conjClosure V G₂
  have hU2 : IsPGroup 2 (conjClosure V G₂) := (pCoreOf_isPGroup 2 G₂).to_le hUR₂
  have hUP := D14.commutator_le_commutator_commutator hU2 hUG₂ hG₂U
  have hne := D15Proof.commutator_ne_bot h
  rw [← F6.twoResidual_eq_oTwoUpper G₂] at hUP hne
  set R := pCoreOf 2 G₁
  set R₂ := pCoreOf 2 G₂
  set U := conjClosure V G₂
  set P := twoResidual G₂
  have hPG₂ : P ≤ G₂ := twoResidual_le G₂
  set I := ⁅U, P⁆
  have hIU : I ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp (hPG₂.trans hG₂U)
  have hIG₂ : I ≤ G₂ := hIU.trans hUG₂
  have hG₂I : G₂ ≤ Subgroup.normalizer (I : Set G) :=
    D14.le_normalizer_commutator hG₂U (le_normalizer_twoResidual G₂)
  have hIE : IsElemAbelian 2 I := by
    rw [B6.isElemAbelian_iff] at hUE ⊢
    exact ⟨fun a ha b hb => hUE.1 a (hIU ha) b (hIU hb), fun a ha => hUE.2 a (hIU ha)⟩
  have hR₂I : R₂ ≤ Subgroup.centralizer (I : Set G) :=
    Subgroup.le_centralizer_iff.mp (hZ.trans inf_le_right)
  have hPI : ¬ P ≤ Subgroup.centralizer (I : Set G) := by
    intro hle
    have hIP : ⁅I, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp hle
    exact hne (le_bot_iff.mp (hIP ▸ hUP))
  set C := G₂ ⊓ Subgroup.centralizer (I : Set G)
  have hCn : G₂ ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hG₂I hg⟩
  have hPC : ¬ P ≤ C := fun hle => hPI (hle.trans inf_le_right)
  have hCM : C ≤ M₂ := (hmp.le_kerIn_of_not_twoResidual_le inf_le_left hCn hPC).trans kerIn_le
  have hred : IsTwoReducedIn G₂ I :=
    SimsD1.Twelve.isTwoReducedIn_of_minParabolic hmp hIG₂ hIE hG₂I hR₂I hCM
  refine ⟨I, hred, hIU, ?_⟩
  have hA : ∃ A : Subgroup G, IsMaxElemAbelian R A ∧ ¬ A ≤ Subgroup.centralizer (I : Set G) := by
    by_contra hno
    apply hPC
    have hJC : thompsonJ R ≤ C := le_inf ((B6.thompsonJ_le R).trans hRG₂)
      (iSup₂_le fun A hA => Classical.byContradiction fun hAI => hno ⟨A, hA, hAI⟩)
    calc P = ⁅P, thompsonJ R⁆ := hPJ
      _ ≤ ⁅P, C⁆ := Subgroup.commutator_mono le_rfl hJC
      _ ≤ C := Subgroup.le_normalizer_iff_commutator_le_right.mp (hPG₂.trans hCn)
  obtain ⟨A, hAR, hAI⟩ := hA
  exact isFFModule_autOn hred.2.2.1 (hIU.trans (hUQ.trans inf_le_left)) hG₂I
    (hAR.1.trans hRG₂) hAR hAI

theorem d14_finite (h : D11Hyp G₁ G₂ T V M₂) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1) :
    IsDualFFInt G₁ V h.reduced.2.2.1 ∨
    (((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      (¬ IsFFInt G₁ V h.reduced.2.2.1 → thompsonJ T = thompsonJ (pCoreOf 2 G₁)) ∧
      (∃ (I : Subgroup G) (hI : IsTwoReducedIn G₂ I),
        I ≤ conjClosure V G₂ ∧ IsFFInt G₂ I hI.2.2.1) ∧
      (Group.IsSolvable G₂ → CharTwo G₂ →
        IsSylowTwoOf (pCoreOf 2 G₁) (twoResidual G₂ ⊔ pCoreOf 2 G₁))) := by
  by_cases hdual : IsDualFFInt G₁ V h.reduced.2.2.1
  · exact Or.inl hdual
  have hmp := minParabolic h hVR₂ hchief hdual
  refine Or.inr ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer
      (inf_le_right.trans (pCoreOf_le 2 G₂))).mpr (D14.inf_pCoreOf_normal h hVR₂ hchief hdual),
    isElemAbelian_conjClosure h hVR₂ hchief hdual,
    commutator_le_centerOf h hmp (not_pCoreOf_le_pCoreOf h hVR₂ hchief hdual) hVR₂ hchief hdual,
    twoResidual_eq_commutator_thompsonJ h hmp (not_thompsonJ_le_pCoreOf h hVR₂ hchief hdual),
    h.thompsonJ_eq, exists_isFFInt h hVR₂ hchief hdual, fun hsolv hchar => ?_⟩
  rw [F6.twoResidual_eq_oTwoUpper G₂]
  exact EmptyFaithfulMultiple.inputD14Solvable_holds G G₁ G₂ T V M₂ h hVR₂ hchief hdual hsolv
    hchar

end CFSG.Quasithin.SimsD1.Four
