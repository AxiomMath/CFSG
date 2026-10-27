module

public import CFSG.Quasithin.Background.D15Twelve
public import CFSG.Quasithin.Background.D14Normal
public import CFSG.Quasithin.Vol2.Ch3Sec1D12

public section

namespace CFSG.Quasithin.D15Proof

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {G₁ G₂ T V M₂ : Subgroup G}

theorem commutator_pCoreOf_le (h : D11Hyp G₁ G₂ T V M₂) (hmp : MinParabolic G₂ T M₂)
    (hRR₂ : ¬ pCoreOf 2 G₁ ≤ pCoreOf 2 G₂)
    (hC : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) :
    ⁅pCoreOf 2 G₂, oTwoUpper G₂⁆ ≤ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 G₁ with hRdef
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set P := oTwoUpper G₂ with hPdef
  have hRT : R ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₁
  have hRG₂ : R ≤ G₂ := hRT.trans h.sylow₂.1
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 G₁
  have hPres : P = twoResidual G₂ := (F6.twoResidual_eq_oTwoUpper G₂).symm
  have hYG₂ : conjClosure R G₂ ≤ G₂ := conjClosure_le fun g hg r hr =>
    G₂.mul_mem (G₂.mul_mem hg (hRG₂ hr)) (G₂.inv_mem hg)
  rcases hmp.le_kerIn_or_twoResidual_le hYG₂ (le_normalizer_conjClosure R G₂) with hker | hres
  · exact absurd (hmp.le_pCoreOf_of_isPGroup_of_le_kerIn hR2
      ((le_conjClosure R G₂).trans hker)) hRR₂
  rw [← hPres] at hres
  refine (Subgroup.commutator_mono le_rfl hres).trans ?_
  refine D14.commutator_le_closure (S := {x | ∃ g ∈ G₂, ∃ r ∈ R, g * r * g⁻¹ = x})
    (hYG₂.trans hC) ?_
  rintro x hx _ ⟨g, hg, r, hr, rfl⟩
  have hx' : g⁻¹ * x * g ∈ R₂ :=
    (Subgroup.mem_normalizer_iff''.mp (le_normalizer_pCoreOf 2 G₂ hg) x).mp hx
  have hxG₁ : g⁻¹ * x * g ∈ G₁ :=
    ((B6.pCoreOf_two_le_of_isSylowTwoOf h.sylow₂).trans h.sylow₁.1) hx'
  have hc : ⁅g⁻¹ * x * g, r⁆ ∈ R ⊓ R₂ := by
    refine ⟨?_, ?_⟩
    · have h1 : (g⁻¹ * x * g) * r * (g⁻¹ * x * g)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₁ hxG₁) r).mp hr
      rw [commutatorElement_def]
      exact R.mul_mem h1 (R.inv_mem hr)
    · have h1 : r * (g⁻¹ * x * g)⁻¹ * r⁻¹ ∈ R₂ :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G₂ (hRG₂ hr)) _).mp
          (R₂.inv_mem hx')
      have e : ⁅g⁻¹ * x * g, r⁆ = (g⁻¹ * x * g) * (r * (g⁻¹ * x * g)⁻¹ * r⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact R₂.mul_mem hx' h1
  have e : ⁅x, g * r * g⁻¹⁆ = g * ⁅g⁻¹ * x * g, r⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hC hg) _).mp hc

omit [Finite G] in
theorem le_centralizer_conjClosure (h : D11Hyp G₁ G₂ T V M₂)
    (hC : G₂ ≤ Subgroup.normalizer ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ : Subgroup G) : Set G)) :
    pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ ≤ Subgroup.centralizer (conjClosure V G₂ : Set G) := by
  have hRC : pCoreOf 2 G₁ ≤ Subgroup.centralizer (V : Set G) := by
    rw [h.centralizer]
    exact inf_le_right
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun g hg v hv => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : g⁻¹ * q * g ∈ pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂ :=
    (Subgroup.mem_normalizer_iff''.mp (hC hg) q).mp hq
  have hc : g⁻¹ * q * g * v = v * (g⁻¹ * q * g) :=
    (Subgroup.mem_centralizer_iff.mp (hRC hq'.1) v hv).symm
  calc q * (g * v * g⁻¹) = g * ((g⁻¹ * q * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
    _ = g * v * g⁻¹ * q := by group

theorem commutator_le_centerOf (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := D14.inf_pCoreOf_normal h hVR₂ hchief hdual
  have hmp := h.minParabolic hnff
  set R := pCoreOf 2 G₁ with hRdef
  set R₂ := pCoreOf 2 G₂ with hR₂def
  set U := conjClosure V G₂ with hUdef
  set P := oTwoUpper G₂ with hPdef
  rw [F6.twoResidual_eq_oTwoUpper G₂]
  have hRR₂ : ¬ R ≤ R₂ := fun hle =>
    h.not_thompsonJ_le_pCoreOf hnff ((B6.thompsonJ_le _).trans hle)
  have hR₂P : ⁅R₂, P⁆ ≤ R ⊓ R₂ := commutator_pCoreOf_le h hmp hRR₂ hC
  have hQU : R ⊓ R₂ ≤ Subgroup.centralizer (U : Set G) := le_centralizer_conjClosure h hC
  have hG₂R₂ : G₂ ≤ Subgroup.normalizer (R₂ : Set G) := le_normalizer_pCoreOf 2 G₂
  have hUR₂ : U ≤ R₂ := conjClosure_le fun g hg v hv =>
    (Subgroup.mem_normalizer_iff.mp (hG₂R₂ hg) v).mp (hVR₂ hv)
  have hUG₂ : U ≤ G₂ := hUR₂.trans (pCoreOf_le 2 G₂)
  have hG₂U : G₂ ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure V G₂
  have hU2 : IsPGroup 2 U := (pCoreOf_isPGroup 2 G₂).to_le hUR₂
  have hPG₂ : P ≤ G₂ := oTwoUpper_le G₂
  set I := ⁅U, P⁆ with hIdef
  have hIU : I ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp (hPG₂.trans hG₂U)
  have hG₂I : G₂ ≤ Subgroup.normalizer (I : Set G) :=
    D14.le_normalizer_commutator hG₂U (le_normalizer_oTwoUpper G₂)
  set W := I ⊓ Subgroup.centralizer (R₂ : Set G) with hWdef
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
    set B : Subgroup G₂ := R₂.subgroupOf G₂ with hBdef
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
    exact commutator_ne_bot h (le_bot_iff.mp (hIP ▸ hUP))
  have hIW : I ≤ W := D14.commutator_le_of_ne_bot hU2 hUG₂ hG₂U hchief hWU hG₂W hWP
  exact le_inf (hIU.trans hUR₂) (hIW.trans inf_le_right)

theorem twoResidual_eq_commutator_thompsonJ (h : D11Hyp G₁ G₂ T V M₂)
    (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1) :
    twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ := by
  have hmp := h.minParabolic hnff
  have hJT : thompsonJ (pCoreOf 2 G₁) ≤ T := (B6.thompsonJ_le _).trans h.pCoreOf_le_T
  have hTJ : T ≤ Subgroup.normalizer (thompsonJ (pCoreOf 2 G₁) : Set G) :=
    h.sylow₁.1.trans ((le_normalizer_pCoreOf 2 G₁).trans (normalizer_le_normalizer_thompsonJ _))
  have hnlt := (hmp.commutator_lt_iff_le_pCoreOf hJT hTJ).not.mpr
    (h.not_thompsonJ_le_pCoreOf hnff)
  have hle : ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ≤ twoResidual G₂ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hJT.trans h.sylow₂.1).trans (le_normalizer_twoResidual G₂))
  exact (eq_of_le_of_not_lt hle hnlt).symm

theorem d15Concl5 (h : D11Hyp G₁ G₂ T V M₂) (hnff : ¬ IsFFInt G₁ V h.reduced.2.2.1)
    (hVR₂ : V ≤ pCoreOf 2 G₂)
    (hchief : IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1)
    (hdual : ¬ IsDualFFInt G₁ V h.reduced.2.2.1) :
    ((pCoreOf 2 G₁ ⊓ pCoreOf 2 G₂).subgroupOf G₂).Normal ∧
      IsElemAbelian 2 (conjClosure V G₂) ∧
      IsChiefSeriesFrom G₂ (conjClosure V G₂) (conjClosure V G₂) 1 ∧
      ⁅conjClosure V G₂, twoResidual G₂⁆ ≤ centerOf (pCoreOf 2 G₂) ∧
      twoResidual G₂ = ⁅twoResidual G₂, thompsonJ (pCoreOf 2 G₁)⁆ ∧
      thompsonJ (pCoreOf 2 G₁) = thompsonJ T :=
  ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_right.trans (pCoreOf_le 2 G₂))).mpr
      (D14.inf_pCoreOf_normal h hVR₂ hchief hdual),
    isElemAbelian_conjClosure h hnff hVR₂, hchief,
    commutator_le_centerOf h hnff hVR₂ hchief hdual,
    twoResidual_eq_commutator_thompsonJ h hnff, (h.thompsonJ_eq hnff).symm⟩

end CFSG.Quasithin.D15Proof
