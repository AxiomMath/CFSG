module

public import CFSG.Quasithin.EmptyFaithful.S1565A
public import CFSG.Quasithin.EmptyFaithful.SBc32Five
public import CFSG.Quasithin.EmptyFaithful.SBd2NoA5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement

@[expose] def SylowFixedOrder32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15332 T Mc M V₁ V₂ Yp I L t → Clause32One T I L →
      Nat.card ↥(UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G)) ≤ 2

namespace SBd2

section Model

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_ZS_basis (h : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ a₁ a₂ : G, a₁ ∈ V₁ ∧ a₂ ∈ V₂ ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      (∀ v : G, v ∈ ZS153 T M V₁ ↔ v = 1 ∨ v = a₁ ∨ v = a₂ ∨ v = a₁ * a₂) ∧
      (∀ v ∈ quasithinOmegaOneCenter T, v = 1 ∨ v = a₁ * a₂) := by
  obtain ⟨hV, L₁, L₂, tb, hS, rfl, rfl, -, -⟩ := D.model
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := hS.exists_sylowFacts h.isSylowTwoOf_autI
  have hTM : T ≤ M := h.T_le
  have hMN : M ≤ Subgroup.normalizer (VZ T M : Set G) := h.le_normalizer
  have hSN : Sgp153 T ((commV L₁).map (inclMod hV)) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans (hTM.trans hMN)
  have hTN : T ≤ Subgroup.normalizer (VZ T M : Set G) := hTM.trans hMN
  have hSbar : autI hV (Sgp153 T ((commV L₁).map (inclMod hV))) = autI hV T ⊓ (L₁ ⊔ L₂) :=
    autI_nS hV hS hTM
  refine ⟨a₁.val, a₂.val, (mem_map_inclMod_iff hV).2 ⟨a₁, hF.sylow.a₁_mem, rfl⟩,
    (mem_map_inclMod_iff hV).2 ⟨a₂, hF.sylow.a₂_mem, rfl⟩,
    fun h1 => hF.sylow.a₁_ne (IntMod.val_injective (h1.trans IntMod.val_one.symm)),
    fun h1 => hF.sylow.a₂_ne (IntMod.val_injective (h1.trans IntMod.val_one.symm)), ?_, ?_⟩
  · intro v
    constructor
    · rintro ⟨hvV, hvC⟩
      let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨v, hvV⟩
      have hw : w ∈ fixV (autI hV T ⊓ (L₁ ⊔ L₂)) := by
        rw [← hSbar]
        exact (mem_fixV_autI hV hSN w).2 hvC
      rcases (hF.sylow.fixS w).mp hw with h1 | h1 | h1 | h1
      · left
        exact congrArg IntMod.val h1
      · right; left
        exact congrArg IntMod.val h1
      · right; right; left
        exact congrArg IntMod.val h1
      · right; right; right
        exact (congrArg IntMod.val h1).trans (IntMod.val_mul a₁ a₂)
    · intro hv
      have key : ∀ w : IntMod (VZ T M) hV, w ∈ fixV (autI hV T ⊓ (L₁ ⊔ L₂)) →
          w.val ∈ ZS153 T M ((commV L₁).map (inclMod hV)) := by
        intro w hw
        rw [← hSbar] at hw
        exact ⟨w.val_mem, (mem_fixV_autI hV hSN w).1 hw⟩
      rcases hv with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact key a₁ ((hF.sylow.fixS a₁).2 (Or.inr (Or.inl rfl)))
      · exact key a₂ ((hF.sylow.fixS a₂).2 (Or.inr (Or.inr (Or.inl rfl))))
      · have := key (a₁ * a₂) ((hF.sylow.fixS (a₁ * a₂)).2 (Or.inr (Or.inr (Or.inr rfl))))
        rwa [IntMod.val_mul a₁ a₂] at this
  · intro v hv
    have hZ := h.lemma_15_3_2_two.1
    rw [hZ] at hv
    obtain ⟨hvV, hvC⟩ := hv
    let w : IntMod (VZ T M) hV := IntMod.mk hV ⟨v, hvV⟩
    have hw : w ∈ fixV (autI hV T) := (mem_fixV_autI hV hTN w).2 hvC
    rcases hF.fix w hw with h1 | h1
    · left
      exact congrArg IntMod.val h1
    · right
      exact (congrArg IntMod.val h1).trans (IntMod.val_mul a₁ a₂)

end Model

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem input32Two_of_sylow_fixed (h113 : StageLemma14113) (hres : SylowFixedOrder32) :
    Input32Two := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c h1
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t :=
    c.toCtx15331.toCtx15330.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hh : Hyp153 G T Mc M := hyp.hyp
  have Dc : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hF : Facts153 T M V₁ Yp I := c25.facts.toFacts153
  have hYp : Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) :=
    c25.facts.case_two.2
  have hcardUL := hres G T Mc M V₁ V₂ Yp I L t c h1
  obtain ⟨a₁, a₂, ha₁V, ha₂V, ha₁1, ha₂1, hZS, hZ⟩ := exists_ZS_basis hh Dc
  have hLI : L ≤ I := S153H.L_le_I c
  have hSI : Sgp153 T V₁ ≤ I := S153H.Sgp153_le_I c
  have hIL : I ≤ Subgroup.normalizer (L : Set G) := c.c27.normal
  have hYL : Yp ≤ L := c.c27.Yp_le
  have hYC : Yp ≤ Subgroup.centralizer (V₁ : Set G) := c.c29.cent
  have hV₂UL : V₂ ≤ UL153 T I L := SBc.V₂_le_UL h113 c
  have hUI : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLI.trans hUI
  have hULU : UL153 T I L ≤ UI153 T I := Subgroup.le_normalizer_iff_commutator_le_left.mp hLU
  have hsyl : IsSylowTwoOf (Sgp153 T V₁) I := hF.sylow
  have hZ' : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (Sgp153 T V₁) := by
    unfold quasithinOmegaOneCenter
    refine Subgroup.closure_mono fun z hz => ?_
    have hzV : z ∈ VZ T M := le_conjClosure _ _ (Subgroup.subset_closure hz)
    exact ⟨⟨S153D.VZ_le_Sgp153 hyp hzV, Subgroup.centralizer_le (fun x hx => hx.1) hz.1.2⟩, hz.2⟩
  obtain ⟨-, hU, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl c25.ctx.charTwo hZ'
  have ha₁S : a₁ ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) :=
    ((hZS a₁).2 (Or.inr (Or.inl rfl))).2
  have ha₂S : a₂ ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) :=
    ((hZS a₂).2 (Or.inr (Or.inr (Or.inl rfl)))).2
  have ha₁U : a₁ ∈ UI153 T I := by
    obtain ⟨z, hz, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : quasithinOmegaOneCenter T = ⊥ :=
        eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hno x hx)
      have h2 := hh.lemma_15_3_2_two.2
      rw [hbot, Subgroup.card_bot] at h2
      omega
    have hzeq : z = a₁ * a₂ := (hZ z hz).resolve_left hz1
    have hzU : z ∈ UI153 T I := le_conjClosure (quasithinOmegaOneCenter T) I hz
    have h2U : a₂ ∈ UI153 T I := hULU (hV₂UL ha₂V)
    have : a₁ = z * a₂⁻¹ := by rw [hzeq]; group
    rw [this]
    exact (UI153 T I).mul_mem hzU ((UI153 T I).inv_mem h2U)
  let φ : ↥I →* MulAut (IntMod (UI153 T I) hU) := convHom hU I hUI
  have hφ : ∀ (x : ↥I) (w : IntMod (UI153 T I) hU), (φ x w).val = (x : G) * w.val * (x : G)⁻¹ :=
    fun x w => convI_apply_val hU ⟨x, hUI x.2⟩ w
  have hodd : Odd ((Sgp153 T V₁).subgroupOf I).index := by
    have := hsyl.2.2
    exact Nat.odd_iff.mpr (by omega)
  let w₀ : IntMod (UI153 T I) hU := IntMod.mk hU ⟨a₁, ha₁U⟩
  have hA : S1565.InvSub φ (⊥ : Subgroup (IntMod (UI153 T I) hU)) := fun x a ha => by
    rw [Subgroup.mem_bot.mp ha, map_one]
    exact Subgroup.one_mem _
  have hw'' : S1565.FixMod φ ⊤ ((UL153 T I L).comap (inclMod hU)) w₀ := by
    intro s _
    show (φ s w₀ * w₀⁻¹).val ∈ UL153 T I L
    have hs : (s : G) ∈ L ⊔ Sgp153 T V₁ := c.I_eq ▸ s.2
    obtain ⟨l, hl, s', hs', hs'e⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (hSI.trans hIL)).1 hs
    have h1 := Subgroup.mem_centralizer_iff.mp ha₁S s' hs'
    have e : (φ s w₀ * w₀⁻¹).val = ⁅l, a₁⁆ := by
      show (φ s w₀).val * (w₀.val)⁻¹ = _
      rw [hφ, hs'e]
      show l * s' * a₁ * (l * s')⁻¹ * a₁⁻¹ = l * a₁ * l⁻¹ * a₁⁻¹
      have e2 : l * s' * a₁ * (l * s')⁻¹ = l * (s' * a₁ * s'⁻¹) * l⁻¹ := by group
      rw [e2, show s' * a₁ * s'⁻¹ = a₁ by rw [h1]; group]
    rw [e]
    have := Subgroup.commutator_mem_commutator hl ha₁U
    rwa [Subgroup.commutator_comm] at this
  have hwB : S1565.FixMod φ ((Sgp153 T V₁).subgroupOf I) ⊥ w₀ := by
    intro s hs
    have hsS : (s : G) ∈ Sgp153 T V₁ := Subgroup.mem_subgroupOf.mp hs
    have h1 := Subgroup.mem_centralizer_iff.mp ha₁S s hsS
    rw [Subgroup.mem_bot, mul_inv_eq_one]
    refine IntMod.val_injective ?_
    rw [hφ]
    show (s : G) * a₁ * (s : G)⁻¹ = a₁
    rw [h1]
    group
  obtain ⟨u, hu, hfix, -⟩ := S1565.norm_step φ (fun w => IntMod.sq_eq_one w)
    ((Sgp153 T V₁).subgroupOf I) hodd (A := ⊥) (A'' := (UL153 T I L).comap (inclMod hU)) hA hw'' hwB
  have huUL : u.val ∈ UL153 T I L := hu
  have hf : ∀ x ∈ I, x * (a₁ * u.val) * x⁻¹ = a₁ * u.val := by
    intro x hx
    have h1 := Subgroup.mem_bot.mp (hfix ⟨x, hx⟩ (Subgroup.mem_top _))
    rw [mul_inv_eq_one] at h1
    have h2 := congrArg IntMod.val h1
    rw [hφ, IntMod.val_mul] at h2
    exact h2
  have huS : u.val ∈ Subgroup.centralizer (Sgp153 T V₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := hf s (hSI hs)
    have h2 := Subgroup.mem_centralizer_iff.mp ha₁S s hs
    have : s * u.val * s⁻¹ = u.val := by
      have e : s * (a₁ * u.val) * s⁻¹ = (s * a₁ * s⁻¹) * (s * u.val * s⁻¹) := by group
      rw [e, show s * a₁ * s⁻¹ = a₁ by rw [h2]; group] at h1
      exact mul_left_cancel h1
    exact mul_inv_eq_iff_eq_mul.mp this
  have huY : ∀ y ∈ Yp, y * u.val * y⁻¹ = u.val := by
    intro y hy
    have h1 := hf y (hLI (hYL hy))
    have h2 := Subgroup.mem_centralizer_iff.mp (hYC hy) a₁ ha₁V
    have : y * u.val * y⁻¹ = u.val := by
      have e : y * (a₁ * u.val) * y⁻¹ = (y * a₁ * y⁻¹) * (y * u.val * y⁻¹) := by group
      rw [e, show y * a₁ * y⁻¹ = a₁ by rw [← h2]; group] at h1
      exact mul_left_cancel h1
    exact this
  have hnoC : ∀ v ∈ V₂, v ≠ 1 → ∃ y ∈ Yp, y * v * y⁻¹ ≠ v := fun v hv hv1 => by
    obtain ⟨y, hy, hne⟩ := exists_not_commute_V₂ h113 hh Dc v hv hv1
    exact ⟨y, hYp ▸ hy, hne⟩
  have hu1 : u.val = 1 := by
    by_contra hne
    have ha₂H : a₂ ∈ UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) :=
      ⟨hV₂UL ha₂V, ha₂S⟩
    have huH : u.val ∈ UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) := ⟨huUL, huS⟩
    have hua₂ : u.val = a₂ := by
      by_contra hne2
      have hsub : ({1, a₂, u.val} : Set G) ⊆
          ((UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) : Set G) := by
        intro g hg
        rcases hg with rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact ha₂H
        · exact huH
      have hc3 : ({1, a₂, u.val} : Set G).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem, Set.ncard_pair (Ne.symm hne2)]
        simp [ha₂1.symm, Ne.symm hne]
      have hH : ((UL153 T I L ⊓ Subgroup.centralizer (Sgp153 T V₁ : Set G) : Subgroup G) :
          Set G).ncard ≤ 2 := by
        rw [← Nat.card_coe_set_eq]
        exact hcardUL
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    obtain ⟨y, hy, hne3⟩ := hnoC a₂ ha₂V ha₂1
    exact hne3 (by rw [← hua₂]; exact huY y hy)
  have ha₁L : a₁ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := hf l (hLI hl)
    rw [hu1, mul_one] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have ha₂L : a₂ ∉ Subgroup.centralizer (L : Set G) := fun h => by
    obtain ⟨y, hy, hne⟩ := hnoC a₂ ha₂V ha₂1
    apply hne
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.mp h y (hYL hy)
  have ha₂V₁ : a₂ ∉ V₁ := fun h => by
    have : a₂ ∈ V₁ ⊓ V₂ := ⟨h, ha₂V⟩
    rw [Dc.inf, Subgroup.mem_bot] at this
    exact ha₂1 this
  have ha₁ZS : a₁ ∈ ZS153 T M V₁ := (hZS a₁).2 (Or.inr (Or.inl rfl))
  have hmem : ∀ v : G, v ∈ ZS153 T M V₁ ⊓ V₁ ↔ v = 1 ∨ v = a₁ := by
    intro v
    constructor
    · rintro ⟨hvZ, hvV⟩
      rcases (hZS v).mp hvZ with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hvV ha₂V₁
      · exfalso
        apply ha₂V₁
        have : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
        rw [this]
        exact V₁.mul_mem (V₁.inv_mem ha₁V) hvV
    · rintro (rfl | rfl)
      · exact ⟨one_mem _, V₁.one_mem⟩
      · exact ⟨ha₁ZS, ha₁V⟩
  refine ⟨?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨hvZ, hvL⟩
      rcases (hZS v).mp hvZ with rfl | rfl | rfl | rfl
      · exact ⟨hvZ, V₁.one_mem⟩
      · exact ⟨hvZ, ha₁V⟩
      · exact absurd hvL ha₂L
      · exfalso
        apply ha₂L
        have : a₂ = a₁⁻¹ * (a₁ * a₂) := by group
        rw [this]
        exact (Subgroup.centralizer (L : Set G)).mul_mem
          ((Subgroup.centralizer (L : Set G)).inv_mem ha₁L) hvL
    · rintro ⟨hvZ, hvV⟩
      rcases (hmem v).mp ⟨hvZ, hvV⟩ with rfl | rfl
      · exact ⟨hvZ, Subgroup.one_mem _⟩
      · exact ⟨hvZ, ha₁L⟩
  · have hpow : a₁ ^ 2 = 1 := hh.elemAbelian.2 a₁ (Dc.le₁ ha₁V)
    have hzp : ZS153 T M V₁ ⊓ V₁ = Subgroup.zpowers a₁ := by
      ext v
      rw [hmem v]
      constructor
      · rintro (h | h)
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers a₁
      · intro hv
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
        have : a₁ ^ k = a₁ ^ (k % 2) := by
          conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
          rw [zpow_add, zpow_mul]
          simp [hpow]
        rw [this]
        have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
        rcases hk with h | h <;> simp [h]
    rw [hzp, Nat.card_zpowers]
    exact orderOf_eq_prime hpow ha₁1

end Context

end SBd2

end CFSG.Quasithin
