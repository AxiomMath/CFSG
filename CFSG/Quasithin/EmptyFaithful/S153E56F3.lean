module

public import CFSG.Quasithin.EmptyFaithful.S153E56F1
public import CFSG.Quasithin.EmptyFaithful.S153E56F2

public section

namespace CFSG.Quasithin

namespace S153E56f

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise

section Basic

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

abbrev Wd (cx : Ctx15350 T Mc M V₁ V₂ t) : Type := IntMod (VZ T M) cx.c.hyp.elemAbelian

noncomputable abbrev cb (cx : Ctx15350 T Mc M V₁ V₂ t) (g : G)
    (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) : MulAut (Wd cx) :=
  convI cx.c.hyp.elemAbelian ⟨g, hg⟩

theorem cb_val (cx : Ctx15350 T Mc M V₁ V₂ t) (g : G) (hg : g ∈ Subgroup.normalizer (VZ T M : Set G))
    (w : Wd cx) : (cb cx g hg w).val = g * w.val * g⁻¹ :=
  convI_apply_val _ _ _

theorem cb_mul (cx : Ctx15350 T Mc M V₁ V₂ t) (g h : G)
    (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) (hh : h ∈ Subgroup.normalizer (VZ T M : Set G)) :
    cb cx (g * h) (Subgroup.mul_mem _ hg hh) = cb cx g hg * cb cx h hh := by
  show convI _ ⟨g * h, _⟩ = convI _ ⟨g, hg⟩ * convI _ ⟨h, hh⟩
  rw [← map_mul]
  rfl

theorem cb_inv (cx : Ctx15350 T Mc M V₁ V₂ t) (g : G) (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) :
    cb cx g⁻¹ (Subgroup.inv_mem _ hg) = (cb cx g hg)⁻¹ := by
  show convI _ ⟨g⁻¹, _⟩ = (convI _ ⟨g, hg⟩)⁻¹
  rw [← map_inv]
  rfl

theorem cb_eq_one_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (g : G)
    (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) :
    cb cx g hg = 1 ↔ g ∈ Subgroup.centralizer (VZ T M : Set G) :=
  convI_eq_one_iff _ _

theorem cb_conj (cx : Ctx15350 T Mc M V₁ V₂ t) (g u : G)
    (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) (hu : u ∈ Subgroup.normalizer (VZ T M : Set G))
    (h : g⁻¹ * u * g ∈ Subgroup.normalizer (VZ T M : Set G)) :
    cb cx (g⁻¹ * u * g) h = (cb cx g hg)⁻¹ * cb cx u hu * cb cx g hg := by
  have e1 : cb cx (g⁻¹ * u * g) h = cb cx (g⁻¹ * u) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hu) *
      cb cx g hg := cb_mul cx _ _ _ hg
  have e2 : cb cx (g⁻¹ * u) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hu) =
      cb cx g⁻¹ (Subgroup.inv_mem _ hg) * cb cx u hu := cb_mul cx _ _ _ hu
  rw [e1, e2, cb_inv cx g hg]

theorem cb_mem_O (cx : Ctx15350 T Mc M V₁ V₂ t) {g : G} (hgM : g ∈ M)
    (hg : g ∈ Subgroup.normalizer (VZ T M : Set G)) :
    cb cx g hg ∈ orthogonalGroupOf (qW cx) := by
  rw [← (qW_spec cx).2.2.2]
  exact convI_mem_autI cx.c.hyp.elemAbelian hgM hg

theorem cb_inv_val (cx : Ctx15350 T Mc M V₁ V₂ t) (g : G) (hg : g ∈ Subgroup.normalizer (VZ T M : Set G))
    (w : Wd cx) : ((cb cx g hg)⁻¹ w).val = g⁻¹ * w.val * g := by
  rw [← cb_inv cx g hg, cb_val]
  simp

theorem exists_z (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ ∀ x ∈ quasithinOmegaOneCenter T, x = 1 ∨ x = z :=
  S1417.exists_eq_of_card_eq_two cx.c.hyp.lemma_15_3_2_two.2

theorem qW_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {z : G} (hz : z ∈ quasithinOmegaOneCenter T) :
    qW cx (IntMod.mk cx.c.hyp.elemAbelian ⟨z, cx.c.hyp.Z_le_VZ hz⟩) = 0 := by
  have hV := cx.c.hyp.elemAbelian
  have hzV : z ∈ VZ T M := cx.c.hyp.Z_le_VZ hz
  by_cases hz1 : z = 1
  · subst hz1
    exact (qW_spec cx).1.1
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, hV₂⟩ := exists_bar_model cx
  have hzfix : IntMod.mk hV ⟨z, hzV⟩ ∈ fixV (autI hV T) := (mem_fixV_autI_T_iff cx _).2 hz
  have hzeq : IntMod.mk hV ⟨z, hzV⟩ = a₁ * a₂ := by
    rcases hF.fix _ (fun x hx => hzfix x hx) with h | h
    · exfalso
      apply hz1
      have := congrArg IntMod.val h
      exact this
    · exact h
  have hq := (qV153_spec cx.c).2.2.2.2 z hzV
  rcases zmod2_cases (qV153 cx.c ⟨z, hzV⟩) with h | h
  · exact h
  · exfalso
    obtain ⟨hz12, -⟩ := hq.1 h
    have ha₁ : a₁ ∈ commV L₁ := hF.sylow.a₁_mem
    have ha₂ : a₂ ∈ commV L₂ := hF.sylow.a₂_mem
    rcases hz12 with h1 | h1
    · rw [← hV₁] at h1
      obtain ⟨w, hw, hwz⟩ := (mem_map_inclMod_iff hV).1 h1
      have hwz' : w = a₁ * a₂ := by
        rw [← hzeq]
        exact IntMod.val_injective hwz
      rw [hwz'] at hw
      have : a₂ ∈ commV L₁ := by
        have := (commV L₁).mul_mem ((commV L₁).inv_mem ha₁) hw
        simpa using this
      have h0 : a₂ ∈ commV L₁ ⊓ commV L₂ := ⟨this, ha₂⟩
      rw [hS.inf, Subgroup.mem_bot] at h0
      exact hF.sylow.a₂_ne h0
    · rw [← hV₂] at h1
      obtain ⟨w, hw, hwz⟩ := (mem_map_inclMod_iff hV).1 h1
      have hwz' : w = a₁ * a₂ := by
        rw [← hzeq]
        exact IntMod.val_injective hwz
      rw [hwz'] at hw
      have : a₁ ∈ commV L₂ := by
        have := (commV L₂).mul_mem hw ((commV L₂).inv_mem ha₂)
        simpa using this
      have h0 : a₁ ∈ commV L₁ ⊓ commV L₂ := ⟨ha₁, this⟩
      rw [hS.inf, Subgroup.mem_bot] at h0
      exact hF.sylow.a₁_ne h0

theorem Yi_inf_pCore_le (N₁ : Subgroup (MulAut ↥(VZ T M))) :
    Yi153 T Mc M V₁ N₁ ⊓ pCoreOf 2 (Y153 Mc M) ≤ pCoreOf 2 (Yi153 T Mc M V₁ N₁) := by
  have hAle : Yi153 T Mc M V₁ N₁ ⊓ pCoreOf 2 (Y153 Mc M) ≤ Yi153 T Mc M V₁ N₁ := inf_le_left
  have hYY : Yi153 T Mc M V₁ N₁ ≤ Y153 Mc M := (oTwoUpper_le _).trans inf_le_left
  have hn1 : Yi153 T Mc M V₁ N₁ ≤ Subgroup.normalizer (Yi153 T Mc M V₁ N₁ : Set G) :=
    Subgroup.le_normalizer
  have hn2 : Yi153 T Mc M V₁ N₁ ≤ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M) : Set G) :=
    hYY.trans (le_normalizer_pCoreOf 2 (Y153 Mc M))
  have hAn : Yi153 T Mc M V₁ N₁ ≤ Subgroup.normalizer
      ((Yi153 T Mc M V₁ N₁ ⊓ pCoreOf 2 (Y153 Mc M) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf hn1 hn2
  have hAp : IsPGroup 2 ↥(Yi153 T Mc M V₁ N₁ ⊓ pCoreOf 2 (Y153 Mc M)) :=
    (pCoreOf_isPGroup 2 (Y153 Mc M)).to_inf_right
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAle hAn hAp

theorem yb_facts (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15355 cx N₁ N₂ g s) {y : G}
    (hy : y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁)) :
    ∃ hyN : y ∈ Subgroup.normalizer (VZ T M : Set G),
      cb cx y hyN ∈ N₁ ∧ cb cx y hyN ≠ 1 ∧ cb cx y hyN ^ 3 = 1 ∧
        fixV (Subgroup.zpowers (cb cx y hyN)) = ⊥ := by
  have hV := cx.c.hyp.elemAbelian
  have hyY' : y ∈ Y153 Mc M ⊓ Ni153 T Mc M V₁ N₁ := oTwoUpper_le _ hy.1
  have hyY : y ∈ Y153 Mc M := hyY'.1
  have hyYU : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := S153E55.Y_le_YU hyY
  have hyN : y ∈ Subgroup.normalizer (VZ T M : Set G) := S153E55.YU_le_normalizer_V cx hyYU
  have hb₁ : cb cx y hyN ∈ N₁ := S153E55.bar_mem_of_mem_Ni cx hyY'.2 hyYU
  have h1 : cb cx y hyN ≠ 1 := by
    intro h
    have hyC : y ∈ Subgroup.centralizer (VZ T M : Set G) := (cb_eq_one_iff cx y hyN).1 h
    have hyP : y ∈ pCoreOf 2 (Y153 Mc M) := by
      rw [cx.r49.case_one.1]
      exact ⟨hyY, hyC⟩
    apply hy.2
    exact Yi_inf_pCore_le (T := T) (Mc := Mc) (M := M) (V₁ := V₁) N₁ ⟨hy.1, hyP⟩
  obtain ⟨e₁⟩ := c.h53one.iso₁
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hY9 : Nat.card ↥(autI hV (Y153 Mc M)) = 9 := by
    rw [hYbar]
    exact hS.card_oTwoUpper cx.c.hyp.isSylowTwoOf_autI
  have hybY : cb cx y hyN ∈ autI hV (Y153 Mc M) := convI_mem_autI hV hyY hyN
  have h9 : cb cx y hyN ^ 9 = 1 := by
    have := pow_card_eq_one' (G := ↥(autI hV (Y153 Mc M))) (x := ⟨cb cx y hyN, hybY⟩)
    rw [hY9] at this
    exact congrArg Subtype.val this
  have h3 : cb cx y hyN ^ 3 = 1 := pow_three_of_pow_nine (W := Wd cx) e₁ hb₁ h9
  have hN₁Y : N₁ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := by
    rw [S153E55.autI_YU_eq cx c.h53one]
    exact le_sup_left
  exact ⟨hyN, hb₁, h1, h3, S153E55.fixV_eq_bot_of_perm (W := Wd cx) IntMod.sq_eq_one e₁
    (S153E55.commV_eq_top cx hN₁Y c.h53one.comm₁) hb₁ h3 h1⟩

theorem ubdata (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))}
    (c : Chain15353 cx N₁ N₂) :
    ∃ a b : MulAut (Wd cx), a ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) ∧
      b ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) ∧ a ∈ N₁ ∧ b ∈ N₂ ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a * a = 1 ∧ b * b = 1 ∧
      (∀ x ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc), x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧
      (∀ τ ∈ autI cx.c.hyp.elemAbelian T, τ ∉ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) →
        τ * a * τ⁻¹ = b ∧ τ * b * τ⁻¹ = a) := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have h1 := c.h51.one
  obtain ⟨hK4, Ω₀, hΩ₀, hsyl⟩ : IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
      ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M hV Ω ∧
        IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω := by
    rcases c.h51.two with h | ⟨hab, -, -, -⟩
    · exact ⟨h.2.1, h.2.2.2.2⟩
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := c.h52
      exact hne (B2F.isElemAbelian_comm hab ha hb)
  obtain ⟨Ω, hΩ, -, hΩeq⟩ := c.h53one.omega
  have hΩΩ₀ : Ω₀ = Ω := by
    ext g
    exact (hΩ₀ g).trans (hΩ g).symm
  have hsyl' : IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) (N₁ ⊔ N₂) := by
    rw [hΩeq, ← hΩΩ₀]
    exact hsyl
  have hNX : ∀ N : Subgroup (MulAut ↥(VZ T M)), N ≤ N₁ ⊔ N₂ → N ≤ autI hV M := by
    intro N hN g hg
    have : g ∈ Ω := by
      rw [← hΩeq]
      exact hN hg
    exact ((hΩ g).1 this).1
  have hU4 : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := hK4.1
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T hT
  have hle : autI hV (UH153 T M V₁ Mc) ≤ autI hV T := autI_U_le_T cx
  have hidx : (autI hV (UH153 T M V₁ Mc)).relIndex (autI hV T) = 2 := by
    have hmul := Subgroup.card_mul_index ((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T))
    have hc : Nat.card ↥((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T)) = 4 := by
      rw [← hU4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hc, hT8] at hmul
    show ((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T)).index = 2
    omega
  obtain ⟨r, hrT, hr1, -, hrc, hrcen, hrinv⟩ := hS.exists_central hT
  have hr : r = s₁ * s₂ := (eq_one_or_mul_of_central hS hT hF hrT hrc).resolve_left hr1
  have hrU : r ∈ autI hV (UH153 T M V₁ Mc) := by
    rw [hr]
    exact mul_mem_autI_U cx h1 hS hF
  obtain ⟨e₁⟩ := c.h53one.iso₁
  obtain ⟨e₂⟩ := c.h53one.iso₂
  exact exists_UbData (W := Wd cx) (X := autI hV M) e₁ e₂ c.h53one.comm c.h53one.inf hsyl'
    (hNX N₁ le_sup_left) (hNX N₂ le_sup_right) hle (fun h hh n hn => autI_U_normal cx hh hn)
    (fun a ha b hb => autI_U_comm cx ha hb) hidx hrU hr1 hrc hrinv hrcen

end Basic

end S153E56f

end CFSG.Quasithin
