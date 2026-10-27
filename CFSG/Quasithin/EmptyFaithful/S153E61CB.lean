module

public import CFSG.Quasithin.EmptyFaithful.S153E55D

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E61C

open CFSG.Quasithin.S153E

section Abstract

variable {G : Type*} [Group G]

theorem comm_of_sq_eq_one {A : Subgroup G} (h : ∀ a ∈ A, a * a = 1) {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    a * b = b * a := by
  have h1 := h _ (A.mul_mem ha hb)
  have h2 := h _ ha
  have h3 := h _ hb
  have e1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right h2
  have e2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right h3
  have e3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, e1, e2] at e3
  exact e3.symm

theorem sq_eq_one_of_fpf {I P V N₁ N₂ P₁ P₂ : Subgroup G} (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂)
    (hV2 : ∀ v ∈ V, v * v = 1) (h₁sq : ∀ x ∈ P₁, x * x ∈ V) {y : G} (hyN : y ∈ N₂)
    (hy : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1) : ∀ a ∈ P₁, a * a = 1 := by
  intro a ha
  have ha' := ha
  rw [pd.cent₁] at ha'
  obtain ⟨haP, -, hac⟩ := ha'
  set w : G := y * a * y⁻¹ * a⁻¹ with hw
  have hwV : w ∈ V := by
    have h1 := V.inv_mem (hac y hyN)
    have e : (a * y * a⁻¹ * y⁻¹)⁻¹ = w := by rw [hw]; group
    rwa [e] at h1
  have hwa : y * a * y⁻¹ = w * a := by rw [hw]; group
  have hc : w * a = a * w := pd.V_central w hwV a haP
  have hfix : y * (a * a) * y⁻¹ = a * a := by
    calc y * (a * a) * y⁻¹ = (y * a * y⁻¹) * (y * a * y⁻¹) := by group
      _ = (w * a) * (w * a) := by rw [hwa]
      _ = w * (a * w) * a := by group
      _ = w * (w * a) * a := by rw [← hc]
      _ = (w * w) * (a * a) := by group
      _ = a * a := by rw [hV2 w hwV, one_mul]
  exact hy _ (h₁sq a ha) hfix

end Abstract

section Chain

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_fpf (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    (hNY : N ≤ autI cx.c.hyp.elemAbelian (Y153 Mc M ⊔ UH153 T M V₁ Mc))
    (e : ↥N ≃* Equiv.Perm (Fin 3)) (hcomm : commV N = ⊤) :
    ∃ y : G, y ∈ Ni153 T Mc M V₁ N ∧ ∀ v ∈ VZ T M, y * v * y⁻¹ = v → v = 1 := by
  have hV := cx.c.hyp.elemAbelian
  let a₀ : ↥N := e.symm (finRotate 3)
  have ha₀3 : a₀ ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simp only [a₀, MulEquiv.apply_symm_apply]
    decide
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    have h1 := congrArg e h
    simp only [a₀, MulEquiv.apply_symm_apply, map_one] at h1
    exact absurd h1 (by decide)
  have ha3 : (a₀ : MulAut (IntMod (VZ T M) hV)) ^ 3 = 1 := by
    have := congrArg Subtype.val ha₀3
    simpa using this
  have ha1 : (a₀ : MulAut (IntMod (VZ T M) hV)) ≠ 1 := fun h => ha₀1 (Subtype.ext (by simpa using h))
  obtain ⟨y', hy'YU, hy'⟩ := (mem_autI hV).1 (hNY a₀.2)
  refine ⟨(y' : G), mem_preAut153.2 ⟨hy'YU, y'.2, ?_⟩, ?_⟩
  · show convI hV y' ∈ N
    rw [hy']
    exact a₀.2
  · intro v hv hvy
    have hfix := S153E55.fixV_eq_bot_of_perm (W := IntMod (VZ T M) hV) IntMod.sq_eq_one e hcomm a₀.2 ha3 ha1
    have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (Subgroup.zpowers (a₀ : MulAut (IntMod (VZ T M) hV))) := by
      rw [mem_fixV_zpowers_iff, ← hy']
      refine IntMod.val_injective ?_
      rw [convI_apply_val]
      exact hvy
    rw [hfix, Subgroup.mem_bot] at hw
    exact congrArg IntMod.val hw

variable {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y₀ t₁ : G}

theorem Pi_sq_eq_one (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15354 cx N₁ N₂ g s) :
    (∀ a ∈ Pi153 T Mc M V₁ N₁ g, a * a = 1) ∧ (∀ a ∈ Pi153 T Mc M V₁ N₂ g, a * a = 1) := by
  have hV := cx.c.hyp.elemAbelian
  have hV2 : ∀ v ∈ VZ T M, v * v = 1 := fun v hv => by
    rw [← pow_two]
    exact hV.2 v hv
  have pd := S153E55.pdecomp cx c
  have hΩ := S153E55.autI_YU_eq cx c.h53one
  have hN₁Y : N₁ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := hΩ ▸ le_sup_left
  have hN₂Y : N₂ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := hΩ ▸ le_sup_right
  obtain ⟨e₁⟩ := c.h53one.iso₁
  obtain ⟨e₂⟩ := c.h53one.iso₂
  obtain ⟨y₁, hy₁N, hy₁f⟩ := exists_fpf cx hN₁Y e₁ (S153E55.commV_eq_top cx hN₁Y c.h53one.comm₁)
  obtain ⟨y₂, hy₂N, hy₂f⟩ := exists_fpf cx hN₂Y e₂ (S153E55.commV_eq_top cx hN₂Y c.h53one.comm₂)
  exact ⟨sq_eq_one_of_fpf pd hV2 (S153E55.sq_mem_of_nat c.h54.four_nat₁) hy₂N hy₂f,
    sq_eq_one_of_fpf pd.symm hV2 (S153E55.sq_mem_of_nat c.h54.four_nat₂) hy₁N hy₁f⟩

end Chain

end S153E61C

end CFSG.Quasithin
