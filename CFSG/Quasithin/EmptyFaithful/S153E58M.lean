module

public import CFSG.Quasithin.EmptyFaithful.S153E58L

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

open S153E57

section Perm

variable {W : Type} [CommGroup W] {H K : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W}
  {bil : W → W → ZMod 2}

theorem Setup58.W₂_ne_bot (hS : Setup58 H K W₁ W₂ bil) : W₂ ≠ ⊥ := by
  intro h
  have := hS.card₂
  rw [h, Subgroup.card_bot] at this
  omega

theorem Setup58.exists_ne_one₁ (hS : Setup58 H K W₁ W₂ bil) : ∃ a ∈ W₁, a ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact hS.W₁_ne_bot ((Subgroup.eq_bot_iff_forall W₁).2 hcon)

theorem Setup58.inf_eq_bot (hS : Setup58 H K W₁ W₂ bil) {x : W} (h₁ : x ∈ W₁) (h₂ : x ∈ W₂) : x = 1 := by
  have : x ∈ W₁ ⊓ W₂ := ⟨h₁, h₂⟩
  rw [hS.dir.2, Subgroup.mem_bot] at this
  exact this

theorem Setup58.cases_swap (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e)
    {h : MulAut W} (hh : h ∈ H) :
    ((∀ w ∈ W₁, h w ∈ W₁) ∧ ∀ w ∈ W₂, h w ∈ W₂) ∨ ((∀ w ∈ W₁, h w ∈ W₂) ∧ ∀ w ∈ W₂, h w ∈ W₁) := by
  have e₁ := hS.eq_or_eq_of_irr hT (isIrr_map hS.Kn hh hS.irr₁)
  have e₂ := hS.eq_or_eq_of_irr hT (isIrr_map hS.Kn hh hS.irr₂)
  have m₁ : ∀ w ∈ W₁, h w ∈ W₁.map (h : W →* W) := fun w hw => ⟨w, hw, rfl⟩
  have m₂ : ∀ w ∈ W₂, h w ∈ W₂.map (h : W →* W) := fun w hw => ⟨w, hw, rfl⟩
  have back : ∀ {S : Subgroup W} {w : W}, h w ∈ S.map (h : W →* W) → w ∈ S := by
    intro S w hw
    obtain ⟨w', hw', hww'⟩ := hw
    have : w' = w := h.injective hww'
    rw [← this]
    exact hw'
  rcases e₁ with e₁ | e₁ <;> rcases e₂ with e₂ | e₂
  ·
    exfalso
    apply hS.W₂_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have h1 : h w ∈ W₁.map (h : W →* W) := by rw [e₁, ← e₂]; exact m₂ w hw
    exact hS.inf_eq_bot (back h1) hw
  · left
    exact ⟨fun w hw => by have := m₁ w hw; rw [e₁] at this; exact this,
      fun w hw => by have := m₂ w hw; rw [e₂] at this; exact this⟩
  · right
    exact ⟨fun w hw => by have := m₁ w hw; rw [e₁] at this; exact this,
      fun w hw => by have := m₂ w hw; rw [e₂] at this; exact this⟩
  ·
    exfalso
    apply hS.W₁_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have h1 : h w ∈ W₂.map (h : W →* W) := by rw [e₂, ← e₁]; exact m₁ w hw
    exact hS.inf_eq_bot hw (back h1)

theorem exists_K_agree {K : Subgroup (MulAut W)} {W₁ : Subgroup W} {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π)
    {h : MulAut W} (hh : ∀ w ∈ W₁, h w ∈ W₁) [Finite W] :
    ∃ k ∈ K, ∀ w ∈ W₁, k w = h w := by
  obtain ⟨e, -, he⟩ := exists_coords_of_realizes hπ
  let r : ↥W₁ →* ↥W₁ := ((h : W →* W).comp W₁.subtype).codRestrict W₁ (fun u => hh u u.2)
  have hrinj : Function.Injective r := fun a b hab => Subtype.ext (h.injective (congrArg Subtype.val hab))
  have : Finite ↥W₁ := inferInstance
  have hrbij : Function.Bijective r := ⟨hrinj, Finite.injective_iff_surjective.1 hrinj⟩
  let α : MulAut V3 := e.symm.trans ((MulEquiv.ofBijective r hrbij).trans e)
  let γ : GL (Fin 3) (ZMod 2) := mulAutPiEquivGL 3 α
  let γ' : ↥(StatedSL 3 (ZMod 2)) := ⟨γ, mem_statedSL_three_two γ⟩
  refine ⟨(π γ' : MulAut W), (π γ').2, fun w hw => ?_⟩
  have h1 := he γ' ⟨w, hw⟩ (hπ.2.2.2.1 (π γ') w hw)
  have h2 : natAct (StatedSL 3 (ZMod 2)) γ' (e ⟨w, hw⟩) = α (e ⟨w, hw⟩) := by
    have := mulAutPiEquivGL_symm_apply 3 γ (e ⟨w, hw⟩)
    rw [show γ = mulAutPiEquivGL 3 α from rfl, MulEquiv.symm_apply_apply] at this
    rw [this]
    rfl
  rw [h2] at h1
  have h3 : α (e ⟨w, hw⟩) = e (r ⟨w, hw⟩) := by
    simp [α]
  rw [h3] at h1
  have h4 := e.injective h1
  exact congrArg Subtype.val h4

variable [Finite W]

omit [Finite W] in
theorem Setup58.eq_one_of_triv₁ (hS : Setup58 H K W₁ W₂ bil) {e : ↥W₁ ≃* V3} (hT : TransvIn K W₁ e)
    {c : MulAut W} (hc : c ∈ H) (h1 : ∀ w ∈ W₁, c w = w) : c = 1 := by
  have hst₂ : ∀ w ∈ W₂, c w ∈ W₂ := by
    rcases hS.cases_swap hT hc with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exfalso
      obtain ⟨a, haW₁, ha1⟩ := hS.exists_ne_one₁
      have h2 := h a haW₁
      rw [h1 a haW₁] at h2
      exact ha1 (hS.inf_eq_bot haW₁ h2)
  have h2 : ∀ y ∈ W₂, c y = y := by
    intro y hy
    have h3 : c y * y⁻¹ = 1 := by
      apply hS.eq_one_of_orth hT _ (W₂.mul_mem (hst₂ y hy) (W₂.inv_mem hy))
      intro x hx
      have h4 := hS.bil_inv c hc x y
      rw [h1 x hx] at h4
      rw [hS.bil_right, hS.bil_inv_right, h4]
      exact CharTwo.add_self_eq_zero _
    exact mul_inv_eq_one.1 h3
  apply MulEquiv.ext
  intro w
  have hw : w ∈ W₁ ⊔ W₂ := hS.dir.1 ▸ Subgroup.mem_top w
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul, h1 x hx, h2 y hy, MulAut.one_apply]

theorem Setup58.mem_K_of_stab (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) {h : MulAut W} (hh : h ∈ H)
    (hst : ∀ w ∈ W₁, h w ∈ W₁) : h ∈ K := by
  obtain ⟨e, hT, -⟩ := exists_coords_of_realizes hπ
  obtain ⟨k, hkK, hk⟩ := exists_K_agree hπ hst
  have hc : k⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hS.KH hkK)) hh
  have h1 : ∀ w ∈ W₁, (k⁻¹ * h) w = w := by
    intro w hw
    rw [MulAut.mul_apply, ← hk w hw]
    exact MulAut.inv_apply_self _ _ _
  have := hS.eq_one_of_triv₁ hT hc h1
  have h2 : h = k := (inv_mul_eq_one.1 this).symm
  rw [h2]
  exact hkK

theorem Setup58.swap_of_not_mem_K (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) {h : MulAut W} (hh : h ∈ H)
    (hnot : h ∉ K) : (∀ w ∈ W₁, h w ∈ W₂) ∧ ∀ w ∈ W₂, h w ∈ W₁ := by
  obtain ⟨e, hT, -⟩ := exists_coords_of_realizes hπ
  rcases hS.cases_swap hT hh with ⟨h1, -⟩ | h
  · exact absurd (hS.mem_K_of_stab hπ hh h1) hnot
  · exact h

theorem Setup58.mem_K_of_fix (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) {h : MulAut W} (hh : h ∈ H) {w : W}
    (hw : w ∈ W₁) (hw1 : w ≠ 1) (hfix : h w = w) : h ∈ K := by
  obtain ⟨e, hT, -⟩ := exists_coords_of_realizes hπ
  rcases hS.cases_swap hT hh with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hS.mem_K_of_stab hπ hh h1
  · exfalso
    have h2 := h1 w hw
    rw [hfix] at h2
    exact hw1 (hS.inf_eq_bot hw h2)

omit [Finite W] in
theorem Setup58.exists_swap (hS : Setup58 H K W₁ W₂ bil) : ∃ h₀ ∈ H, ¬ ∀ w ∈ W₁, h₀ w ∈ W₁ := by
  by_contra hcon
  push Not at hcon
  rcases hS.Hirr.2.2 W₁ le_top (fun k hk b hb => hcon k hk b hb) with h | h
  · exact hS.W₁_ne_bot h
  · apply hS.W₂_ne_bot
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have : w ∈ W₁ := h ▸ Subgroup.mem_top w
    exact hS.inf_eq_bot this hw

theorem Setup58.relIndex_eq_two (hS : Setup58 H K W₁ W₂ bil) {π : ↥(StatedSL 3 (ZMod 2)) →* ↥K}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π) : K.relIndex H = 2 := by
  obtain ⟨e, hT, -⟩ := exists_coords_of_realizes hπ
  obtain ⟨h₀, hh₀, hns⟩ := hS.exists_swap
  have hh₀K : h₀ ∉ K := fun hK => hns (fun w hw => hS.inv₁ h₀ hK w hw)
  have hsw₀ := hS.swap_of_not_mem_K hπ hh₀ hh₀K
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨h₀, hh₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hbK : (b : MulAut W) ∈ K
  · right
    refine ⟨hbK, fun hbh => hh₀K ?_⟩
    have := K.mul_mem (K.inv_mem hbK) hbh
    simpa using this
  · left
    refine ⟨?_, hbK⟩
    have hsw := hS.swap_of_not_mem_K hπ b.2 hbK
    refine hS.mem_K_of_stab hπ (H.mul_mem b.2 hh₀) fun w hw => ?_
    rw [MulAut.mul_apply]
    exact hsw.2 _ (hsw₀.1 w hw)

end Perm

end S153E58

end CFSG.Quasithin
