module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G) (H : Subgroup G) {α β : V}
include F

theorem edgeTransitive_of_locTrans (hαβ : Γ.Adj α β)
    (hα : ∀ a b, Γ.Adj α a → Γ.Adj α b → ∃ h ∈ H, h • α = α ∧ h • a = b)
    (hβ : ∀ a b, Γ.Adj β a → Γ.Adj β b → ∃ h ∈ H, h • β = β ∧ h • a = b) :
    EdgeTransitive Γ H := by
  let P : V → Prop := fun v => ∃ h ∈ H, h • α = v
  let Q : V → Prop := fun v => ∃ h ∈ H, h • β = v
  have hPQ : ∀ u w, P u → Γ.Adj u w → Q w := by
    rintro u w ⟨h, hh, rfl⟩ hw
    have hw' : Γ.Adj α (h⁻¹ • w) := by
      have := (F.adj_smul h⁻¹ _ _).2 hw
      rwa [inv_smul_smul] at this
    obtain ⟨k, hk, -, hkb⟩ := hα β _ hαβ hw'
    exact ⟨h * k, H.mul_mem hh hk, by rw [mul_smul, hkb, smul_inv_smul]⟩
  have hQP : ∀ u w, Q u → Γ.Adj u w → P w := by
    rintro u w ⟨h, hh, rfl⟩ hw
    have hw' : Γ.Adj β (h⁻¹ • w) := by
      have := (F.adj_smul h⁻¹ _ _).2 hw
      rwa [inv_smul_smul] at this
    obtain ⟨k, hk, -, hka⟩ := hβ α _ hαβ.symm hw'
    exact ⟨h * k, H.mul_mem hh hk, by rw [mul_smul, hka, smul_inv_smul]⟩
  have hall : ∀ v, P v ∨ Q v := by
    intro v
    obtain ⟨p⟩ := F.isTree.connected.preconnected α v
    have key : ∀ (u w : V) (p : Γ.Walk u w), (P u ∨ Q u) → (P w ∨ Q w) := by
      intro u w p
      induction p with
      | nil => exact id
      | cons h p ih =>
        intro hu
        refine ih ?_
        rcases hu with hu | hu
        · exact Or.inr (hPQ _ _ hu h)
        · exact Or.inl (hQP _ _ hu h)
    exact key α v p (Or.inl ⟨1, H.one_mem, one_smul _ _⟩)
  have hloc : ∀ v, (P v ∨ Q v) → ∀ a b, Γ.Adj v a → Γ.Adj v b → ∃ h ∈ H, h • v = v ∧ h • a = b := by
    intro v hv a b ha hb
    rcases hv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · have ha' : Γ.Adj α (g⁻¹ • a) := by
        have := (F.adj_smul g⁻¹ _ _).2 ha
        rwa [inv_smul_smul] at this
      have hb' : Γ.Adj α (g⁻¹ • b) := by
        have := (F.adj_smul g⁻¹ _ _).2 hb
        rwa [inv_smul_smul] at this
      obtain ⟨k, hk, hkα, hkab⟩ := hα _ _ ha' hb'
      refine ⟨g * k * g⁻¹, H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg), ?_, ?_⟩
      · rw [mul_smul, mul_smul, ← mul_smul g⁻¹ g, inv_mul_cancel, one_smul, hkα]
      · rw [mul_smul, mul_smul, hkab, smul_inv_smul]
    · have ha' : Γ.Adj β (g⁻¹ • a) := by
        have := (F.adj_smul g⁻¹ _ _).2 ha
        rwa [inv_smul_smul] at this
      have hb' : Γ.Adj β (g⁻¹ • b) := by
        have := (F.adj_smul g⁻¹ _ _).2 hb
        rwa [inv_smul_smul] at this
      obtain ⟨k, hk, hkβ, hkab⟩ := hβ _ _ ha' hb'
      refine ⟨g * k * g⁻¹, H.mul_mem (H.mul_mem hg hk) (H.inv_mem hg), ?_, ?_⟩
      · rw [mul_smul, mul_smul, ← mul_smul g⁻¹ g, inv_mul_cancel, one_smul, hkβ]
      · rw [mul_smul, mul_smul, hkab, smul_inv_smul]
  have move : ∀ a b a' b' : V, Γ.Adj a b → Γ.Adj a' b' → (P a' ∨ Q a') →
      (∃ g ∈ H, g • a = a') → ∃ g ∈ H, g • a = a' ∧ g • b = b' := by
    rintro a b a' b' hab ha'b' ha' ⟨g, hg, hga⟩
    have h1 : Γ.Adj a' (g • b) := by
      have := (F.adj_smul g a b).2 hab
      rwa [hga] at this
    obtain ⟨k, hk, hka, hkb⟩ := hloc a' ha' _ _ h1 ha'b'
    exact ⟨k * g, H.mul_mem hk hg, by rw [mul_smul, hga, hka], by rw [mul_smul, hkb]⟩
  have orbit : ∀ x y : V, (P x ∧ P y) ∨ (Q x ∧ Q y) → ∃ g ∈ H, g • x = y := by
    rintro x y (⟨⟨g, hg, rfl⟩, ⟨g', hg', rfl⟩⟩ | ⟨⟨g, hg, rfl⟩, ⟨g', hg', rfl⟩⟩)
    · exact ⟨g' * g⁻¹, H.mul_mem hg' (H.inv_mem hg), by rw [mul_smul, inv_smul_smul]⟩
    · exact ⟨g' * g⁻¹, H.mul_mem hg' (H.inv_mem hg), by rw [mul_smul, inv_smul_smul]⟩
  intro u v u' v' huv hu'v'
  have hu := hall u
  have hu' := hall u'
  rcases hu with hu | hu <;> rcases hu' with hu' | hu'
  ·
    obtain ⟨g, hg, h1, h2⟩ := move u v u' v' huv hu'v' (Or.inl hu') (orbit _ _ (Or.inl ⟨hu, hu'⟩))
    exact ⟨g, hg, Or.inl ⟨h1, h2⟩⟩
  ·
    have hv' : P v' := hQP _ _ hu' hu'v'
    obtain ⟨g, hg, h1, h2⟩ := move u v v' u' huv hu'v'.symm (Or.inl hv')
      (orbit _ _ (Or.inl ⟨hu, hv'⟩))
    exact ⟨g, hg, Or.inr ⟨h1, h2⟩⟩
  · have hv' : Q v' := hPQ _ _ hu' hu'v'
    obtain ⟨g, hg, h1, h2⟩ := move u v v' u' huv hu'v'.symm (Or.inr hv')
      (orbit _ _ (Or.inr ⟨hu, hv'⟩))
    exact ⟨g, hg, Or.inr ⟨h1, h2⟩⟩
  · obtain ⟨g, hg, h1, h2⟩ := move u v u' v' huv hu'v' (Or.inr hu') (orbit _ _ (Or.inr ⟨hu, hu'⟩))
    exact ⟨g, hg, Or.inl ⟨h1, h2⟩⟩

theorem eq_bot_of_locTrans {U : Subgroup G} (hαβ : Γ.Adj α β)
    (hU : ∀ u ∈ U, u • α = α ∧ u • β = β) (hN : H ≤ Subgroup.normalizer (U : Set G))
    (hα : ∀ a b, Γ.Adj α a → Γ.Adj α b → ∃ h ∈ H, h • α = α ∧ h • a = b)
    (hβ : ∀ a b, Γ.Adj β a → Γ.Adj β b → ∃ h ∈ H, h • β = β ∧ h • a = b) : U = ⊥ := by
  refine F.eq_bot_of_edgeTransitive hαβ hU fun u v u' v' huv hu'v' => ?_
  obtain ⟨h, hh, hcase⟩ := F.edgeTransitive_of_locTrans H hαβ hα hβ u v u' v' huv hu'v'
  exact ⟨h, hN hh, hcase⟩

end FanTree

end CFSG.Quasithin.Fan86
