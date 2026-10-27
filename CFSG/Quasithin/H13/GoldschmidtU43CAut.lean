module

public import CFSG.Quasithin.H13.GoldschmidtU43CPlanes
public import CFSG.Quasithin.H13.GoldschmidtU43BPhi2

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

@[expose] def SwapA (g : MulAut (Multiplicative V4)) : Prop :=
  (∀ v, InP1 v → InP2 (vapp g v)) ∧ (∀ v, InP2 v → InP1 (vapp g v))

theorem swapC_iff (g : MulAut (Multiplicative V4)) : SwapC (colsOf g) ↔ SwapA g := by
  unfold SwapC SwapA
  simp only [vapp_eq_app]

theorem cube1_iff (g : MulAut (Multiplicative V4)) : Cube1 (colsOf g) ↔ g ^ 3 = 1 := by
  unfold Cube1
  rw [← colsOf_mul, ← colsOf_mul, ← colsOf_one, colsOf_eq_iff, pow_three]

theorem comp_eq_idc_iff (g h : MulAut (Multiplicative V4)) :
    comp (colsOf g) (colsOf h) = idc ↔ g * h = 1 := by
  rw [← colsOf_mul, ← colsOf_one, colsOf_eq_iff]

theorem cols_eq_idc_iff (g : MulAut (Multiplicative V4)) : colsOf g = idc ↔ g = 1 := by
  rw [← colsOf_one, colsOf_eq_iff]

@[expose] def Rbar : Subgroup (MulAut (Multiplicative V4)) where
  carrier := {g | g ∈ Oq ∧ g ^ 3 = 1}
  mul_mem' := by
    rintro g g' ⟨hg, hg3⟩ ⟨hg', hg3'⟩
    refine ⟨mul_mem hg hg', ?_⟩
    have := cube1_closed (toOC ⟨g, hg⟩) (toOC ⟨g', hg'⟩)
      (by rw [toOC_mk_cols, cube1_iff]; exact hg3) (by rw [toOC_mk_cols, cube1_iff]; exact hg3')
    rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, cube1_iff] at this
    exact this
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' := by
    rintro g ⟨hg, hg3⟩
    exact ⟨inv_mem hg, by rw [inv_pow, hg3, inv_one]⟩

theorem conj_mem_Rbar {g r : MulAut (Multiplicative V4)} (hg : g ∈ Oq) (hr : r ∈ Rbar) :
    g * r * g⁻¹ ∈ Rbar :=
  ⟨mul_mem (mul_mem hg hr.1) (inv_mem hg), by
    rw [conj_pow, hr.2]
    group⟩

theorem card_Rbar : Nat.card Rbar = 9 := by
  let f : Rbar → {x : OC // Cube1 x.cols} := fun g =>
    ⟨toOC ⟨g.1, g.2.1⟩, by rw [toOC_mk_cols, cube1_iff]; exact g.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' hg
      have := toOC_injective (congrArg Subtype.val hg)
      exact Subtype.ext (Subtype.mk.inj this)
    · rintro ⟨x, hx⟩
      obtain ⟨α, rfl⟩ := toOC_surjective x
      exact ⟨⟨α.1, α.2, by rw [← cube1_iff, ← toOC_mk_cols α.1 α.2]; exact hx⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_cube1

theorem Rbar_fixed {ξ : V4} (hξ : ξ ≠ 0) : ∃ r ∈ Rbar, vapp r ξ ≠ ξ := by
  obtain ⟨x, hx, hxξ⟩ := cube1_fixed ξ hξ
  refine ⟨ofOC x, ⟨ofOC_mem x, ?_⟩, ?_⟩
  · rw [← cube1_iff, colsOf_ofOC]; exact hx
  · rw [vapp_eq_app, colsOf_ofOC]; exact hxξ

theorem fix_swapA {τ α : V4} (hL : LinePair τ α) {g : MulAut (Multiplicative V4)} (hg : g ∈ Oq)
    (h1 : vapp g τ = τ) (h2 : vapp g α = α) (hne : g ≠ 1) :
    SwapA g ∧ g * g = 1 ∧ ∀ ξ : V4, vapp g ξ = ξ → Aset τ α ξ := by
  have key := fix_swap τ α hL (toOC ⟨g, hg⟩) (by
      unfold FixPair
      rw [toOC_mk_cols, ← vapp_eq_app, ← vapp_eq_app]
      exact ⟨h1, h2⟩)
    (by rw [toOC_mk_cols]; exact fun h => hne ((cols_eq_idc_iff g).1 h))
  rw [toOC_mk_cols] at key
  refine ⟨(swapC_iff g).1 key.1, (comp_eq_idc_iff g g).1 key.2.1, fun ξ hξ => key.2.2 ξ ?_⟩
  rw [← vapp_eq_app]; exact hξ

theorem fix_pairA {τ α β : V4} (hL : LinePair τ α) (hL' : LinePair τ β) (hb : bq α β = 1)
    {g g' : MulAut (Multiplicative V4)} (hg : g ∈ Oq) (hg' : g' ∈ Oq) (h1 : vapp g τ = τ)
    (h2 : vapp g α = α) (hne : g ≠ 1) (h1' : vapp g' τ = τ) (h2' : vapp g' β = β)
    (hne' : g' ≠ 1) : g * g' = g' * g ∧ g ≠ g' := by
  have key := fix_pair τ α β hL hL' hb (toOC ⟨g, hg⟩) (by
      unfold FixPair
      rw [toOC_mk_cols, ← vapp_eq_app, ← vapp_eq_app]
      exact ⟨h1, h2⟩)
    (by rw [toOC_mk_cols]; exact fun h => hne ((cols_eq_idc_iff g).1 h)) (toOC ⟨g', hg'⟩) (by
      unfold FixPair
      rw [toOC_mk_cols, ← vapp_eq_app, ← vapp_eq_app]
      exact ⟨h1', h2'⟩)
    (by rw [toOC_mk_cols]; exact fun h => hne' ((cols_eq_idc_iff g').1 h))
  rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul, ← colsOf_mul, colsOf_eq_iff] at key
  exact ⟨key.1, fun h => key.2 (by rw [h])⟩

@[expose] def SwapPairA (g g' : MulAut (Multiplicative V4)) : Prop :=
  SwapA g ∧ SwapA g' ∧ g * g = 1 ∧ g' * g' = 1 ∧ g * g' = g' * g ∧ g ≠ g'

theorem swapPair_iff (g g' : MulAut (Multiplicative V4)) :
    SwapPair (colsOf g) (colsOf g') ↔ SwapPairA g g' := by
  unfold SwapPair SwapPairA
  rw [swapC_iff, swapC_iff, comp_eq_idc_iff, comp_eq_idc_iff, ← colsOf_mul, ← colsOf_mul]
  simp only [ne_eq, colsOf_eq_iff]

theorem cprime_invA {g g' : MulAut (Multiplicative V4)} (hg : g ∈ Oq) (hg' : g' ∈ Oq)
    (hp : SwapPairA g g') {r : MulAut (Multiplicative V4)} (hr : r ∈ Rbar) :
    (g * g') * r * (g * g')⁻¹ = r⁻¹ := by
  have key := cprime_inv (toOC ⟨g, hg⟩) (toOC ⟨g', hg'⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, swapPair_iff]; exact hp) (toOC ⟨r, hr.1⟩)
    (by rw [toOC_mk_cols, cube1_iff]; exact hr.2)
  rw [toOC_mk_cols, toOC_mk_cols, toOC_mk_cols] at key
  simp only [← colsOf_mul, colsOf_eq_iff] at key
  have hc : (g * g')⁻¹ = g * g' := by
    rw [inv_eq_iff_mul_eq_one]
    calc g * g' * (g * g') = g * (g' * g) * g' := by group
      _ = g * (g * g') * g' := by rw [hp.2.2.2.2.1]
      _ = (g * g) * (g' * g') := by group
      _ = 1 := by rw [hp.2.2.1, hp.2.2.2.1, one_mul]
  rw [hc, mul_assoc (g * g') r (g * g'), key]
  have h3 : r * r * r = 1 := by rw [← pow_three']; exact hr.2
  exact (inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h3 : r * (r * r) = 1)).symm

theorem cprime_reflA {g g' : MulAut (Multiplicative V4)} (hg : g ∈ Oq) (hg' : g' ∈ Oq)
    (hp : SwapPairA g g') : ∃ n : V4, InP1 n ∧ n ≠ 0 ∧ vapp (g * g') n = n ∧
      ∀ ξ : V4, InP1 ξ → ξ ≠ 0 → ξ ≠ n → vapp (g * g') ξ = ξ + n := by
  have key := cprime_refl (toOC ⟨g, hg⟩) (toOC ⟨g', hg'⟩)
    (by rw [toOC_mk_cols, toOC_mk_cols, swapPair_iff]; exact hp)
  rw [toOC_mk_cols, toOC_mk_cols, ← colsOf_mul] at key
  obtain ⟨n, h1, h2, h3, h4⟩ := key
  refine ⟨n, h1, h2, by rw [vapp_eq_app]; exact h3, fun ξ hξ hξ0 hξn => ?_⟩
  rw [vapp_eq_app]
  exact h4 ξ hξ hξ0 hξn

theorem exists_rhoA : ∃ ρ ∈ Rbar, ρ ≠ 1 ∧ ∀ v, InP2 v → vapp ρ v = v := by
  obtain ⟨x, hx, hne, hfix⟩ := exists_rho1
  refine ⟨ofOC x, ⟨ofOC_mem x, ?_⟩, ?_, fun v hv => ?_⟩
  · rw [← cube1_iff, colsOf_ofOC]; exact hx
  · rw [Ne, ← cols_eq_idc_iff, colsOf_ofOC]; exact hne
  · rw [vapp_eq_app, colsOf_ofOC]; exact hfix v hv

theorem rho_rotA {ρ : MulAut (Multiplicative V4)} (hρ : ρ ∈ Rbar) (hne : ρ ≠ 1)
    (hfix : ∀ v, InP2 v → vapp ρ v = v) {ξ : V4} (hξ : InP1 ξ) (hξ0 : ξ ≠ 0) :
    vapp ρ ξ ≠ ξ ∧ ξ + vapp ρ ξ + vapp ρ (vapp ρ ξ) = 0 := by
  have key := rho_rot (toOC ⟨ρ, hρ.1⟩) (by rw [toOC_mk_cols, cube1_iff]; exact hρ.2)
    (by rw [toOC_mk_cols]; exact fun h => hne ((cols_eq_idc_iff ρ).1 h))
    (by
      intro v hv
      rw [toOC_mk_cols, ← vapp_eq_app]
      exact hfix v hv) ξ hξ hξ0
  rw [toOC_mk_cols, ← vapp_eq_app, ← vapp_eq_app] at key
  exact key

theorem span_fourA {s ρ : MulAut (Multiplicative V4)} (hs : s ∈ Oq) (hρ : ρ ∈ Rbar)
    (hsw : SwapA s) (hs2 : s * s = 1) (hne : ρ ≠ 1) (hfix : ∀ v, InP2 v → vapp ρ v = v)
    {n : V4} (hn : InP1 n) (hn0 : n ≠ 0) (ξ : V4) :
    ∃ e₁ e₂ e₃ e₄ : ZMod 2, ξ = e₁ • n + e₂ • vapp ρ (vapp ρ n) + e₃ • vapp s n +
      e₄ • vapp s (vapp ρ (vapp ρ n)) := by
  have key := span_four (toOC ⟨s, hs⟩) (by rw [toOC_mk_cols, swapC_iff]; exact hsw)
    (by rw [toOC_mk_cols, comp_eq_idc_iff]; exact hs2) (toOC ⟨ρ, hρ.1⟩)
    (by rw [toOC_mk_cols, cube1_iff]; exact hρ.2)
    (by rw [toOC_mk_cols]; exact fun h => hne ((cols_eq_idc_iff ρ).1 h))
    (by
      intro v hv
      rw [toOC_mk_cols, ← vapp_eq_app]
      exact hfix v hv) n hn hn0 ξ
  simp only [toOC_mk_cols, ← vapp_eq_app] at key
  exact key

end CFSG.Quasithin.H13.U43
