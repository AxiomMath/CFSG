module

public import CFSG.Quasithin.Background.G10FourSetup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem G101Hyp.exists_move (hyp : G101Hyp B Γ v₁ W X X₀) (hW : 2 ≤ Module.finrank (ZMod 2) W) :
    ∃ w ∈ W, ∃ x ∈ X, x w = w + v₁ := by
  have hex : ∃ w ∈ W, w ∉ Submodule.span (ZMod 2) {v₁} := by
    by_contra hcon
    push Not at hcon
    have hle : W ≤ Submodule.span (ZMod 2) {v₁} := hcon
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hyp.point] at this
    omega
  obtain ⟨w, hwW, hw⟩ := hex
  have hnot : (⟨w, hwW⟩ : W) ∉ Submodule.span (ZMod 2) {(⟨v₁, hyp.mem_W⟩ : W)} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    apply hw
    rw [Submodule.mem_span_singleton]
    exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨f, hf0, hf1⟩ := g10Four_exists_dual W ⟨v₁, hyp.mem_W⟩ ⟨w, hwW⟩ hnot
  obtain ⟨x, hx, hxf⟩ := hyp.transvection_full f hf0
  refine ⟨w, hwW, x, hx, ?_⟩
  have := hxf ⟨w, hwW⟩
  simpa [hf1] using this

theorem G101Hyp.sup_eq_top (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hUX : Invariant X U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0) : U ⊔ W = ⊤ := by
  obtain ⟨hWU, -, -, -, -⟩ := hyp.counting U hUX h1 h2
  have hWbot : W ⊓ U = ⊥ := hyp.inf_eq_bot U hUX h1
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [inf_comm, hWbot, finrank_bot] at this
  omega

theorem G101Hyp.exists_common_center (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hUX : Invariant X U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0) {U' : Submodule (ZMod 2) V}
    (hU'X : Invariant X U') (hcompl : IsCompl U U') :
    ∃ c' ∈ U', c' ≠ 0 ∧ ∀ x ∈ X, ∀ u' ∈ U', ∃ l : ZMod 2, x u' - u' = l • c' := by
  have hsup := hyp.sup_eq_top hUX h1 h2
  have hdecW : ∀ v : V, ∃ a ∈ U, ∃ w ∈ W, v = a + w := by
    intro v
    have : v ∈ U ⊔ W := by
      rw [hsup]
      trivial
    obtain ⟨a, ha, w, hw, hv⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, w, hw, hv.symm⟩
  have hdecU' : ∃ a ∈ U, ∃ b ∈ U', v₁ = a + b := by
    have : v₁ ∈ U ⊔ U' := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hv⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, b, hb, hv.symm⟩
  obtain ⟨u₁, hu₁, c', hc', hv₁⟩ := hdecU'
  have hc0 : c' ≠ 0 := by
    intro h0
    apply h1
    rw [hv₁, h0, add_zero]
    exact hu₁
  refine ⟨c', hc', hc0, ?_⟩
  intro x hx u' hu'
  obtain ⟨a, haU, w', hw'W, hu'e⟩ := hdecW u'
  obtain ⟨f, -, hxf⟩ := hyp.transvection x hx
  have hxw := hxf ⟨w', hw'W⟩
  simp only at hxw
  refine ⟨f ⟨w', hw'W⟩, ?_⟩
  have hd : x u' - u' - f ⟨w', hw'W⟩ • c' ∈ U ⊓ U' := by
    constructor
    · have e1 : x u' - u' - f ⟨w', hw'W⟩ • c' = (x a - a) + f ⟨w', hw'W⟩ • u₁ := by
        rw [hu'e, map_add, hxw]
        have e2 : c' = v₁ - u₁ := by rw [hv₁]; abel
        rw [e2, smul_sub]
        abel
      rw [e1]
      exact U.add_mem (U.sub_mem (hUX x hx a haU) haU) (U.smul_mem _ hu₁)
    · exact U'.sub_mem (U'.sub_mem (hU'X x hx u' hu') hu') (U'.smul_mem _ hc')
  rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hd
  exact sub_eq_zero.1 hd

theorem partner_contradiction (hyp : G101Hyp B Γ v₁ W X X₀) (U : Submodule (ZMod 2) V)
    (hUX : Invariant X U) (h1 : v₁ ∉ U) (h2 : ∃ u ∈ U, B v₁ u ≠ 0)
    (hn3 : 3 ≤ Module.finrank (ZMod 2) U)
    (hdim : 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V)
    (U' : Submodule (ZMod 2) V) (hU'X : Invariant X U') (hcompl : IsCompl U U')
    (h1' : v₁ ∉ U') : False := by
  obtain ⟨hWU, -, -, -, -⟩ := hyp.counting U hUX h1 h2
  have hWn : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U := by omega
  have hsup := hyp.sup_eq_top hUX h1 h2
  have hdecW : ∀ v : V, ∃ a ∈ U, ∃ w ∈ W, v = a + w := by
    intro v
    have : v ∈ U ⊔ W := by
      rw [hsup]
      trivial
    obtain ⟨a, ha, w, hw, hv⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, w, hw, hv.symm⟩
  have hdecU' : ∀ v : V, ∃ a ∈ U, ∃ b ∈ U', v = a + b := by
    intro v
    have : v ∈ U ⊔ U' := by
      rw [hcompl.sup_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hv⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, b, hb, hv.symm⟩
  have hU'dim : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) U := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  have h2' : ∃ u' ∈ U', B v₁ u' ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hwW, x, hx, hxw⟩ := hyp.exists_move (by omega)
    obtain ⟨a, haU, b, hbU', hwab⟩ := hdecU' w
    have hBa : B v₁ a = 0 := by
      have e1 : a = w - b := by rw [hwab]; abel
      rw [e1, map_sub, hcon b hbU', hyp.isotropic v₁ hyp.mem_W w hwW]
      exact sub_self _
    have hxa : x a = a := hyp.fix_of_perp U hUX h1 hx haU hBa
    apply h1'
    have e2 : v₁ = x b - b := by
      have h3 : x w = x a + x b := by rw [hwab, map_add]
      rw [hxa] at h3
      have h4 : w + v₁ = a + x b := by rw [← hxw, h3]
      have h5 : v₁ = a + x b - w := by rw [← h4]; abel
      rw [h5, hwab]
      abel
    rw [e2]
    exact U'.sub_mem (hU'X x hx b hbU') hbU'
  obtain ⟨-, -, -, hfull', hker'⟩ := hyp.counting U' hU'X h1' h2'
  obtain ⟨c', hc', hc0, hcommon⟩ := hyp.exists_common_center hUX h1 h2 hU'X hcompl
  have hk2 : 2 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker ((B v₁).domRestrict U')) := by omega
  obtain ⟨a', ha', b', hb', ha0, hb0, hab⟩ := g10Four_exists_two_ne_zero (V := ↥U') _ hk2
  have hex : ∃ e : U', B v₁ (e : V) = 0 ∧ e ≠ 0 ∧ (e : V) ≠ c' := by
    by_cases hac : (a' : V) = c'
    · refine ⟨b', by simpa using hb', hb0, fun h => hab (Subtype.ext (hac.trans h.symm))⟩
    · exact ⟨a', by simpa using ha', ha0, hac⟩
  obtain ⟨e, he, he0, hec⟩ := hex
  obtain ⟨x, hx, hxe⟩ := hfull' e he
  obtain ⟨u₀, hu₀, hB₀⟩ := G101Hyp.exists_one U' h2'
  obtain ⟨l, hl⟩ := hcommon x hx u₀ hu₀
  have hmove := hxe ⟨u₀, hu₀⟩
  simp only [hB₀, one_smul] at hmove
  have hel : (e : V) = l • c' := by
    rw [← hl, hmove]
    abel
  rcases g10Four_zmod_two_cases l with rfl | rfl
  · apply he0
    apply Subtype.ext
    rw [hel, zero_smul]
    rfl
  · exact hec (by rw [hel, one_smul])

end CFSG.Quasithin
