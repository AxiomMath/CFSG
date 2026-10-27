module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TArc
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Quasithin.Fan86.Tutte

open CFSG.Quasithin.F6.GoldAmL3T

section Aux

variable {W : Type*} {Γ : SimpleGraph W} {A : Type*} [Group A] [MulAction A W]

private theorem two_others {x y : W} (hcard : Nat.card (Γ.neighborSet x) = 3)
    (hxy : Γ.Adj x y) :
    ∃ a b : W, a ≠ b ∧ Γ.Adj x a ∧ a ≠ y ∧ Γ.Adj x b ∧ b ≠ y ∧
      ∀ c, Γ.Adj x c → c ≠ y → c = a ∨ c = b := by
  have hn : (Γ.neighborSet x).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hmem : y ∈ Γ.neighborSet x := hxy
  have h2 : (Γ.neighborSet x \ {y}).ncard = 2 := by
    rw [Set.ncard_sdiff_singleton_of_mem hmem, hn]
  obtain ⟨a, b, hab, hset⟩ := Set.ncard_eq_two.mp h2
  have ha : a ∈ Γ.neighborSet x \ {y} := by rw [hset]; simp
  have hb : b ∈ Γ.neighborSet x \ {y} := by rw [hset]; simp
  refine ⟨a, b, hab, ha.1, ha.2, hb.1, hb.2, fun c hc hcy => ?_⟩
  have hc' : c ∈ Γ.neighborSet x \ {y} := ⟨hc, hcy⟩
  rw [hset] at hc'
  simpa using hc'

private theorem swap_of_moves
    (hadj : ∀ (a : A) (u v : W), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    {g : A} {x y c a b : W} (hcard : Nat.card (Γ.neighborSet x) = 3) (hxy : Γ.Adj x y)
    (hgx : g • x = x) (hgy : g • y = y) (hc : Γ.Adj x c) (hcy : c ≠ y) (hmove : g • c ≠ c)
    (ha : Γ.Adj x a) (hay : a ≠ y) (hb : Γ.Adj x b) (hby : b ≠ y) (hab : a ≠ b) :
    g • a = b := by
  obtain ⟨d, e, hde, hd, hdy, he, hey, hall⟩ := two_others hcard hxy
  have hmaps : ∀ u, Γ.Adj x u → u ≠ y → g • u = d ∨ g • u = e := by
    intro u hu huy
    have h1 : Γ.Adj x (g • u) := by
      have := (hadj g x u).2 hu
      rwa [hgx] at this
    exact hall _ h1 fun h => huy (smul_left_cancel g (h.trans hgy.symm))
  have hdd := hmaps d hd hdy
  have hee := hmaps e he hey
  have hsw : g • d = e ∧ g • e = d := by
    rcases hall c hc hcy with hcd | hce
    · rw [hcd] at hmove
      have h1 : g • d = e := hdd.resolve_left hmove
      exact ⟨h1, hee.resolve_right fun h => hde (smul_left_cancel g (h1.trans h.symm))⟩
    · rw [hce] at hmove
      have h1 : g • e = d := hee.resolve_right hmove
      exact ⟨hdd.resolve_left fun h => hde (smul_left_cancel g (h.trans h1.symm)), h1⟩
  rcases hall a ha hay with had | hae <;> rcases hall b hb hby with hbd | hbe
  · exact absurd (had.trans hbd.symm) hab
  · rw [had, hbe]
    exact hsw.1
  · rw [hae, hbd]
    exact hsw.2
  · exact absurd (hae.trans hbe.symm) hab

private theorem exists_conj
    (hadj : ∀ (a : A) (u v : W), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v) (n g : A) :
    ∃ n' : A, (∀ y : W, n' • g • y = g • n • y) ∧
      ∀ u : W, (∀ x, Γ.Adj u x → n • x = x) → ∀ x, Γ.Adj (g • u) x → n' • x = x := by
  refine ⟨g * n * g⁻¹, fun y => ?_, fun u h x hx => ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul]
  · have h1 : Γ.Adj u (g⁻¹ • x) := by
      have := (hadj g⁻¹ (g • u) x).2 hx
      rwa [inv_smul_smul] at this
    rw [mul_smul, mul_smul, h _ h1, smul_inv_smul]

private theorem triv_of_fix
    (h5 : ∀ (P : Arc Γ 5) (a : A), (∀ i, i ≤ 5 → a • P.vert i = P.vert i) → ∀ w : W, a • w = w)
    {m : A} {x₀ x₁ x₂ x₃ x₄ x₅ : W}
    (a₀ : Γ.Adj x₀ x₁) (a₁ : Γ.Adj x₁ x₂) (a₂ : Γ.Adj x₂ x₃) (a₃ : Γ.Adj x₃ x₄)
    (a₄ : Γ.Adj x₄ x₅) (b₀ : x₀ ≠ x₂) (b₁ : x₁ ≠ x₃) (b₂ : x₂ ≠ x₄) (b₃ : x₃ ≠ x₅)
    (f₀ : m • x₀ = x₀) (f₁ : m • x₁ = x₁) (f₂ : m • x₂ = x₂) (f₃ : m • x₃ = x₃)
    (f₄ : m • x₄ = x₄) (f₅ : m • x₅ = x₅) : ∀ w : W, m • w = w := by
  refine h5 ⟨fun i => match i with
    | 0 => x₀ | 1 => x₁ | 2 => x₂ | 3 => x₃ | 4 => x₄ | _ => x₅, ?_, ?_⟩ m ?_
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    all_goals assumption
  · intro i hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals assumption
  · intro i hi
    obtain rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
    all_goals assumption

end Aux

theorem fixes_nbrs_of_fixes_two_stars {W : Type*} {Γ : SimpleGraph W}
    (hdeg : ∀ w, Nat.card (Γ.neighborSet w) = 3)
    {A : Type*} [Group A] [MulAction A W]
    (hadj : ∀ (a : A) (u v : W), Γ.Adj (a • u) (a • v) ↔ Γ.Adj u v)
    (harc : ∀ u v u' v' : W, Γ.Adj u v → Γ.Adj u' v' → ∃ a : A, a • u = u' ∧ a • v = v')
    (h5 : ∀ (P : Arc Γ 5) (a : A), (∀ i, i ≤ 5 → a • P.vert i = P.vert i) → ∀ w : W, a • w = w)
    {v w₁ w₂ w₃ : W} (h₁ : Γ.Adj v w₁) (h₂ : Γ.Adj v w₂) (h₃ : Γ.Adj v w₃)
    (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃) (h₂₃ : w₂ ≠ w₃) {n : A}
    (hv : ∀ x, Γ.Adj v x → n • x = x)
    (hw₂ : ∀ x, Γ.Adj w₂ x → n • x = x) (hw₃ : ∀ x, Γ.Adj w₃ x → n • x = x) :
    ∀ x, Γ.Adj w₁ x → n • x = x := by
  have nv : n • v = v := hw₂ v h₂.symm
  have nw₁ : n • w₁ = w₁ := hv w₁ h₁
  have nw₂ : n • w₂ = w₂ := hv w₂ h₂
  have nw₃ : n • w₃ = w₃ := hv w₃ h₃
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc, hnc⟩ := hcon
  have hcv : c ≠ v := fun h => hnc (by rw [h]; exact nv)
  obtain ⟨a, a', haa', ha, hav, ha', ha'v, -⟩ := two_others (hdeg w₁) h₁.symm
  have hna : n • a = a' :=
    swap_of_moves hadj (hdeg w₁) h₁.symm nw₁ nv hc hcv hnc ha hav ha' ha'v haa'
  have hna' : n • a' = a :=
    swap_of_moves hadj (hdeg w₁) h₁.symm nw₁ nv hc hcv hnc ha' ha'v ha hav haa'.symm
  have hnt : ¬ ∀ w : W, n • w = w := fun h =>
    haa' (by have h' := h a; rw [hna] at h'; exact h'.symm)
  have step1 : ∀ x, Γ.Adj w₂ x → x ≠ v → ∀ z, Γ.Adj x z → z ≠ w₂ → n • z ≠ z := by
    intro x hx hxv z hz hzw hfix
    obtain ⟨y, _, -, hy, hyv, -⟩ := two_others (hdeg w₃) h₃.symm
    exact hnt (triv_of_fix h5 hz.symm hx.symm h₂.symm h₃ hy hzw hxv h₂₃ (Ne.symm hyv) hfix
      (hw₂ x hx) nw₂ nv nw₃ (hw₃ y hy))
  obtain ⟨x, x', -, hx, hxv, hx', hx'v, hallx⟩ := two_others (hdeg w₂) h₂.symm
  obtain ⟨g, hgv, hgw₁⟩ := harc v w₁ w₂ x h₁ hx
  have hgw : ∀ w, Γ.Adj v w → w ≠ w₁ → g • w = v ∨ g • w = x' := by
    intro w hw hww₁
    have a1 : Γ.Adj w₂ (g • w) := by
      have := (hadj g v w).2 hw
      rwa [hgv] at this
    have hne : g • w ≠ x := fun h => hww₁ (smul_left_cancel g (h.trans hgw₁.symm))
    by_cases hvw : g • w = v
    · exact Or.inl hvw
    · rcases hallx _ a1 hvw with h | h
      · exact absurd h hne
      · exact Or.inr h
  have hgw₂ := hgw w₂ h₂ (Ne.symm h₁₂)
  have hgw₃ := hgw w₃ h₃ (Ne.symm h₁₃)
  have hgne : g • w₂ ≠ g • w₃ := fun h => h₂₃ (smul_left_cancel g h)
  obtain ⟨n', hn'c, hn'f⟩ := exists_conj hadj n g
  have f₂ : ∀ y, Γ.Adj w₂ y → n' • y = y := by
    have := hn'f v hv
    rwa [hgv] at this
  have f₀ : (∀ y, Γ.Adj v y → n' • y = y) ∧ ∀ y, Γ.Adj x' y → n' • y = y := by
    have e2 := hn'f w₂ hw₂
    have e3 := hn'f w₃ hw₃
    rcases hgw₂ with h2 | h2 <;> rcases hgw₃ with h3 | h3
    · exact absurd (h2.trans h3.symm) hgne
    · rw [h2] at e2
      rw [h3] at e3
      exact ⟨e2, e3⟩
    · rw [h2] at e2
      rw [h3] at e3
      exact ⟨e3, e2⟩
    · exact absurd (h2.trans h3.symm) hgne
  obtain ⟨fv, fx'⟩ := f₀
  have n'v : n' • v = v := f₂ v h₂.symm
  have n'w₁ : n' • w₁ = w₁ := fv w₁ h₁
  have n'w₂ : n' • w₂ = w₂ := fv w₂ h₂
  have n'x : n' • x = x := f₂ x hx
  have n'x' : n' • x' = x' := f₂ x' hx'
  have hga : Γ.Adj x (g • a) := by
    have := (hadj g w₁ a).2 ha
    rwa [hgw₁] at this
  have hgaw : g • a ≠ w₂ := fun h => hav (smul_left_cancel g (h.trans hgv.symm))
  have hn'ga : n' • g • a = g • a' := by rw [hn'c, hna]
  have hmov : n' • g • a ≠ g • a := fun h =>
    haa' (smul_left_cancel g (h.symm.trans hn'ga))
  have hnt' : ¬ ∀ w : W, n' • w = w := fun h => hmov (h _)
  obtain ⟨z', _, -, hz', hz'w, -⟩ := two_others (hdeg x') hx'.symm
  have hn'a_ne : n' • a ≠ a := fun hfix =>
    hnt' (triv_of_fix h5 ha.symm h₁.symm h₂ hx' hz' hav h₁₂ (Ne.symm hx'v) (Ne.symm hz'w)
      hfix n'w₁ n'v n'w₂ n'x' (fx' z' hz'))
  have hn'a : n' • a = a' :=
    swap_of_moves hadj (hdeg w₁) h₁.symm n'w₁ n'v ha hav hn'a_ne ha hav ha' ha'v haa'
  obtain ⟨z, z₂, hzz, hz, hzw, hz₂, hz₂w, -⟩ := two_others (hdeg x) hx.symm
  have hnz : n • z₂ = z :=
    swap_of_moves hadj (hdeg x) hx.symm (hw₂ x hx) nw₂ hz hzw (step1 x hx hxv z hz hzw)
      hz₂ hz₂w hz hzw hzz.symm
  have hn'z : n' • z = z₂ :=
    swap_of_moves hadj (hdeg x) hx.symm n'x n'w₂ hga hgaw hmov hz hzw hz₂ hz₂w hzz
  have hm : ∀ w : W, (n * n') • w = w :=
    triv_of_fix h5 ha.symm h₁.symm h₂ hx hz hav h₁₂ (Ne.symm hxv) (Ne.symm hzw)
      (by rw [mul_smul, hn'a, hna']) (by rw [mul_smul, n'w₁, nw₁]) (by rw [mul_smul, n'v, nv])
      (by rw [mul_smul, n'w₂, nw₂]) (by rw [mul_smul, n'x, hw₂ x hx])
      (by rw [mul_smul, hn'z, hnz])
  obtain ⟨u, _, -, hu, huw, -⟩ := two_others (hdeg x') hx'.symm
  have hmu := hm u
  rw [mul_smul, fx' u hu] at hmu
  exact step1 x' hx' hx'v u hu huw hmu

end CFSG.Quasithin.Fan86.Tutte

end
