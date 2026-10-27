module

public import CFSG.Quasithin.Background.P3OrthoA8Quad

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Matrix

namespace CFSG.Quasithin

namespace G11

namespace P3Ortho

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {H' : Subgroup (GLV U)}

namespace Data

variable (D : Data U H')

theorem q_comp_eq (γ : GLV U) (hγB : ∀ v w, D.B0 (γ v) (γ w) = D.B0 v w)
    (hγH : ∀ h ∈ H', γ * h * γ⁻¹ ∈ H') (u : U) : D.q (γ u) = D.q u := by
  have h2 : ∀ t : ZMod 2, t + t = 0 := by decide
  let d : U → ZMod 2 := fun v => D.q (γ v) + D.q v
  have hd_add : ∀ v w, d (v + w) = d v + d w := by
    intro v w
    simp only [d, map_add, D.q_add, hγB]
    linear_combination h2 (D.B0 v w)
  have hd_H : ∀ h : ↥H', ∀ v, d ((h : GLV U) v) = d v := by
    intro h v
    have hmem : γ * (h : GLV U) * γ⁻¹ ∈ H' := hγH h h.2
    have e : γ ((h : GLV U) v) = ((⟨γ * (h : GLV U) * γ⁻¹, hmem⟩ : ↥H') : GLV U) (γ v) := by
      simp
    simp only [d]
    rw [e, D.q_inv, D.q_inv]
  have hd_zero : d 0 = 0 := by
    simp only [d, map_zero, D.q_zero]
    exact h2 0
  have hf_inv : ∀ σ ∈ alternatingGroup (Fin 8), ∀ i j, d (D.w (σ i) (σ j)) = d (D.w i j) := by
    intro σ hσ i j
    obtain ⟨h, hh⟩ := D.w_inv σ hσ
    rw [← hh i j]
    exact hd_H h _
  have hf_const : ∀ i j i' j' : Fin 8, i ≠ j → i' ≠ j' → d (D.w i j) = d (D.w i' j') := by
    intro i j i' j' hij hij'
    obtain ⟨σ, hσ, h1, h2⟩ := exists_alt_two hij hij'
    rw [← h1, ← h2]
    exact (hf_inv σ hσ i j).symm
  have hc0 : d (D.w 0 1) = 0 := by
    have e1 : D.w 0 1 + D.w 1 2 = D.w 0 2 := D.w_add 0 1 2
    have h3 := hd_add (D.w 0 1) (D.w 1 2)
    rw [e1, hf_const 0 2 0 1 (by decide) (by decide),
      hf_const 1 2 0 1 (by decide) (by decide)] at h3
    linear_combination h3 + h2 (d (D.w 0 1))
  let dl : U →ₗ[ZMod 2] ZMod 2 := (AddMonoidHom.mk' d hd_add).toZModLinearMap 2
  have hdl : dl = 0 := by
    apply LinearMap.ext_on D.span_w
    rintro x ⟨a, rfl⟩
    show d (D.w 0 a) = 0
    by_cases ha : a = 0
    · subst ha
      rw [D.w_self]
      exact hd_zero
    · rw [hf_const 0 a 0 1 (Ne.symm ha) (by decide)]
      exact hc0
  have hdu : d u = 0 := LinearMap.congr_fun hdl u
  have hdu' : D.q (γ u) + D.q u = 0 := hdu
  linear_combination hdu' - h2 (D.q u)

theorem v3_mem (i : Fin 3) : v3 i ∈ permCore 8 := by
  show ∑ j, v3 i j = 0
  revert i
  decide

@[expose] def V3 (i : Fin 3) : ↥(permCore 8) := ⟨v3 i, v3_mem i⟩

@[expose] noncomputable def bs (i : Fin 3) : U := D.β (V3 i)

theorem sum_bs (c : Fin 3 → ZMod 2) :
    ∑ i, c i • D.bs i = D.β (∑ i, c i • V3 i) := by
  simp [bs, map_sum, map_smul]

theorem coe_sum_V3 (c : Fin 3 → ZMod 2) :
    (((∑ i, c i • V3 i : ↥(permCore 8))) : Fin 8 → ZMod 2) =
      c 0 • v3 0 + c 1 • v3 1 + c 2 • v3 2 := by
  simp [Fin.sum_univ_three, V3]

theorem linearIndependent_bs : LinearIndependent (ZMod 2) D.bs := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [sum_bs] at hg
  have hk := (D.ker _).1 hg
  have hall : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
    have hc := (v3_combo (g 0) (g 1) (g 2)).2.2
    rcases hk with h0 | ⟨-, h1⟩
    · apply hc
      left
      have := congrArg (fun z : ↥(permCore 8) => (z : Fin 8 → ZMod 2)) h0
      rw [coe_sum_V3] at this
      exact this
    · apply hc
      right
      have := funext h1
      rw [coe_sum_V3] at this
      exact this
  fin_cases i
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2

@[expose] noncomputable def sing3 : Submodule (ZMod 2) U :=
  Submodule.span (ZMod 2) (Set.range D.bs)

theorem finrank_sing3 : Module.finrank (ZMod 2) ↥D.sing3 = 3 := by
  rw [sing3, finrank_span_eq_card D.linearIndependent_bs]
  simp

theorem sing3_q : ∀ s ∈ D.sing3, D.q s = 0 := by
  intro s hs
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hs
  rw [sum_bs, q_β]
  have h := (v3_combo (c 0) (c 1) (c 2)).2.1
  rw [← coe_sum_V3] at h
  exact h

end Data

end P3Ortho

end G11

end CFSG.Quasithin
