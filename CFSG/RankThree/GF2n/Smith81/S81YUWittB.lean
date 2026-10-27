module

public import CFSG.RankThree.GF2n.Smith81.S81U6Basic
public import CFSG.RankThree.GF2n.Smith81.S81YGenDef

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.RootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F}

theorem exists_ti_triple_ext (hσ : IsUnitaryInvolution σ) {X a Y b : Fin 6 → F}
    (hli : LinearIndependent F ![X, a, Y])
    (hiso : ∀ i j, herm σ (![X, a, Y] i) (![X, a, Y] j) = 0)
    (hab : herm σ a b = 0) (hbb : herm σ b b = 0) (hb : herm σ X b ≠ 0 ∨ herm σ Y b ≠ 0) :
    ∃ c' : Fin 6 → F, c' ∈ Submodule.span F {X, Y} ∧ herm σ b c' = 0 ∧
      LinearIndependent F ![c', a, b] ∧
      ∀ i j, herm σ (![c', a, b] i) (![c', a, b] j) = 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hXX : herm σ X X = 0 := hiso 0 0
  have hXa : herm σ X a = 0 := hiso 0 1
  have hXY : herm σ X Y = 0 := hiso 0 2
  have haX : herm σ a X = 0 := hiso 1 0
  have haa : herm σ a a = 0 := hiso 1 1
  have haY : herm σ a Y = 0 := hiso 1 2
  have hYX : herm σ Y X = 0 := hiso 2 0
  have hYa : herm σ Y a = 0 := hiso 2 1
  have hYY : herm σ Y Y = 0 := hiso 2 2
  obtain ⟨s, hs⟩ : ∃ s : F, s = σ (herm σ Y b) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : F, t = σ (herm σ X b) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : Fin 6 → F, c' = s • X + t • Y := ⟨_, rfl⟩
  have hst : s ≠ 0 ∨ t ≠ 0 := by
    rcases hb with hb | hb
    · right
      rw [ht]
      exact (map_ne_zero σ).mpr hb
    · left
      rw [hs]
      exact (map_ne_zero σ).mpr hb
  have hbX : herm σ b X = t := by
    rw [herm_conj σ hσ.invol X b, ht]
  have hbY : herm σ b Y = s := by
    rw [herm_conj σ hσ.invol Y b, hs]
  have hc'mem : c' ∈ Submodule.span F {X, Y} := by
    rw [hc']
    exact Submodule.mem_span_pair.mpr ⟨s, t, rfl⟩
  have hbc : herm σ b c' = 0 := by
    rw [hc', herm_add_right, herm_smul_right, herm_smul_right, hbX, hbY]
    linear_combination (s * t) * h2
  have hcX : herm σ c' X = 0 := by
    simp [hc', herm_add_left, herm_smul_left, hXX, hYX]
  have hcY : herm σ c' Y = 0 := by
    simp [hc', herm_add_left, herm_smul_left, hXY, hYY]
  have hXc : herm σ X c' = 0 := by
    rw [herm_conj σ hσ.invol c' X, hcX, map_zero]
  have hYc : herm σ Y c' = 0 := by
    rw [herm_conj σ hσ.invol c' Y, hcY, map_zero]
  have hca : herm σ c' a = 0 := by
    simp [hc', herm_add_left, herm_smul_left, hXa, hYa]
  have hac : herm σ a c' = 0 := by
    simp [hc', herm_add_right, herm_smul_right, haX, haY]
  have hcc : herm σ c' c' = 0 := by
    have e : herm σ c' c' = herm σ c' (s • X + t • Y) := by rw [← hc']
    rw [e]
    simp [herm_add_right, herm_smul_right, hcX, hcY]
  have hcb : herm σ c' b = 0 := by
    rw [herm_conj σ hσ.invol b c', hbc, map_zero]
  have hba : herm σ b a = 0 := by
    rw [herm_conj σ hσ.invol a b, hab, map_zero]
  refine ⟨c', hc'mem, hbc, ?_, ?_⟩
  ·
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • c' + g 1 • a + g 2 • b = 0 := by
      rw [Fin.sum_univ_three] at hg
      exact hg
    have e1 : g 2 * herm σ X b = 0 := by
      have := congrArg (herm σ X) hg'
      simpa [herm_add_right, herm_smul_right, hXc, hXa] using this
    have e2 : g 2 * herm σ Y b = 0 := by
      have := congrArg (herm σ Y) hg'
      simpa [herm_add_right, herm_smul_right, hYc, hYa] using this
    have hg2 : g 2 = 0 := by
      rcases hb with hb | hb
      · exact (mul_eq_zero.mp e1).resolve_right hb
      · exact (mul_eq_zero.mp e2).resolve_right hb
    have hg'' : g 0 • c' + g 1 • a = 0 := by
      rw [hg2, zero_smul, add_zero] at hg'
      exact hg'
    have hsum : ∑ i, ![g 0 * s, g 1, g 0 * t] i • ![X, a, Y] i = 0 := by
      rw [Fin.sum_univ_three]
      show (g 0 * s) • X + g 1 • a + (g 0 * t) • Y = 0
      rw [hc'] at hg''
      linear_combination (norm := module) hg''
    have hcoef := Fintype.linearIndependent_iff.mp hli ![g 0 * s, g 1, g 0 * t] hsum
    have h0 : g 0 * s = 0 := hcoef 0
    have h1 : g 1 = 0 := hcoef 1
    have h0' : g 0 * t = 0 := hcoef 2
    have hg0 : g 0 = 0 := by
      rcases hst with hs0 | ht0
      · exact (mul_eq_zero.mp h0).resolve_right hs0
      · exact (mul_eq_zero.mp h0').resolve_right ht0
    intro i
    fin_cases i <;> simp [hg0, h1, hg2]
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [hcc, hca, hcb, hac, haa, hab, hba, hbb, hbc]

end CFSG.RankThree.GF2n.Smith81.RootGenU
