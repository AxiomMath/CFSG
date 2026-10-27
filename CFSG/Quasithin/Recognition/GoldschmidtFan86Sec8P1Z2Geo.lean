module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V : Type*} {Γ : SimpleGraph V}

theorem IsTree.dist_eq_two_of_adj (hT : Γ.IsTree) {a c u : V} (hac : Γ.Adj a c)
    (hcu : Γ.Adj c u) (hua : u ≠ a) : Γ.dist a u = 2 := by
  have d1 : Γ.dist u c = 1 := dist_eq_one_iff_adj.mpr hcu.symm
  have := IsTree.dist_succ_of_ne hT (a := c) (b := u) (b' := a) (w := u) hcu hac.symm hua
    (by rw [SimpleGraph.dist_self, d1])
  rw [SimpleGraph.dist_comm] at this
  omega

theorem IsTree.dist_eq_five_of_chain (hT : Γ.IsTree) {p₀ p₁ p₂ p₃ p₄ p₅ : V}
    (h01 : Γ.Adj p₀ p₁) (h12 : Γ.Adj p₁ p₂) (h23 : Γ.Adj p₂ p₃) (h34 : Γ.Adj p₃ p₄)
    (h45 : Γ.Adj p₄ p₅) (h02 : p₀ ≠ p₂) (h13 : p₁ ≠ p₃) (h24 : p₂ ≠ p₄) (h35 : p₃ ≠ p₅) :
    Γ.dist p₀ p₅ = 5 := by
  have d1 : Γ.dist p₀ p₁ = 1 := dist_eq_one_iff_adj.mpr h01
  have d2 : Γ.dist p₀ p₂ = 2 := by
    have := IsTree.dist_succ_of_ne hT (a := p₁) (b := p₀) (b' := p₂) (w := p₀) h01.symm h12 h02
      (by rw [SimpleGraph.dist_self, d1])
    omega
  have d3 : Γ.dist p₀ p₃ = 3 := by
    have := IsTree.dist_succ_of_ne hT (a := p₂) (b := p₁) (b' := p₃) (w := p₀) h12.symm h23 h13
      (by omega)
    omega
  have d4 : Γ.dist p₀ p₄ = 4 := by
    have := IsTree.dist_succ_of_ne hT (a := p₃) (b := p₂) (b' := p₄) (w := p₀) h23.symm h34 h24
      (by omega)
    omega
  have := IsTree.dist_succ_of_ne hT (a := p₄) (b := p₃) (b' := p₅) (w := p₀) h34.symm h45 h35
    (by omega)
  omega

theorem IsTree.dist_eq_four_of_branches (hT : Γ.IsTree) {a c₁ c₂ u w : V} (h₁ : Γ.Adj a c₁)
    (h₁' : Γ.Adj c₁ u) (h₂ : Γ.Adj a c₂) (h₂' : Γ.Adj c₂ w) (hc : c₁ ≠ c₂) (hua : u ≠ a)
    (hwa : w ≠ a) : Γ.dist u w = 4 := by
  have d1 : Γ.dist u c₁ = 1 := dist_eq_one_iff_adj.mpr h₁'.symm
  have d2 : Γ.dist u a = 2 := by
    have := IsTree.dist_succ_of_ne hT (a := c₁) (b := u) (b' := a) (w := u) h₁' h₁.symm hua
      (by rw [SimpleGraph.dist_self, d1])
    omega
  have d3 : Γ.dist u c₂ = 3 := by
    have := IsTree.dist_succ_of_ne hT (a := a) (b := c₁) (b' := c₂) (w := u) h₁ h₂ hc
      (by omega)
    omega
  have := IsTree.dist_succ_of_ne hT (a := c₂) (b := a) (b' := w) (w := u) h₂.symm h₂' hwa.symm
    (by omega)
  omega

end CFSG.Quasithin.Fan86
