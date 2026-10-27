module

public import CFSG.RankThree.PartOne.N1322.CaseBasic
public import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.RepresentationTheory

theorem central_of_center {p : ℕ} [Fact p.Prime] {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    {a : GL (Fin 3) (ZMod p)} (hc : ∀ x ∈ H, x * a = a * x) (g : GL (Fin 3) (ZMod p)) :
    g * a = a * g := by
  obtain ⟨c, hc'⟩ := hsch (a : Matrix (Fin 3) (Fin 3) (ZMod p)) (fun x hx => by
    rw [← Units.val_mul, ← Units.val_mul, hc x hx])
  exact central_of_scalar hc' g

theorem lm_central_eq_one {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hsch : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c)
    {l : GL (Fin 3) (ZMod p)} (hl : l ∈ d.Lm) (hlH : ∀ x ∈ H, x * l = l * x) : l = 1 := by
  obtain ⟨c, hc⟩ := hsch (l : Matrix (Fin 3) (Fin 3) (ZMod p)) (fun x hx => by
    rw [← Units.val_mul, ← Units.val_mul, hlH x hx])
  have hfix := h.c_fix l hl
  rw [hc] at hfix
  have hc1 : c = 1 := by
    obtain ⟨i, hi⟩ : ∃ i, d.c i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h.c_ne (funext hcon)
    have h1 := congrFun hfix i
    have h2 : c * d.c i = 1 * d.c i := by
      simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal] using h1
    exact mul_right_cancel₀ hi h2
  apply Units.ext
  exact (hc.trans (by rw [hc1, map_one])).trans Units.val_one.symm

end CFSG.RankThree.PartOne.N1322
