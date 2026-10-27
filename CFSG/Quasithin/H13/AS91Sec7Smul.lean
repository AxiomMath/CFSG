module

public import CFSG.Quasithin.H13.AS91Sec7Chain

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

namespace Loc49

variable {G : Type} [Group G] [Finite G] {z : G} (c : Loc49 G z)

theorem onL_smul_iff (g : G) {a : G ⧸ c.G1} {m : G ⧸ c.G2} :
    c.OnL (g • a) (g • m) ↔ c.OnL a m := cInc_smul c.G1 c.G2 g a m

theorem onP_smul_iff (g : G) {a : G ⧸ c.G1} {σ : G ⧸ c.G3} :
    c.OnP (g • a) (g • σ) ↔ c.OnP a σ := cInc_smul c.G1 c.G3 g a σ

theorem adj_smul_iff (g : G) {a b : G ⧸ c.G1} : c.Delta.Adj (g • a) (g • b) ↔ c.Delta.Adj a b :=
  (instGraphActionColGraph c.G1 c.G2).adj_smul g a b

theorem mem_deltaAt_smul_iff (g : G) (i : Fin 5) {a : G ⧸ c.G1} {m n : G ⧸ c.G2} :
    g • n ∈ c.deltaAt i (g • a) (g • m) ↔ n ∈ c.deltaAt i a m := by
  constructor
  · rintro ⟨h, hx, hl, hd⟩
    refine ⟨g⁻¹ * h, ?_, ?_, ?_⟩
    · rw [mul_smul, hx, inv_smul_smul]
    · rw [mul_smul, hl, inv_smul_smul]
    · rwa [mul_inv_rev, inv_inv, mul_smul]
  · rintro ⟨h, hx, hl, hd⟩
    refine ⟨g * h, ?_, ?_, ?_⟩
    · rw [mul_smul, hx]
    · rw [mul_smul, hl]
    · rwa [mul_inv_rev, mul_smul, inv_smul_smul]

theorem perp_smul_iff (g : G) {a b : G ⧸ c.G1} :
    Perp c.Delta (g • a) (g • b) ↔ Perp c.Delta a b := by
  simp only [Perp, smul_left_cancel_iff, c.adj_smul_iff]

theorem dist2_smul_iff (g : G) {a b : G ⧸ c.G1} :
    Dist2 c.Delta (g • a) (g • b) ↔ Dist2 c.Delta a b := by
  simp only [Dist2, ne_eq, smul_left_cancel_iff, c.adj_smul_iff]
  constructor
  · rintro ⟨h1, h2, w, h3, h4⟩
    refine ⟨h1, h2, g⁻¹ • w, ?_, ?_⟩
    · rw [← c.adj_smul_iff g, smul_inv_smul]
      exact h3
    · rw [← c.adj_smul_iff g, smul_inv_smul]
      exact h4
  · rintro ⟨h1, h2, w, h3, h4⟩
    exact ⟨h1, h2, g • w, (c.adj_smul_iff g).2 h3, (c.adj_smul_iff g).2 h4⟩

end Loc49

end CFSG.Quasithin.H13.AS91
