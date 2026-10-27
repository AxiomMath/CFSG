module

public import Certificates.Kernel.S1277.C7215Facts

public section

namespace Certificates

open CFSG.Quasithin.H13.S127.Mod in
theorem certificate7215 :
    (∀ B ∈ gm6, (∀ D ∈ gm6, B.comp D = D.comp B) → B ∈ zs6) ∧
    (∀ g ∈ gm6, presv p1c g = true → ∀ r ∈ r1, (g.comp r).comp (inv6 g) ∈ r1) ∧
    (∀ u ∈ gm6, presv p1c u = true → two6 u = true → u ∉ r1 →
      ∃ g ∈ gm6, presv p1c g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false) ∧
    (∀ g ∈ gm6, presv l2c g = true → ∀ r ∈ r2, (g.comp r).comp (inv6 g) ∈ r2) ∧
    (∀ u ∈ gm6, presv l2c u = true → two6 u = true → u ∉ r2 →
      ∃ g ∈ gm6, presv l2c g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false) ∧
    (∀ p ∈ l2c, ∃ r ∈ r2, ∃ c ∈ List.range 64, ∃ r' ∈ r2, ∃ c' ∈ List.range 64,
      p = (c ^^^ r.app c) ^^^ (c' ^^^ r'.app c')) ∧
    (∀ p ∈ l2c, ∃ s ∈ s0, ∃ c ∈ List.range 64, c ^^^ s.app c = p) ∧
    (∀ c ∈ List.range 64, c ∉ p1c →
      spanHas (p1c ++ (gm6.filter (presv p1c)).map (·.app c)) (List.range 64) = true) ∧
    (∀ c ∈ p1c, c ≠ 0 → spanHas ((gm6.filter (presv p1c)).map (·.app c)) p1c = true) ∧
    (∀ g ∈ gmList, ∃ s ∈ s0m, ∃ s' ∈ s0m, (s.mul g).mul s' ∈ dreps ∧
      presv p1c ((s.mul g).mul s').toB6 = presv p1c g.toB6 ∧
      presv l2c ((s.mul g).mul s').toB6 = presv l2c g.toB6) ∧
    (∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = false →
      genAll (s0m ++ [r]) = true) ∧
    (∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = true →
      ∀ r' ∈ dreps, presv p1c r'.toB6 = true → presv l2c r'.toB6 = false →
        genAll (s0m ++ [r, r']) = true) ∧
    (∀ y ∈ gm6, presv p1c y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ l1 ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false) ∧
    (∀ u ∈ gm6, presv p1c u = true → two6 u = true → u ∉ l1 → ∀ y ∈ l1, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false) ∧
    (∀ g ∈ gm6, fixP1 g = true → g.pow 15 = B6.id → g ∈ l1) ∧
    (∀ y ∈ gm6, presv l2c y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ l2 ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false) ∧
    (∀ u ∈ gm6, presv l2c u = true → two6 u = true → u ∉ l2 → ∀ y ∈ l2, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false) ∧
    (∀ g ∈ gm6, onQuot g = true → g.pow 15 = B6.id → g ∈ l2) ∧
    (∀ g ∈ gm6, presv p1c g = true → g.pow 15 = B6.id → ∃ a ∈ l1, ∃ z ∈ zs6, g = a.comp z) ∧
    (∀ g ∈ gm6, presv p1c g = true → ∃ a ∈ l1, ∃ z ∈ zs6, g.comp g = a.comp z) ∧
    (∀ g ∈ gm6, presv l2c g = true → g.pow 15 = B6.id → ∃ a ∈ l2, ∃ z ∈ zs6, g = a.comp z) ∧
    (∀ g ∈ gm6, presv l2c g = true → ∃ a ∈ l2, ∃ z ∈ zs6, g.comp g = a.comp z) ∧
    (∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL →
      ∀ g ∈ gm6, g.pow 5 = B6.id → g ≠ B6.id → g.app c ≠ c) ∧
    (∀ c ∈ oVecL, ∃ g ∈ gm6, g.pow 5 = B6.id ∧ g ≠ B6.id ∧ g.app c = c) ∧
    (∀ B ∈ nm6, (∀ p ∈ oPts, pn (B.app p) = p) → B ∈ zs6) := CFSG.KP.C7215.cert

end Certificates

end
