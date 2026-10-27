module

public import Certificates.Kernel.S1277.C7214Facts

public section

namespace Certificates

open CFSG.Quasithin.H13.S127.Mod in
theorem certificate7214 :
    (∀ c ∈ oVecL, ∃ g ∈ gm6, g.app c = 1) ∧
    (∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL → ∀ d ∈ p1c, d ≠ 0 → ∃ g ∈ gm6, g.app c = d) ∧
    ((gm6.filter (presv pt1)).length = 180) ∧
    (stab1.length = 60) ∧
    (∀ g ∈ gm6, presv pt1 g = true → blkC g = [1, 0, 0, 1] → g = B6.id) ∧
    (∀ g ∈ stab1, det2 g = 1) ∧
    (∀ c ∈ List.range 64, c ∉ pt1 →
      spanHas (pt1 ++ stab1.map (·.app c)) (List.range 64) = true) ∧
    (spanHas (stab1.flatMap fun g => (List.range 64).map fun c => c ^^^ g.app c)
      (List.range 64) = true) ∧
    (∀ g ∈ stab1, ∃ a ∈ stab1, ∃ b ∈ stab1, a.pow 3 = B6.id ∧ b.pow 3 = B6.id ∧
      g = a.comp b) ∧
    (∀ g ∈ stab1, ∃ a ∈ stab1, ∃ b ∈ stab1, g = ((a.comp b).comp (inv6 a)).comp (inv6 b)) ∧
    (∀ B ∈ nm6, B.comp B = B6.id → B ≠ B6.id → fixCount B ≤ 16) ∧
    (∀ B ∈ nm6, B.pow 15 = B6.id → B ≠ B6.id → fixCount B < 8) ∧
    (∀ B ∈ nm6, B.comp B = B6.id → B ≠ B6.id → 16 ≤ fixCount B →
      ∃ c ∈ oVecL, B.app c = c) ∧
    (∀ B ∈ gm6, B.comp B = B6.id → B ≠ B6.id →
      ∃ g ∈ gm6, ∀ c ∈ List.range 64, (B.app c = c ↔ g.app c ∈ l2c)) ∧
    (∀ B ∈ nm6, 8 ≤ (l2c.filter fun c => B.app c == c).length → B ∈ r2) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → ∀ B ∈ nm6,
      (∀ c ∈ List.range 64, y.app c = c → B.app c = c) → B = B6.id ∨ B = y) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → fixCount y = 8) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id → ∀ p ∈ oPts, presv (ptOf p) y = true →
      ∃ c ∈ oVecL, y.app c = c) ∧
    (∀ τ ∈ nm6, τ ∉ gm6 → (∀ s ∈ s0, ∃ s' ∈ s0, τ.comp s = s'.comp τ) → two6 τ = true →
      ∃ k ∈ zs6, ∃ u ∈ s0p, k.comp τ = u.comp k) ∧
    (∀ x ∈ l1s0p, ∀ y ∈ l1s0p, x.comp y ∈ l1s0p) ∧
    (∀ x ∈ l2s0p, ∀ y ∈ l2s0p, x.comp y ∈ l2s0p) ∧
    (∀ B ∈ l1s0p, (∀ D ∈ l1 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i1) ∧
    (∀ B ∈ l2s0p, (∀ D ∈ l2 ++ s0p, B.comp D = D.comp B) → B = B6.id ∨ B = i2) ∧
    (∀ y ∈ nm6, y ∉ gm6 → y.comp y = B6.id →
      ∃ m ∈ nm6, y.comp m = m.comp i1 ∨ y.comp m = m.comp i2) ∧
    (∀ m ∈ nm6, i2.comp m ≠ m.comp i1) ∧
    (i1 ∈ nm6 ∧ i1 ∉ gm6 ∧ i2 ∈ nm6 ∧ i2 ∉ gm6) ∧
    (i1 ∈ l1s0p ∧ i2 ∈ l2s0p) ∧
    (∀ B ∈ nm6, B.pow 60 = B6.id) := CFSG.KP.C7214.cert

end Certificates

end
