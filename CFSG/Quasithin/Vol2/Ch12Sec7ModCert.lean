module

public import Certificates.Certificate7215

public section

namespace CFSG.Quasithin.H13.S127.Mod

theorem cert_center :
    ∀ B ∈ gm6, (∀ D ∈ gm6, B.comp D = D.comp B) → B ∈ zs6 :=
  Certificates.certificate7215.1

theorem cert_n1 :
    ∀ g ∈ gm6, presv p1c g = true → ∀ r ∈ r1, (g.comp r).comp (inv6 g) ∈ r1 :=
  Certificates.certificate7215.2.1

theorem cert_m1 :
    ∀ u ∈ gm6, presv p1c u = true → two6 u = true → u ∉ r1 →
      ∃ g ∈ gm6, presv p1c g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false :=
  Certificates.certificate7215.2.2.1

theorem cert_n2 :
    ∀ g ∈ gm6, presv l2c g = true → ∀ r ∈ r2, (g.comp r).comp (inv6 g) ∈ r2 :=
  Certificates.certificate7215.2.2.2.1

theorem cert_m2 :
    ∀ u ∈ gm6, presv l2c u = true → two6 u = true → u ∉ r2 →
      ∃ g ∈ gm6, presv l2c g = true ∧ two6 (u.comp ((g.comp u).comp (inv6 g))) = false :=
  Certificates.certificate7215.2.2.2.2.1

theorem cert_r2span :
    ∀ p ∈ l2c, ∃ r ∈ r2, ∃ c ∈ List.range 64, ∃ r' ∈ r2, ∃ c' ∈ List.range 64,
      p = (c ^^^ r.app c) ^^^ (c' ^^^ r'.app c') :=
  Certificates.certificate7215.2.2.2.2.2.1

theorem cert_s0span :
    ∀ p ∈ l2c, ∃ s ∈ s0, ∃ c ∈ List.range 64, c ^^^ s.app c = p :=
  Certificates.certificate7215.2.2.2.2.2.2.1

theorem cert_irr1 :
    ∀ c ∈ List.range 64, c ∉ p1c →
      spanHas (p1c ++ (gm6.filter (presv p1c)).map (·.app c)) (List.range 64) = true :=
  Certificates.certificate7215.2.2.2.2.2.2.2.1

theorem cert_irr2 :
    ∀ c ∈ p1c, c ≠ 0 → spanHas ((gm6.filter (presv p1c)).map (·.app c)) p1c = true :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.1

theorem cert_dcov :
    ∀ g ∈ gmList, ∃ s ∈ s0m, ∃ s' ∈ s0m, (s.mul g).mul s' ∈ dreps ∧
      presv p1c ((s.mul g).mul s').toB6 = presv p1c g.toB6 ∧
      presv l2c ((s.mul g).mul s').toB6 = presv l2c g.toB6 :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.1

theorem cert_gen1 :
    ∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = false →
      genAll (s0m ++ [r]) = true :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.1

theorem cert_gen2 :
    ∀ r ∈ dreps, presv p1c r.toB6 = false → presv l2c r.toB6 = true →
      ∀ r' ∈ dreps, presv p1c r'.toB6 = true → presv l2c r'.toB6 = false →
        genAll (s0m ++ [r, r']) = true :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_ord3a :
    ∀ y ∈ gm6, presv p1c y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ l1 ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_beta1 :
    ∀ u ∈ gm6, presv p1c u = true → two6 u = true → u ∉ l1 → ∀ y ∈ l1, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_odd1 :
    ∀ g ∈ gm6, fixP1 g = true → g.pow 15 = B6.id → g ∈ l1 :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_ord3b :
    ∀ y ∈ gm6, presv l2c y = true → ord3 y = true → y ∈ zs6 ∨ y ∈ l2 ∨
      ∃ s ∈ s0, two6 (y.comp (inv6 ((s.comp y).comp (inv6 s)))) = false ∧
        two6 (y.comp ((s.comp y).comp (inv6 s))) = false :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_beta2 :
    ∀ u ∈ gm6, presv l2c u = true → two6 u = true → u ∉ l2 → ∀ y ∈ l2, ord3 y = true →
      two6 (u.comp ((y.comp u).comp (inv6 y))) = false ∨
        two6 (u.comp (((inv6 y).comp u).comp y)) = false :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_odd2 :
    ∀ g ∈ gm6, onQuot g = true → g.pow 15 = B6.id → g ∈ l2 :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_ost1 :
    ∀ g ∈ gm6, presv p1c g = true → g.pow 15 = B6.id → ∃ a ∈ l1, ∃ z ∈ zs6, g = a.comp z :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_sq1 :
    ∀ g ∈ gm6, presv p1c g = true → ∃ a ∈ l1, ∃ z ∈ zs6, g.comp g = a.comp z :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_ost2 :
    ∀ g ∈ gm6, presv l2c g = true → g.pow 15 = B6.id → ∃ a ∈ l2, ∃ z ∈ zs6, g = a.comp z :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_sq2 :
    ∀ g ∈ gm6, presv l2c g = true → ∃ a ∈ l2, ∃ z ∈ zs6, g.comp g = a.comp z :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_fix5a :
    ∀ c ∈ List.range 64, c ≠ 0 → c ∉ oVecL →
      ∀ g ∈ gm6, g.pow 5 = B6.id → g ≠ B6.id → g.app c ≠ c :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_fix5b :
    ∀ c ∈ oVecL, ∃ g ∈ gm6, g.pow 5 = B6.id ∧ g ≠ B6.id ∧ g.app c = c :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cert_ker6 :
    ∀ B ∈ nm6, (∀ p ∈ oPts, pn (B.app p) = p) → B ∈ zs6 :=
  Certificates.certificate7215.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Quasithin.H13.S127.Mod

end
