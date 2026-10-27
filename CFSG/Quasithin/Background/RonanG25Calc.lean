module

public import CFSG.Quasithin.Background.RonanG25Defs

public section

namespace CFSG.Quasithin.RonanG25

section Calc

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G} {ord : Bool}

theorem ChainCounts.trans {A B C : Subgroup G} {a b a' b' : ℕ}
    (h : ChainCounts F X ord A B a b) (h' : ChainCounts F X ord B C a' b') :
    ChainCounts F X ord A C (a + a') (b + b') := by
  revert h'
  induction h with
  | refl A hA =>
    intro h'
    simpa using h'
  | natural hs hn rest ih =>
    intro h'
    rw [Nat.add_right_comm]
    exact ChainCounts.natural hs hn (ih h')
  | additional hs habel hc hcard rest ih =>
    intro h'
    rw [Nat.add_right_comm]
    exact ChainCounts.additional hs habel hc hcard (ih h')
  | central hs hc hp hcard rest ih =>
    intro h'
    exact ChainCounts.central hs hc hp hcard (ih h')
  | other hord hs h2 rest ih =>
    intro h'
    exact ChainCounts.other hord hs h2 (ih h')

theorem ChainCounts.toOrd {A C : Subgroup G} {a b : ℕ} (h : ChainCounts F X false A C a b) :
    ChainCounts F X true A C a b := by
  induction h with
  | refl A hA => exact ChainCounts.refl A hA
  | natural hs hn rest ih => exact ChainCounts.natural hs hn ih
  | additional hs habel hc hcard rest ih => exact ChainCounts.additional hs habel hc hcard ih
  | central hs hc hp hcard rest ih => exact ChainCounts.central hs hc hp hcard ih
  | other hord hs h2 rest ih => exact absurd hord (by decide)

end Calc

end CFSG.Quasithin.RonanG25
