module

public import CFSG.LocalAnalysis.StandardType.GGDepAOdd
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggDepAOdd_large_false (hKG : GGReflClassLargeInput') {p N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hN : 11 ≤ N) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] {h : Fin (N - 1) → V} {α : Fin (N - 1) → Module.Dual (ZMod p) V}
    {x : V} (F : GGDepAFrame p N h α x) (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (ra : V ≃ₗ[ZMod p] V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hra : ∀ v, ra v = v - αa v • ha) (hαa : αa ha = 2)
    (hjoin : ∃ c, αa (h c) ≠ 0) (hw : αa x ≠ 0)
    (hnt : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w))
    (hcard : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N)) : False := by
  by_cases hnH : ha ∈ Submodule.span (ZMod p) (Set.range h)
  · exact ggDepAOdd_caseII_false hKG hp2 hN F r hr ra ha αa hra hαa hw hnt hcard hnH
  · exact ggDepAOdd_caseI_false hKG hp2 hN F r hr ra ha αa hra hαa hjoin hw hnt hcard hnH

end CFSG.StandardType
