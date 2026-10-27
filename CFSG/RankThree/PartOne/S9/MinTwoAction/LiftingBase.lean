module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.Lifting36

open CFSG
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inSubgroup_frattini_le {p : ℕ} (hp : p.Prime) {R K : Subgroup G} (hR : IsPGroup p R)
    (hcomm : ⁅R, R⁆ ≤ K) (hpow : ∀ r ∈ R, r ^ p ∈ K) : inSubgroup frattini R ≤ K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p R) := ⟨hR⟩
  have h : frattini R ≤ K.comap R.subtype := by
    rw [frattini_eq_closure_commutator_union_powers (p := p), Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · have hx' : R.subtype x ∈ ⁅R, R⁆ := by
        have : R.subtype x ∈ (commutator R).map R.subtype := Subgroup.mem_map_of_mem _ hx
        rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at this
      exact hcomm hx'
    · exact hpow y y.2
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact h hy

theorem inSubgroup_frattini_eq_bot {q : ℕ} (hq : q.Prime) {D : Subgroup G}
    (hD : IsElementaryAbelian q D) : inSubgroup frattini D = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact (IsPGroup q D) := ⟨IsElementaryAbelian.isPGroup q D⟩
  rw [inSubgroup, frattini_eq_bot_of_isElementaryAbelian (R := D) (p := q), Subgroup.map_bot]

end CFSG.RankThree.PartOne.Lifting36
