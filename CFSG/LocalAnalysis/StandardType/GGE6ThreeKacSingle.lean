module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRows1585
import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType.E6KacSingle

open CFSG CFSG.Assembly CFSG.StandardType

private local instance (priority := high) decEqLabel : DecidableEq LargeEvenLabel := fun a b =>
  match a, b with
  | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
    if h1 : ta = tb then
      if h2 : ra = rb then
        if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
        else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
      else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
    else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private def pairShapes : List (LargeEvenLieTag × ℕ × ℕ) :=
  [(.D, 5, 1), (.twD, 5, 1), (.A, 5, 1), (.twA, 5, 1),
    (.triD4, 0, 1), (.twD, 4, 1), (.A, 2, 3), (.twA, 2, 3)]

private theorem table_single_of_pairShape :
    ∀ tw : Bool, ∀ n : ℕ, n = 1 ∨ n = 2 →
      ∀ D ∈ ggKacTable .E6 tw 3 n, ∀ o ∈ D.orbits,
        ggKacShapeLabel n o.lab ∈ pairShapes → D.orbits.length = 1 := by
  intro tw n hn
  rcases hn with rfl | rfl
  all_goals cases tw
  all_goals decide +kernel

private theorem pair_shape_mem {tw : Bool} {n : ℕ} (hn : 1 ≤ n)
    {o : GGKacOrbit}
    (hpair : GGPairE6Three 3 ⟨(if tw then .twE6 else .E6), 0, n⟩ o.lab) :
    ggKacShapeLabel n o.lab ∈ pairShapes := by
  have hnpos : 0 < n := by omega
  rcases hpair.2.2 with h | h | h | h | h | h | h | h
  all_goals rw [h]
  all_goals simp [ggKacShapeLabel, pairShapes, Nat.div_self hnpos,
    Nat.mul_div_left _ hnpos]

private theorem table_single_of_shape {tw : Bool} {n n₀ : ℕ}
    (hn : 1 ≤ n) (hn₀ : n₀ = 1 ∨ n₀ = 2)
    (hshape : (↑((ggKacTable .E6 tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable .E6 tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n)
    {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hpair : GGPairE6Three 3 ⟨(if tw then .twE6 else .E6), 0, n⟩ o.lab) :
    D.orbits.length = 1 := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable .E6 tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD', hDshape⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have horbits : (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
      Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have h := congrArg Prod.fst hDshape
    simpa only [GGKacDatum.shape] using h.symm
  have hlength : D.orbits.length = D'.orbits.length := by
    simpa only [Multiset.coe_card, List.length_map] using congrArg Multiset.card horbits
  have hmemOrbit : ggKacShapeLabel n o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  rw [horbits] at hmemOrbit
  obtain ⟨o', ho', heq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmemOrbit)
  have hshape' : ggKacShapeLabel n₀ o'.lab ∈ pairShapes := by
    rw [heq]
    exact pair_shape_mem hn hpair
  exact hlength.trans (table_single_of_pairShape tw n₀ hn₀ D' hD' o' ho' hshape')

theorem orbits_length_eq_one_of_pair {tw : Bool} {n : ℕ}
    (hn : 1 ≤ n) (hb : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1)
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n)
    {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hpair : GGPairE6Three 3 ⟨(if tw then .twE6 else .E6), 0, n⟩ o.lab) :
    D.orbits.length = 1 := by
  rcases hb with hminus | hplus
  · exact table_single_of_shape hn (Or.inr rfl)
      (ggKacTable_shape .E6 tw Nat.prime_three hn (by decide : 1 ≤ 2)
        (Or.inl ⟨hminus, by decide⟩)) hD ho hpair
  · exact table_single_of_shape hn (Or.inl rfl)
      (ggKacTable_shape .E6 tw Nat.prime_three hn (by decide : 1 ≤ 1)
        (Or.inr ⟨hplus, by decide⟩)) hD ho hpair

end CFSG.StandardType.E6KacSingle
