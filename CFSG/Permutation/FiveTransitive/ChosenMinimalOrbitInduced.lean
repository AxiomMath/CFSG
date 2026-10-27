module

public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitChoice
public import CFSG.Permutation.FiveTransitive.FixedNormalizerImage

public section

namespace CFSG

namespace FiveTransitive.ChosenMinimalOrbitInduced

open MulAction FixedNormalizerAction FixedNormalizerImage OyamaMinimalOrbitDescent

theorem point_fixer_data
    {G X : Type*} [Group G] [MulAction G X] (A : Subgroup G)
    (x : X) (hx : x ∉ fixedPoints A X) :
    let Q := (stabilizer A x).map A.subtype
    Q < A ∧ fixedPoints A X ⊂ fixedPoints Q X ∧ Nat.card Q = Nat.card (stabilizer A x) := by
  let T := stabilizer A x
  let Q := T.map A.subtype
  have hQA : Q ≤ A := by
    intro q hq
    obtain ⟨r, _, rfl⟩ := Subgroup.mem_map.mp hq
    exact r.property
  have hproper : T ≠ ⊤ := by
    intro he
    apply hx
    intro a
    have ha : a ∈ T := by rw [he]; trivial
    exact ha
  have hlt : Q < A := by
    apply lt_of_le_of_ne hQA
    intro he
    apply hproper
    apply top_unique
    intro r _
    have hr : (r : G) ∈ Q := by rw [he]; exact r.property
    obtain ⟨u, hu, hur⟩ := Subgroup.mem_map.mp hr
    exact (show u = r from Subtype.ext hur) ▸ hu
  have hfixed : fixedPoints Q X = fixedPoints T X :=
    OyamaMinimalOrbitChoice.fixedPoints_map_subtype A T
  have hstrict : fixedPoints A X ⊂ fixedPoints Q X := by
    rw [hfixed]
    refine ⟨MinimalOrbitStabilizer.fixedPoints_subset_stabilizer_fixedPoints A X x, ?_⟩
    intro h
    exact hx (h (MinimalOrbitStabilizer.self_mem_stabilizer_fixedPoints A X x))
  exact ⟨hlt, hstrict,
    (Nat.card_congr (T.equivMapOfInjective A.subtype Subtype.val_injective).toEquiv).symm⟩

end FiveTransitive.ChosenMinimalOrbitInduced

end CFSG
