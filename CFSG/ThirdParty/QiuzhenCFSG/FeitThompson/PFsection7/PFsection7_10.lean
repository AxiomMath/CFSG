module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_10_statement
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G)
    (G0 : Set G) : Prop :=
  theorem_7_10_source_hypothesis L H G0 →
    theorem_7_10_lowerBoundData L H G0 →
    ∃ i, let h := Nat.card (H i); let e := (H i).relIndex (L i);
      (((G0.ncard : ℝ) - 1) / (Nat.card G : ℝ)) ≥
        (e - 1 : ℝ) *
          (((h : ℝ) - 2 * (e : ℝ) - 1) / ((e : ℝ) * (h : ℝ)) +
            2 / ((h : ℝ) * ((h : ℝ) + 2)))

/-- Peterfalvi `(7.11)`. -/


private theorem theorem_7_10_lowerBound_simplify {h e : ℕ}
    (hh : 0 < h) (he : 0 < e) :
    1 - (e : ℝ) / (h : ℝ) -
          (((h : ℝ) - 1) / ((e : ℝ) * (h : ℝ))) -
          (((e : ℝ) - 1) / ((h : ℝ) + 2)) =
      ((e : ℝ) - 1) *
        ((((h : ℝ) - 2 * (e : ℝ) - 1) /
            ((e : ℝ) * (h : ℝ))) +
          2 / ((h : ℝ) * ((h : ℝ) + 2))) := by
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  have heR : (e : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  have hh2R : (h : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hhR, heR, hh2R]
  ring

public theorem theorem_7_10
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Fintype I]
    (L H : I → Subgroup G)
    (G0 : Set G) :
    theorem_7_10_statement L H G0 := by
  rw [theorem_7_10_statement]
  intro _hsource hboundData
  rcases hboundData with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  dsimp at hi ⊢
  rcases hi with ⟨hh, he, hbound⟩
  calc
    (((G0.ncard : ℝ) - 1) / (Nat.card G : ℝ)) ≥
        1 - ((H i).relIndex (L i) : ℝ) / (Nat.card (H i) : ℝ) -
          (((Nat.card (H i) : ℝ) - 1) /
            (((H i).relIndex (L i) : ℝ) * (Nat.card (H i) : ℝ))) -
          ((((H i).relIndex (L i) : ℝ) - 1) /
            ((Nat.card (H i) : ℝ) + 2)) := hbound
    _ = (((H i).relIndex (L i) : ℝ) - 1) *
          ((((Nat.card (H i) : ℝ) -
              2 * ((H i).relIndex (L i) : ℝ) - 1) /
              (((H i).relIndex (L i) : ℝ) * (Nat.card (H i) : ℝ))) +
            2 / ((Nat.card (H i) : ℝ) * ((Nat.card (H i) : ℝ) + 2))) :=
        theorem_7_10_lowerBound_simplify hh he

end CFSG.Section7
