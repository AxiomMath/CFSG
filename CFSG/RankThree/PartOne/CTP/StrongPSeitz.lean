module

public import CFSG.RankThree.PartOne.CTP.StrongPSolvable
public import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne (IsStronglyPEmbedded ExtSeitz)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {H : Type} [Group H]

theorem seitz_stronglyPEmbedded (hSeitz : ExtSeitz) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (S : Subgroup H) [S.Normal] [Finite H] {t : StatedLieTag} {n r f : ℕ}
    (hadm : StatedLieAdmissible t n r f) (hmodel : CFSG.Blueprint.LieModel ↥S t n r f)
    (hpr : p ≠ r) (hSc : Subgroup.centralizer (S : Set H) = ⊥)
    [hout : Group.IsSolvable (Outer ↥S)] {Y : Subgroup H} (hY : IsStronglyPEmbedded p Y)
    {E : Subgroup H} (hEY : E ≤ Y) [CFSG.IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) :
    p = 5 ∧ ((t = .Tits ∧ n = 0 ∧ r = 2 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ r = 2 ∧ f = 5)) := by
  have hρ := conjNormal_injective_of_centralizer S hSc
  have hE'ab : CFSG.IsElementaryAbelian p (E.map (MulAut.conjNormal (H := S))) :=
    CFSG.IsElementaryAbelian.map _
  have hE'card : Nat.card (E.map (MulAut.conjNormal (H := S))) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective hρ, hE]
  have hE'nc : ¬ IsCyclic (E.map (MulAut.conjNormal (H := S))) :=
    CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hE'card
  rcases hSeitz ↥S t n r f hadm hmodel p Fact.out hp5 hpr _ hE'ab hE'nc with hgen | ⟨hcard, hexc⟩
  · exfalso
    refine IsStronglyPEmbedded.false_of_generation hY hEY hE (S := S) ?_
      (solvable_quotient_of_outer S hSc)
    intro s hs
    have hmem : (⟨s, hs⟩ : ↥S) ∈ Subgroup.closure
        {k : ↥S | ∃ F : Subgroup (MulAut ↥S), F ≤ E.map (MulAut.conjNormal (H := S)) ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} := hgen ▸ Subgroup.mem_top _
    have hle : Subgroup.closure
        {k : ↥S | ∃ F : Subgroup (MulAut ↥S), F ≤ E.map (MulAut.conjNormal (H := S)) ∧ F ≠ ⊥ ∧
          ∀ φ ∈ F, φ k = k} ≤
        (Subgroup.closure {k : H | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k}).comap S.subtype := by
      rw [Subgroup.closure_le]
      rintro k ⟨F, hFE, hF1, hFk⟩
      obtain ⟨⟨φ, hφF⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF1
      obtain ⟨x, hxE, rfl⟩ := hFE hφF
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hφ1 (Subtype.ext (map_one _))
      refine Subgroup.subset_closure ⟨x, hxE, hx1, ?_⟩
      have h1 := congrArg (fun a : ↥S => (a : H)) (hFk _ hφF)
      simp only [MulAut.conjNormal_apply] at h1
      calc (k : H) * x = x * k * x⁻¹ * x := by rw [h1]
        _ = x * k := by group
    exact hle hmem
  · refine ⟨?_, hexc⟩
    have h25 : p ^ 2 = 5 ^ 2 := by rw [← hE'card, hcard]; norm_num
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h25

end CFSG.RankThree.PartOne.CTP
