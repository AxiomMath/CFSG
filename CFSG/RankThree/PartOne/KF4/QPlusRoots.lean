module

public import CFSG.RankThree.PartOne.KF4.Strings
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.RankThree.E6.RootLatticeTools

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open scoped Matrix

@[expose] def qpPairOK (β γ : Fin Tag.F4.rank → ℤ) : Bool :=
  decide (iform (τ := Tag.F4) β γ = 0) && !f4IsRootB (β + γ) && !f4IsRootB (β - γ)

@[expose] def qpOrthB : List (Fin Tag.F4.rank → ℤ) → Bool
  | [] => true
  | β :: C => C.all (qpPairOK β) && qpOrthB C

@[expose] def qpReflect (C : List (Fin Tag.F4.rank → ℤ)) (v : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → ℤ :=
  C.foldr (fun β v => v - (2 * iform (τ := Tag.F4) β v / iform (τ := Tag.F4) β β) • β) v

@[expose] def qpCascadeB (J : Finset (Fin Tag.F4.rank)) (C : List (Fin Tag.F4.rank → ℤ)) :
    Bool :=
  C.all f4IsRootB && C.all (fun β => decide (∀ i : Fin Tag.F4.rank, i ∉ J → β i = 0)) &&
    qpOrthB C && (List.finRange Tag.F4.rank).all (fun j =>
      decide (j ∉ J) ||
        decide (qpReflect C (Pi.single j 1) = -(Pi.single j 1 : Fin Tag.F4.rank → ℤ)))

structure QPCascade (J : Finset (Fin Tag.F4.rank)) (C : List (Fin Tag.F4.rank → ℤ)) : Prop where
  root : ∀ β ∈ C, f4IsRootB β = true
  supp : ∀ β ∈ C, ∀ i : Fin Tag.F4.rank, i ∉ J → β i = 0
  orth : C.Pairwise fun β γ =>
    iform (τ := Tag.F4) β γ = 0 ∧ f4IsRootB (β + γ) = false ∧ f4IsRootB (β - γ) = false
  neg : ∀ j ∈ J, qpReflect C (Pi.single j 1) = -(Pi.single j 1 : Fin Tag.F4.rank → ℤ)

theorem qpOrthB_pairwise : ∀ C : List (Fin Tag.F4.rank → ℤ), qpOrthB C = true →
    C.Pairwise fun β γ =>
      iform (τ := Tag.F4) β γ = 0 ∧ f4IsRootB (β + γ) = false ∧ f4IsRootB (β - γ) = false
  | [], _ => List.Pairwise.nil
  | β :: C, h => by
    simp only [qpOrthB, Bool.and_eq_true, List.all_eq_true] at h
    refine List.Pairwise.cons (fun γ hγ => ?_) (qpOrthB_pairwise C h.2)
    have := h.1 γ hγ
    simp only [qpPairOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

theorem QPCascade.of_check {J : Finset (Fin Tag.F4.rank)} {C : List (Fin Tag.F4.rank → ℤ)}
    (h : qpCascadeB J C = true) : QPCascade J C := by
  simp only [qpCascadeB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, qpOrthB_pairwise C h3, fun j hj => ?_⟩
  have := h4 j (List.mem_finRange j)
  simpa [hj] using this

theorem qpCascade_0 :
    QPCascade {f4Index 0}
      [![1, 0, 0, 0]] :=
  QPCascade.of_check (by decide +kernel)

theorem qpCascade_1 :
    QPCascade {f4Index 1}
      [![0, 1, 0, 0]] :=
  QPCascade.of_check (by decide +kernel)

theorem qpCascade_2 :
    QPCascade {f4Index 2}
      [![0, 0, 1, 0]] :=
  QPCascade.of_check (by decide +kernel)

theorem qpCascade_3 :
    QPCascade {f4Index 3}
      [![0, 0, 0, 1]] :=
  QPCascade.of_check (by decide +kernel)

theorem qpCascade_12 :
    QPCascade {f4Index 1, f4Index 2}
      [![0, 1, 0, 0], ![0, 1, 2, 0]] :=
  QPCascade.of_check (by decide +kernel)

theorem qpCascade_012 :
    QPCascade {f4Index 0, f4Index 1, f4Index 2}
      [![1, 0, 0, 0], ![1, 2, 2, 0], ![0, 0, 1, 0]] :=
  QPCascade.of_check (by decide +kernel)

theorem qpCascade_123 :
    QPCascade {f4Index 1, f4Index 2, f4Index 3}
      [![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 1, 2, 2]] :=
  QPCascade.of_check (by decide +kernel)

end CFSG.RankThree.PartOne.KF4
