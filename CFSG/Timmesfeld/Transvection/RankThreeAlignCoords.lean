module

public import CFSG.Timmesfeld.Transvection.RankThreeAlign
public import CFSG.Timmesfeld.Transvection.ShortRootField

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)} {r k : ℕ} {P Q : Fin r → Subgroup G}

namespace IsFrame

variable [Finite G] (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ) {o i j : Fin r}
include hF hΔ

theorem aligned_of_aligned (hoi : o ≠ i) (hoj : o ≠ j) (hij : i ≠ j)
    (φ : ∀ l, SL2Coords (P l) (Q l) k) (hoi' : SL2Coords.Aligned Δ (φ o) (φ i))
    (hoj' : SL2Coords.Aligned Δ (φ o) (φ j))
    (hA2 : ∀ y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i),
      ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j),
        ⁅y, x⁆ ∈ shortRootGroup Δ (Q o) (P o) (P j) (Q j))
    (hB5 : ∀ y ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i),
      ∀ x ∈ shortRootGroup Δ (Q i) (P i) (P j) (Q j), x ≠ 1 → ⁅y, x⁆ = 1 → y = 1)
    (hne : ∃ y₀ ∈ shortRootGroup Δ (Q o) (P o) (P i) (Q i), y₀ ≠ 1) :
    SL2Coords.Aligned Δ (φ i) (φ j) := by
  intro ν x hx
  obtain ⟨y₀, hy₀, hy₀1⟩ := hne
  exact hF.commute_mul_of_commute_mul hΔ hoi hoj hij ((φ o).torusElt_mem ν)
    ((φ i).torusElt_mem ν) ((φ j).torusElt_mem ν) ((φ o).conjSub_torusElt ν).1
    ((φ o).conjSub_torusElt ν).2 ((φ i).conjSub_torusElt ν).1 ((φ i).conjSub_torusElt ν).2
    ((φ j).conjSub_torusElt ν).1 ((φ j).conjSub_torusElt ν).2 (hoi' ν) (hoj' ν) hA2 hB5 hy₀ hy₀1
    hx

end IsFrame

end CFSG.Timmesfeld.Transvection
