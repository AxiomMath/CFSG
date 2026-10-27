module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityRegular
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module QuadraticMap CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCPrimary

section Core

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

open _root_.Classical in
theorem exists_mixing_of_factor {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h2 : (2 : K) ≠ 0)
    {Ã : Subgroup (orthDerived Q)} (hint : DirectSum.IsInternal (innerSummand p Ã))
    (horth : ∀ i j, i ≠ j → ∀ u ∈ innerSummand p Ã i, ∀ v ∈ innerSummand p Ã j,
      polarBilin Q u v = 0)
    (hnd : ∀ i, (LinearMap.BilinForm.restrict (polarBilin Q) (innerSummand p Ã i)).Nondegenerate)
    {M N : Subgroup Ã} (hM : Nat.card M = p) (hN : Nat.card N = p) (hMN : M ≠ N)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hSM : ∀ v ∈ lineSpace M, x v ∈ lineSpace M)
    (hSN : ∀ v ∈ lineSpace N, x v ∈ lineSpace N) {r : K[X]}
    (hrmem : r ∈ primaryFactors x.toLinearMap) (hr1 : r ≠ X - 1)
    (hMr : lineSpace M ⊓ primaryComponent x.toLinearMap r ≠ ⊥)
    (hNr : lineSpace N ⊓ primaryComponent x.toLinearMap r ≠ ⊥) :
    2 ≤ primaryMultiplicity x.toLinearMap r ∧
      ∃ g ∈ specialBlock Q x r, ∃ v ∈ lineSpace M, ∃ s ∈ lineSpace M, ∃ t ∈ lineSpace N,
        t ≠ 0 ∧ g v = s + t := by
  have hij : (some ⟨M, hM⟩ : Option {M : Subgroup Ã // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h => hMN (by simpa using h)
  have hdisj : Disjoint (lineSpace M) (lineSpace N) :=
    hint.submodule_iSupIndep.pairwiseDisjoint hij
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  by_cases hself : r = reciprocalPolynomial r
  · have hv := exists_map_ne_zero_of_selfdual hx hrmem hself hSM (hnd (some ⟨M, hM⟩)) hMr
    have hw := exists_map_ne_zero_of_selfdual hx hrmem hself hSN (hnd (some ⟨N, hN⟩)) hNr
    obtain ⟨hm, g, hg, v, hv', s, hs, t, ht, ht0, hgv⟩ := exists_selfdual_mixing hx hp2 hrmem hr1
      hself h2 hSM hSN hdisj (fun u hu w hw => horth (some ⟨M, hM⟩) (some ⟨N, hN⟩) hij u hu w hw)
      hv hw
    exact ⟨hm, g, hg, v, hv', s, hs, t, ht, ht0, hgv⟩
  · exact exists_paired_mixing hx hrmem hself hSM hSN hdisj hMr hNr

end Core

end CFSG.RankThree.PartOne.KCOrthogonal
