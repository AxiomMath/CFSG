module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinear
public import CFSG.RankThree.PartOne.KC.OrthogonalNaturalCommon
public import CFSG.RankThree.PartOne.KC.OrthogonalNonbinaryNonsplit

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module QuadraticMap CFSG CFSG.Assembly CFSG.RankThree.Classical
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCOrthogonalAut

theorem orthogonal_inner_plane_common_centralizer_nonbinary_primes_of_d4
    {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hpq : ¬ p ∣ Nat.card K ^ 2 - 1)
    (D : Subgroup (MulAut (ProjOrthDerived Q)))
    (hD : (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range ≤ D)
    (A : Subgroup (ProjOrthDerived Q)) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hD4 : (finrank K V = 8 ∧ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0) →
      ∀ α : MulAut (ProjOrthDerived Q),
        (∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
            ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
          α * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * α) →
        InducedBySemilinear Q α) :
    (⨅ (a : ProjOrthDerived Q) (_ : a ∈ A ∧ a ≠ 1), Subgroup.centralizer
      (((CFSG.layer ↥(D ⊓ Subgroup.centralizer
          ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q))))).map
        (D ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))).subtype :
          Subgroup (MulAut (ProjOrthDerived Q))) : Set (MulAut (ProjOrthDerived Q)))) = ⊥ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hV3 : 3 ≤ finrank K V := by
    obtain ⟨U, hU3, -⟩ := hT
    exact hU3 ▸ Submodule.finrank_le U
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  have : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨Ã, hle, hsyl, -⟩ :=
    orthogonal_inner_plane_kernel_line_quadratic_decomposition hℓ hp hp2 hpl Q hQ A hA hAc
  obtain ⟨hDat, hDims⟩ := kernelLineDims Q hQ hp hp2 hpl A hA hAc Ã ⟨hle, hsyl⟩
  obtain ⟨M₁, M₂, hM₁, hM₂, hM₁₂, hM₁a, hM₂a⟩ := hDat.two_active
  have hδ : 4 ≤ Nat.lcm (orderOf (Nat.card K : ZMod p)) 2 := by
    obtain ⟨hpos, hdvd⟩ := hDims.dvd M₁ hM₁ hM₁a
    exact four_le_lcm_of_not_dvd _ hpq (fun h => by
      rw [h] at hdvd
      exact hpos.ne' (zero_dvd_iff.mp hdvd))
  have hdim8 : 8 ≤ finrank K V := by
    have := hDims.le
    omega
  have hdimW : ∀ M : Subgroup Ã, Nat.card M = p → lineSpace M ≠ ⊥ →
      4 ≤ finrank K (lineFixSpace M) := fun M hM hMa => by
    obtain ⟨hpos, hdvd⟩ := hDims.dvd M hM hMa
    exact (hδ.trans (Nat.le_of_dvd hpos hdvd)).trans
      (Submodule.finrank_mono (inf_le_left : lineSpace M ≤ lineFixSpace M))
  refine eq_bot_iff.mpr fun α hα => ?_
  rw [Subgroup.mem_bot]
  have hcent : ∀ a ∈ A, a ≠ 1 → ∀ d ∈ CFSG.layer ↥(D ⊓ Subgroup.centralizer
      ({MulAut.conj a} : Set (MulAut (ProjOrthDerived Q)))),
      α * (d : MulAut (ProjOrthDerived Q)) = (d : MulAut (ProjOrthDerived Q)) * α := by
    intro a ha ha1 d hd
    have h1 := Subgroup.mem_iInf.mp hα a
    have h2 := Subgroup.mem_iInf.mp h1 ⟨ha, ha1⟩
    exact (Subgroup.mem_centralizer_iff.mp h2 _ (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)).symm
  have hind : InducedBySemilinear Q α := by
    by_cases hspl : finrank K V = 8 ∧ ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0
    · exact hD4 hspl α hcent
    · exact orthogonal_aut_semilinear Q hQ hdim8 (fun h8 hU => hspl ⟨h8, hU⟩) α
  obtain ⟨σ, F, hFσ, μ, hμ, hFQ, hκF⟩ := hind
  exact (orthogonal_natural_common_centralizer_with_nonexceptional_fixed_sectors Q hQ hT hp hp3
    hpl D hD A hA hAc Ã ⟨hle, hsyl⟩
    (fun M hM hMa => (by norm_num : 3 ≤ 4).trans (hdimW M hM hMa))
    (fun _ M hM hMa => by have := hdimW M hM hMa; omega)
    (fun _ M hM hMa ⟨h4, hS⟩ => not_split_four_of_active hp hp3 hpl hpq hDat hDims hM hMa h4 hS)
    σ F hFσ μ hμ hFQ α hκF hcent).2.2

end CFSG.RankThree.PartOne
