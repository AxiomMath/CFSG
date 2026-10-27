module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.theorem_11_3

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 11.4

This file contains the Section 11 Corollary 11.4 statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 11.4. -/
public theorem CFSG.corollary_11_4
    {M A0 A H : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P)
    (hH : H ∈ section9MaximalSubgroupsContaining A)
    (hinter : section10Msigma M ⊓ section10Msigma H ≠ ⊥) :
    M = H := by
  classical
  have hnilMσ : Group.IsNilpotent (section10Msigma M) := theorem_11_3 h11
  obtain ⟨g, hHgM⟩ : ∃ g : G, H.conjBy g = M := by
    by_contra hnone
    have hconj : ∀ g : G, H.conjBy g ≠ M := by
      intro g hg
      exact hnone ⟨g, hg⟩
    have hdisj :
        Disjoint (section10Msigma M) (section10Msigma H) :=
      (lemma_10_12_b h11.maximal hH.1 hconj hnilMσ).1
    exact hinter (disjoint_iff.mp hdisj)
  have hH_eq_Mginv : H = M.conjBy g⁻¹ := by
    calc
      H = (H.conjBy g).conjBy g⁻¹ := (section11_conjBy_inv (G := G) H g).symm
      _ = M.conjBy g⁻¹ := by rw [hHgM]
  have hAginv : A ≤ M.conjBy g⁻¹ := by
    simpa [← hH_eq_Mginv] using hH.2
  have hginvM : g⁻¹ ∈ M := by
    by_contra hnot
    have hbot := corollary_11_2_a
      (M := M) (A0 := A0) (A := A) (p := p) (P := P)
      h11 (g := g⁻¹) hnot hAginv
    have hle :
        section10Msigma M ⊓ section10Msigma H ≤
          section10Msigma M ⊓ M.conjBy g⁻¹ := by
      intro x hx
      exact ⟨hx.1, by
        have hxH : x ∈ H := section11_msigma_le H hx.2
        simpa [hH_eq_Mginv] using hxH⟩
    have hbot' : section10Msigma M ⊓ section10Msigma H = ⊥ :=
      le_bot_iff.mp (by simpa [hbot] using hle)
    exact hinter hbot'
  have hM_conj_ginv : M.conjBy g⁻¹ = M := by
    exact section11_conjBy_eq_of_mem_normalizer
      (H := M) (g := g⁻¹) (Subgroup.le_normalizer hginvM)
  exact hH_eq_Mginv.trans hM_conj_ginv |>.symm

end Section11
