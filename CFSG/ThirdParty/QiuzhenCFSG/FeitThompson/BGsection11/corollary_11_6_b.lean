module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.corollary_11_6_a

namespace CFSG
end CFSG
open CFSG

/-!
# Corollary 11.6(b)

This file contains the Section 11 Corollary 11.6(b) statement and proof.
-/

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 11.6(b). -/
public theorem CFSG.corollary_11_6_b
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    subgroupCentralizerIn (section10Msigma M) A = ⊥ := by
  classical
  let Pamb : Subgroup G := section10AmbientSylowSubgroup M P
  obtain ⟨g, hgN, hgM⟩ :
      ∃ g : G, g ∈ Subgroup.normalizer (Pamb : Set G) ∧ g ∉ M := by
    by_contra h
    apply h11.not_normalizer_ambient_sylow_le
    intro x hxN
    by_contra hxM
    exact h ⟨x, hxN, hxM⟩
  have hAeqΩ : A = section11OmegaOne p Pamb := by
    simpa [Pamb] using corollary_11_6_a h11
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := by
    have hgΩ : g ∈ Subgroup.normalizer (section11OmegaOne p Pamb : Set G) :=
      section11_normalizer_le_normalizer_omegaOne p Pamb hgN
    simpa [hAeqΩ] using hgΩ
  have hA_le_Mg : A ≤ M.conjBy g := by
    have hginvA : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      Subgroup.inv_mem (Subgroup.normalizer (A : Set G)) hgA
    have hA_conj_inv : A.conjBy g⁻¹ = A :=
      section11_conjBy_eq_of_mem_normalizer hginvA
    have hA_conj_inv_le_M : A.conjBy g⁻¹ ≤ M := by
      simpa [hA_conj_inv] using h11.A_le_M
    simpa using
      (section11_le_conjBy_inv_of_conjBy_le
        (G := G) (H := A) (K := M) (g := g⁻¹) hA_conj_inv_le_M)
  have hA0g_le_A : A0.conjBy g ≤ A := by
    have hA_conj : A.conjBy g = A :=
      section11_conjBy_eq_of_mem_normalizer hgA
    calc
      A0.conjBy g ≤ A.conjBy g := Subgroup.map_mono h11.A0_le_A
      _ = A := hA_conj
  have hfixA0g :
      section10Msigma M ⊓ Subgroup.centralizer ((A0.conjBy g) : Set G) = ⊥ :=
    corollary_11_2_b h11 hgM hA_le_Mg
  have hle :
      subgroupCentralizerIn (section10Msigma M) A ≤
        section10Msigma M ⊓ Subgroup.centralizer ((A0.conjBy g) : Set G) := by
    intro x hx
    exact ⟨hx.1, Subgroup.centralizer_le (show (A0.conjBy g : Set G) ⊆ (A : Set G) from
      hA0g_le_A) hx.2⟩
  exact le_bot_iff.mp (by simpa [subgroupCentralizerIn, hfixA0g] using hle)

end Section11
