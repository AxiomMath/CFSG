
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3A8Inputs
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA8Model
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallNoNilpCheck
public import Certificates.Data.Kernel.Census.CatFacts.C2013Defs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum
import Certificates.Kernel.Census.CatFacts.C2013K
import Certificates.Kernel.Census.CatFacts.C2013N
import Certificates.Kernel.Census.CatFacts.C2013N1
import Certificates.Kernel.Census.CatFacts.C2013N2
import Certificates.Kernel.Census.CatFacts.C2013N3

public section

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8
  CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.Certificates.Kernel.CatFacts

theorem noNilp_mono {n : Nat} {LA odd odd' : List (Equiv.Perm (Fin n))} {m : Nat}
    (hsub : ∀ x ∈ odd', x ∈ odd) (h : noNilpCheck LA odd' m = true) :
    noNilpCheck LA odd m = true := by
  unfold noNilpCheck at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro s hs
  have h1 := h s hs
  simp only [pairWitness, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.mem_filter] at h1 ⊢
  rcases h1 with h1 | ⟨x₁, ⟨hx₁, hc₁⟩, x₂, ⟨hx₂, hc₂⟩, h12⟩
  · exact Or.inl h1
  · exact Or.inr ⟨x₁, ⟨hsub x₁ hx₁, hc₁⟩, x₂, ⟨hsub x₂ hx₂, hc₂⟩, h12⟩

theorem odd3_sub : ∀ x ∈ odd3, x ∈ (elemsV QA8).filter oddTest := by
  intro x hx
  unfold odd3 at hx
  rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hx
  rw [List.mem_filter]
  refine ⟨hx.1, ?_⟩
  unfold oddTest
  rw [Bool.or_eq_true, decide_eq_true_eq]
  left
  rw [show 15 = 3 * 5 by rfl, pow_mul, hx.2.1, one_pow]

theorem noNilp2013 : noNilpCheck (elemsT QS8) ((elemsT QA8).filter oddTest) 315 = true := by
  rw [elemsT_eq_elemsV, elemsT_eq_elemsV]
  refine noNilp_mono odd3_sub ?_
  unfold noNilpCheck
  refine all_of_chunks _ _ noNilpLen 8 (by rw [len2013K]; decide) fun j hj => ?_
  have h : ∀ j < 8, noNilpBlock j = true := by
    intro j hj
    interval_cases j
    · exact noNilpBlock0
    · exact noNilpBlock1
    · exact noNilpBlock2
    · exact noNilpBlock3
    · exact noNilpBlock4
    · exact noNilpBlock5
    · exact noNilpBlock6
    · exact noNilpBlock7
  have h1 := h j hj
  unfold noNilpBlock noNilpCheck at h1
  exact h1

open Certificates in
open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSmall in
open CFSG.ComponentClassification.CatFactsSmall.A8 CFSG.GH74.KGroups CFSG.Certificates in
open CFSG.Sporadic.Schreier Subgroup in
theorem facts2013 : (centTrivCheck (elemsT QS8) a8 b8 = true)
    ∧ (noNilpCheck (elemsT QS8) ((elemsT QA8).filter oddTest) 315 = true) :=
  ⟨by rw [elemsT_eq_elemsV]; exact cent2013K, noNilp2013⟩

end CertificateChecks.KernelCatFacts
