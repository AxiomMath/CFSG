module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingDichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingIsoPoint
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingBaerFrame
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingBaerTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary CFSG.Open
open CFSG.LieType.Universal.Unitary (SUid)
open scoped Matrix

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {n p : ℕ}

private theorem exists_stab_isoLine_of_totSing_T1J6 (hσ : IsUnitaryInvolution σ)
    (hσpow : ∀ c, σ c = c ^ 2 ^ n) (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (E : AddSubgroup (Fin 4 → F)) {v : Fin 4 → F} (hv0 : v ≠ 0)
    (hvv : herm σ v v = 0) (hvE : ∀ c : F, c • v ∈ E) :
    ∃ X : AddSubgroup (Fin 4 → F), X ≤ E ∧ X ≠ ⊥ ∧
      ∃ P : Subgroup (GL (Fin 4) F), P ≤ SUid σ 4 ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
        ∀ g ∈ P, ∀ x : Fin 4 → F,
          ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ X ↔ x ∈ X := by
  obtain ⟨P, hPsu, hPab, hPcard, hPstab⟩ :=
    exists_stab_isotropicLine hσ hσpow hF hp hpq hv0 hvv
  refine ⟨(Submodule.span F {v}).toAddSubgroup, ?_, ?_, P, hPsu, hPab, hPcard, ?_⟩
  · intro x hx
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    exact hvE a
  · intro hbot
    have hvX : v ∈ (Submodule.span F {v}).toAddSubgroup := by
      rw [Submodule.mem_toAddSubgroup]
      exact Submodule.mem_span_singleton_self v
    exact hv0 (by simpa [hbot] using hvX)
  · intro g hg x
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup]
    exact hPstab g hg x

private theorem exists_stab_baerLine_of_totSing_T1J6 (hσ : IsUnitaryInvolution σ)
    (hσpow : ∀ c, σ c = c ^ 2 ^ n) (h2 : (2 : F) = 0) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (E : AddSubgroup (Fin 4 → F))
    (hE : Nat.card E = 2 ^ (4 * n)) (hQ : ∀ x ∈ E, herm σ x x = 0) {e f : Fin 4 → F}
    (he : e ∈ E) (hf : f ∈ E) (hef : herm σ e f = 1) :
    ∃ X : AddSubgroup (Fin 4 → F), X ≤ E ∧ X ≠ ⊥ ∧
      ∃ P : Subgroup (GL (Fin 4) F), P ≤ SUid σ 4 ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
        ∀ g ∈ P, ∀ x : Fin 4 → F,
          ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ X ↔ x ∈ X := by
  obtain ⟨z, hz, hcoord⟩ :=
    exists_orthonormal_baer_frame hσ h2 (hQ e he) (hQ f hf) hef
  obtain ⟨X, P, hX, hPsu, hPab, hPcard, hPstab⟩ :=
    exists_stab_baerLine hσ hσpow hF hp hpq z hz
  refine ⟨X, ?_, ?_, P, hPsu, hPab, hPcard, hPstab⟩
  · intro x hx
    rw [hX x] at hx
    obtain ⟨α, rfl⟩ := hx
    obtain ⟨a, b, ha, hb, hab⟩ := hcoord α
    rw [hab]
    exact E.add_mem (smul_mem_of_totSing hσ h2 hF E hE hQ ha he)
      (smul_mem_of_totSing hσ h2 hF E hE hQ hb hf)
  · intro hbot
    have hz01 : z 0 + z 1 ∈ X := by
      rw [hX (z 0 + z 1)]
      exact ⟨1, by simp⟩
    have hne : z 0 + z 1 ≠ 0 := by
      intro h0
      have h1 : herm σ (z 0) (z 0 + z 1) = 1 := by
        rw [herm_add_right, hz 0 0, hz 0 1]
        simp
      rw [h0, herm_zero_right] at h1
      exact one_ne_zero h1.symm
    have hmem : z 0 + z 1 ∈ (⊥ : AddSubgroup (Fin 4 → F)) := by
      rw [← hbot]
      exact hz01
    exact hne (by simpa using hmem)

theorem exists_noncyclic_stab_of_totSing (hσ : IsUnitaryInvolution σ)
    (hσpow : ∀ c, σ c = c ^ 2 ^ n) (h2 : (2 : F) = 0) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (E : AddSubgroup (Fin 4 → F))
    (hE : Nat.card E = 2 ^ (4 * n)) (hQ : ∀ x ∈ E, herm σ x x = 0) :
    ∃ X : AddSubgroup (Fin 4 → F), X ≤ E ∧ X ≠ ⊥ ∧
      ∃ P : Subgroup (GL (Fin 4) F), P ≤ SUid σ 4 ∧ IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
        ∀ g ∈ P, ∀ x : Fin 4 → F,
          ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ x ∈ X ↔ x ∈ X := by
  rcases exists_isotropic_line_or_hyperbolic_pair hσ h2 hF E hE hQ with
    ⟨v, hv0, hvv, hvE⟩ | ⟨e, he, f, hf, hef⟩
  · exact exists_stab_isoLine_of_totSing_T1J6 hσ hσpow hF hp hpq E hv0 hvv hvE
  · exact exists_stab_baerLine_of_totSing_T1J6 hσ hσpow h2 hF hp hpq E hE hQ he hf hef

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
