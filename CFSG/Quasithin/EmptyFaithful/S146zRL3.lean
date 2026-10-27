module

public import CFSG.Quasithin.EmptyFaithful.SBc15F3Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
import all CFSG.Quasithin.EmptyFaithful.SBc15F3Model

public section

namespace CFSG.Quasithin

namespace SBc15

namespace L3

namespace N3

@[expose] def tr (x : N3) : N3 := ⟨x.a, x.d, x.g, x.b, x.e, x.h, x.c, x.f, x.i⟩

@[expose] def tauN (x : N3) : N3 := tr (inv x)

set_option maxRecDepth 100000 in
theorem pe_tau_a : ∀ g ∈ elems, ∃ y ∈ al, conj g (tauN y) ∉ al := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pe_tau_b : ∀ g ∈ elems, ∃ y ∈ al', conj g (tauN y) ∉ al' := by
  decide +kernel

end N3

open CFSG.ComponentClassification CFSG.QuasithinUnique.Setup.Family

theorem toN3_slGraphAut (x : SL32) :
    toN3 (CatalogueBGraphForm.slGraphAut 3 (ZMod 2) x) = N3.tauN (toN3 x) := by
  show _ = N3.tr (N3.inv (toN3 x))
  rw [← toN3_inv]
  rfl

theorem slConjugation_toGL_apply (s x : SL32) :
    CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) (Matrix.SpecialLinearGroup.toGL s) x =
      s * x * s⁻¹ := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]

theorem aut_SL32_cases (φ : MulAut SL32) :
    (∃ s : SL32, φ = MulAut.conj s) ∨
      ∃ s : SL32, ∀ x : SL32,
        φ x = s * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) x * s⁻¹ := by
  rcases aut_SL3_cases φ with ⟨A, hA⟩ | ⟨A, hA⟩
  · obtain ⟨s, hs⟩ := (slEquivGL 3).surjective A
    refine Or.inl ⟨s, MulEquiv.ext fun x => ?_⟩
    have hs' : Matrix.SpecialLinearGroup.toGL s = A := hs
    rw [hA, MulAut.conj_apply, ← slConjugation_toGL_apply, hs']
  · obtain ⟨s, hs⟩ := (slEquivGL 3).surjective A
    refine Or.inr ⟨s, fun x => ?_⟩
    have hs' : Matrix.SpecialLinearGroup.toGL s = A := hs
    rw [hA, MulAut.mul_apply, ← slConjugation_toGL_apply, hs']

theorem exists_tau_not_mem_A4a (s : SL32) :
    ∃ y ∈ A4a, s * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) y * s⁻¹ ∉ A4a := by
  obtain ⟨m, hm, hno⟩ := N3.pe_tau_a (toN3 s) (toN3_mem_elems s)
  obtain ⟨x, hx, rfl⟩ := exists_A4a hm
  refine ⟨x, hx, fun h => hno ?_⟩
  rwa [mem_A4a, toN3_conj, toN3_slGraphAut] at h

theorem exists_tau_not_mem_A4b (s : SL32) :
    ∃ y ∈ A4b, s * CatalogueBGraphForm.slGraphAut 3 (ZMod 2) y * s⁻¹ ∉ A4b := by
  obtain ⟨m, hm, hno⟩ := N3.pe_tau_b (toN3 s) (toN3_mem_elems s)
  obtain ⟨x, hx, rfl⟩ := exists_A4b hm
  refine ⟨x, hx, fun h => hno ?_⟩
  rwa [mem_A4b, toN3_conj, toN3_slGraphAut] at h

theorem inner_of_stab_A4a {φ : MulAut SL32} (h : ∀ y ∈ A4a, φ y ∈ A4a) :
    φ ∈ (MulAut.conj : SL32 →* MulAut SL32).range := by
  rcases aut_SL32_cases φ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨s, hs.symm⟩
  · exfalso
    obtain ⟨y, hy, hno⟩ := exists_tau_not_mem_A4a s
    exact hno (hs y ▸ h y hy)

theorem inner_of_stab_A4b {φ : MulAut SL32} (h : ∀ y ∈ A4b, φ y ∈ A4b) :
    φ ∈ (MulAut.conj : SL32 →* MulAut SL32).range := by
  rcases aut_SL32_cases φ with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨s, hs.symm⟩
  · exfalso
    obtain ⟨y, hy, hno⟩ := exists_tau_not_mem_A4b s
    exact hno (hs y ▸ h y hy)

end L3

end SBc15

end CFSG.Quasithin
