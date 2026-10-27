module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelDefs

public section

namespace CFSG.StandardType.E6ThreeModel

theorem modelSCr_transport {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (I : Set (MulAut R)) (I' : Set (MulAut R'))
    (hI : ∀ φ : MulAut R', φ ∈ I' ↔ (MulAut.congr e).symm φ ∈ I) :
    GGE6ThreeModelSCr R I → GGE6ThreeModelSCr R' I' := by
  intro h L' _ _ ψ' hψ' hker hperf A hA hAI h5 hsc
  have hψ : Function.Surjective (e.symm.toMonoidHom.comp ψ') :=
    e.symm.surjective.comp hψ'
  have hkerEq : (e.symm.toMonoidHom.comp ψ').ker = ψ'.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  have := h L' (e.symm.toMonoidHom.comp ψ') hψ (hkerEq ▸ hker) hperf A hA ?_ h5 hsc
  · rwa [hkerEq] at this
  · intro a ha
    obtain ⟨φ', hφ', hφ'a⟩ := hAI a ha
    refine ⟨(MulAut.congr e).symm φ', (hI φ').1 hφ', fun l => ?_⟩
    simp [MulAut.congr_symm_apply, hφ'a]

end CFSG.StandardType.E6ThreeModel
