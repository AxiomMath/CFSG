module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.ModelFacts

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem NearSimple.not_dvd_index_fixedNormalizer
    {p r : ℕ} {J : Type*} [Group J] [Finite J]
    (h : NearSimple p J) {f : MulAut J} (hf : orderOf f = p) (hr : r.Prime)
    (hJ : (r = 2 ∧ Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p))) ∨
      (r = 3 ∧ Nonempty (J ≃* PSU3 2 p))) :
    ¬ r ∣ (fixedNormalizer f).index := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨R⟩ : Nonempty (Sylow r J) := inferInstance
  obtain ⟨g, hg⟩ := h.sylow_le_conj_fixedNormalizer hf hr hJ R
  intro hdvd
  have h1 : ((fixedNormalizer f).map (MulAut.conj g).toMonoidHom).index =
      (fixedNormalizer f).index :=
    Subgroup.index_map_of_bijective (MulAut.conj g).bijective _
  exact R.not_dvd_index (hdvd.trans (h1 ▸ Subgroup.index_dvd_of_le hg))

end CFSG.SignalizerFunctorTheorem.McBride
