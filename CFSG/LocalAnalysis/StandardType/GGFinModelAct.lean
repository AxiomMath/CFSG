module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.StandardType.GGFinModel

section ConjAut

variable {C G : Type} [Group C] [Group G]

@[expose] noncomputable def ggConjAut (ι : C →* G) (hι : Function.Injective ι) :
    ↥(Subgroup.normalizer (ι.range : Set G)) →* MulAut C :=
  (MulAut.congr (MonoidHom.ofInjective hι).symm).toMonoidHom.comp
    (Subgroup.normalizerMonoidHom ι.range)

theorem ggConjAut_apply (ι : C →* G) (hι : Function.Injective ι)
    (m : ↥(Subgroup.normalizer (ι.range : Set G))) (x : C) :
    ι (ggConjAut ι hι m x) = (m : G) * ι x * (m : G)⁻¹ := by
  have h : ggConjAut ι hι m x = (MonoidHom.ofInjective hι).symm
      (Subgroup.normalizerMonoidHom ι.range m (MonoidHom.ofInjective hι x)) := rfl
  rw [h, MonoidHom.apply_ofInjective_symm]
  rfl

end ConjAut

end CFSG.StandardType.GGFinModel
