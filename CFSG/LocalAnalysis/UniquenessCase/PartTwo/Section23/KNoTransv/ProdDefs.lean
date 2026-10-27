module

public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

variable {G S₀ : Type*} [Group G] [Group S₀] {H : Subgroup G}

@[expose] def prodFst (g : ↥H →* S₀ × S₀) : Subgroup G :=
  ((MonoidHom.snd S₀ S₀).comp g).ker.map H.subtype

@[expose] def prodSnd (g : ↥H →* S₀ × S₀) : Subgroup G :=
  ((MonoidHom.fst S₀ S₀).comp g).ker.map H.subtype

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
