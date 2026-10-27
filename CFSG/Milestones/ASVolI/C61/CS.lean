module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

structure burnsideC56_CS (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) : Prop where
  T_two : IsPGroup 2 T
  l244 : ∀ S₀ : Subgroup G, S₀ ≠ ⊥ → S₀ ≤ S → H ≤ Subgroup.normalizer (S₀ : Set G) →
    T ⊓ Subgroup.normalizer (S₀ : Set G) = S
  charTwo : CharTwo H
  sylow : IsSylowTwoOf S H
  le_T : S ≤ T
  ne_T : S ≠ T
  block : IsChi0Block H L
  thompson : ⁅L, CFSG.Quasithin.thompsonJ S⁆ = L
  eq_join : H = conjJoin S L ⊔ S
  blocks : conjJoin S L = L ∨
    ∃ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
      conjJoin S L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
      ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥
  minParabolic : IsMinimalParabolic S H

end CFSG.QuasithinUnique
