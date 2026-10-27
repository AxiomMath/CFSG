module

public import CFSG.Monster.Existence.TwoPoint.Classes
public import CFSG.Monster.Existence.TwoPointConj

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem exists_conj_pair_of_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hsep : OddTypesSeparated a z₀) {α β y : G} (hα : IsConj a α)
    (hβ : IsConj a β) (hy : IsConj a y) (h : IsConj (α * β) (a * y)) :
    ∃ g : G, g * a * g⁻¹ = α ∧ g * y * g⁻¹ = β := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hα
  set β' := g⁻¹ * β * g with hβ'
  have hβ'A : IsConj a β' := hβ.trans (isConj_iff.2 ⟨g⁻¹, by rw [hβ']; group⟩)
  have hprod : g⁻¹ * (α * β) * g = a * β' := by
    rw [← hg, hβ']
    group
  have h1 : IsConj (a * y) (a * β') := by
    rw [← hprod]
    exact h.symm.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
  obtain ⟨c, hc, hcy⟩ := three_i I hG hex hsep (IsConj.refl a) hy hβ'A h1
  have hca : c * a * c⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  refine ⟨g * c, ?_, ?_⟩
  · calc g * c * a * (g * c)⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by group
      _ = α := by rw [hca, hg]
  · calc g * c * y * (g * c)⁻¹ = g * (c * y * c⁻¹) * g⁻¹ := by group
      _ = β := by rw [hcy, hβ']; group

theorem twoPointShape_of_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hsep : OddTypesSeparated a z₀) {α β y : G} (hα : IsConj a α)
    (hβ : IsConj a β) (hy : IsConj a y) (h : IsConj (α * β) (a * y)) {i : Fin 9}
    (hs : TwoPointShape (cent2 a y) i) : TwoPointShape (cent2 α β) i := by
  obtain ⟨g, rfl, rfl⟩ := exists_conj_pair_of_isConj I hG hex hsep hα hβ hy h
  exact TwoPointShape.conj g hs

end CFSG.Monster.Existence
