module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexPt
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexLn
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoTransport

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin CFSG.Quasithin.TitsGeo

universe u u' v v'

variable {X : Type u} {X' : Type u'} [Group X] [Group X'] {V : Type v} {V' : Type v'}
  [MulAction X V] [MulAction X' V'] {Γ : SimpleGraph V} {Γ' : SimpleGraph V'}

namespace HexPt

variable {Φ : X →* X'} {e : V' ≃ V} {a b₀ : V'}

theorem transport (E : EqData Φ e Γ Γ') (L : HexPt X Γ (e a) (e b₀)) : HexPt X' Γ' a b₀ where
  dist := by rw [E.dist]; exact L.dist
  card := by rw [E.ncard_neighborSet]; exact L.card
  orb b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb (e b) (by rw [← E.dist]; exact hb)
    exact ⟨Φ g, (E.smul_eq_iff g a a).2 h1, (E.smul_eq_iff g b₀ b).2 h2⟩
  two u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne' := by
    obtain ⟨k, h1, h2, h3, h4⟩ := L.two (e u₁) (e u₂) (e v₁) (e v₂) ((E.adj _ _).1 hu₁)
      ((E.adj _ _).1 hu₂) (fun h => hne (e.injective h)) ((E.adj _ _).1 hv₁)
      ((E.adj _ _).1 hv₂) (fun h => hne' (e.injective h))
    exact ⟨Φ k, (E.smul_eq_iff k a a).2 h1, (E.smul_eq_iff k b₀ b₀).2 h2,
      (E.smul_eq_iff k u₁ v₁).2 h3, (E.smul_eq_iff k u₂ v₂).2 h4⟩

end HexPt

namespace HexLn

variable {Φ : X →* X'} {e : V' ≃ V} {l y₀ m₀ : V'}

theorem transport (E : EqData Φ e Γ Γ') (L : HexLn X Γ (e l) (e y₀) (e m₀)) :
    HexLn X' Γ' l y₀ m₀ where
  dist5 := by rw [E.dist]; exact L.dist5
  orb5 b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb5 (e b) (by rw [← E.dist]; exact hb)
    exact ⟨Φ g, (E.smul_eq_iff g l l).2 h1, (E.smul_eq_iff g y₀ b).2 h2⟩
  dist6 := by rw [E.dist]; exact L.dist6
  orb6 b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb6 (e b) (by rw [← E.dist]; exact hb)
    exact ⟨Φ g, (E.smul_eq_iff g l l).2 h1, (E.smul_eq_iff g m₀ b).2 h2⟩
  card := by rw [E.ncard_neighborSet]; exact L.card
  two u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne' := by
    obtain ⟨k, h1, h2, h3, h4⟩ := L.two (e u₁) (e u₂) (e v₁) (e v₂) ((E.adj _ _).1 hu₁)
      ((E.adj _ _).1 hu₂) (fun h => hne (e.injective h)) ((E.adj _ _).1 hv₁)
      ((E.adj _ _).1 hv₂) (fun h => hne' (e.injective h))
    exact ⟨Φ k, (E.smul_eq_iff k l l).2 h1, (E.smul_eq_iff k m₀ m₀).2 h2,
      (E.smul_eq_iff k u₁ v₁).2 h3, (E.smul_eq_iff k u₂ v₂).2 h4⟩

end HexLn

end CFSG.Quasithin.D4Hex
