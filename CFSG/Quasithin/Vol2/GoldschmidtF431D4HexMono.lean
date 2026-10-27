module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexPt
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexLn

public section

namespace CFSG.Quasithin.D4Hex

universe u u' v

variable {X : Type u} {Y : Type u'} [Group X] [Group Y] {V : Type v} [MulAction X V]
  [MulAction Y V] {Γ : SimpleGraph V}

theorem HexPt.mono {a b₀ : V} (ψ : X →* Y) (hψ : ∀ (x : X) (v : V), ψ x • v = x • v)
    (L : HexPt X Γ a b₀) : HexPt Y Γ a b₀ where
  dist := L.dist
  card := L.card
  orb b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb b hb
    exact ⟨ψ g, by rw [hψ, h1], by rw [hψ, h2]⟩
  two u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne' := by
    obtain ⟨g, h1, h2, h3, h4⟩ := L.two u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne'
    exact ⟨ψ g, by rw [hψ, h1], by rw [hψ, h2], by rw [hψ, h3], by rw [hψ, h4]⟩

theorem HexLn.mono {l y₀ m₀ : V} (ψ : X →* Y) (hψ : ∀ (x : X) (v : V), ψ x • v = x • v)
    (L : HexLn X Γ l y₀ m₀) : HexLn Y Γ l y₀ m₀ where
  dist5 := L.dist5
  orb5 b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb5 b hb
    exact ⟨ψ g, by rw [hψ, h1], by rw [hψ, h2]⟩
  dist6 := L.dist6
  orb6 b hb := by
    obtain ⟨g, h1, h2⟩ := L.orb6 b hb
    exact ⟨ψ g, by rw [hψ, h1], by rw [hψ, h2]⟩
  card := L.card
  two u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne' := by
    obtain ⟨g, h1, h2, h3, h4⟩ := L.two u₁ u₂ v₁ v₂ hu₁ hu₂ hne hv₁ hv₂ hne'
    exact ⟨ψ g, by rw [hψ, h1], by rw [hψ, h2], by rw [hψ, h3], by rw [hψ, h4]⟩

end CFSG.Quasithin.D4Hex
