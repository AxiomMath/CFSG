module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexBase

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

structure HexLn (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (l y₀ m₀ : V) : Prop where
  dist5 : Γ.dist l y₀ = 5
  orb5 : ∀ y, Γ.dist l y = 5 → ∃ g : X, g • l = l ∧ g • y₀ = y
  dist6 : Γ.dist l m₀ = 6
  orb6 : ∀ y, Γ.dist l y = 6 → ∃ g : X, g • l = l ∧ g • m₀ = y
  card : (Γ.neighborSet l).ncard = 3
  two : ∀ u₁ u₂ v₁ v₂, Γ.Adj l u₁ → Γ.Adj l u₂ → u₁ ≠ u₂ → Γ.Adj l v₁ → Γ.Adj l v₂ → v₁ ≠ v₂ →
    ∃ g : X, g • l = l ∧ g • m₀ = m₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂

namespace HexLn

variable {l y₀ m₀ : V} (L : HexLn X Γ l y₀ m₀)

include L

theorem flag {u u' : V} (hu : Γ.Adj l u) (hu' : Γ.Adj l u') : ∃ k : X, k • l = l ∧ k • u = u' := by
  obtain ⟨k, h1, -, h3⟩ := trans_of_two (by rw [L.card]; norm_num) L.two hu hu'
  exact ⟨k, h1, h3⟩

variable [GraphAction X Γ] (hP : IsGenPolygon Γ 6)

include hP

theorem pathTrans5 {q q' : GPath Γ 5} (hq : q ∈ GPath.nbPaths Γ l 5)
    (hq' : q' ∈ GPath.nbPaths Γ l 5) : ∃ g : X, g • l = l ∧ g • q = q' := by
  have d := end_dist hP (by norm_num) hq
  have d' := end_dist hP (by norm_num) hq'
  obtain ⟨h, hhl, hhq⟩ := L.orb5 _ d
  obtain ⟨h', hhl', hhq'⟩ := L.orb5 _ d'
  have hh1 : h⁻¹ • l = l := by rw [inv_smul_eq_iff, hhl]
  have hga : (h' * h⁻¹) • l = l := by rw [mul_smul, hh1, hhl']
  refine ⟨h' * h⁻¹, hga, ?_⟩
  have g1 : q.IsGeodesic := by
    show Γ.dist (q 0) (q 5) = 5
    rw [hq.1]
    exact d
  have g2 : q'.IsGeodesic := by
    show Γ.dist (q' 0) (q' 5) = 5
    rw [hq'.1]
    exact d'
  refine hP.uniqueGeod 5 _ _ (GPath.IsGeodesic.smul hP.connected g1 _) g2 ?_ ?_ (by norm_num)
  · rw [GPath.smul_apply, hq.1, hq'.1, hga]
  · rw [GPath.smul_apply, ← hhq, ← hhq', mul_smul, inv_smul_smul]

theorem transPair {p q : GPath Γ 6} (hp : p ∈ GPath.nbPaths Γ l 6)
    (hq : q ∈ GPath.nbPaths Γ l 6) (hpq : p 1 ≠ q 1) {y y' : V} (hy : Γ.Adj l y)
    (hy' : Γ.Adj l y') : ∃ g ∈ ((p.stabPath : Subgroup X) ⊔ q.stabPath), g • y = y' :=
  transPair_of_two hP (by rw [L.card]) L.orb6 L.two hp hq hpq hy hy'

end HexLn

end CFSG.Quasithin.D4Hex
