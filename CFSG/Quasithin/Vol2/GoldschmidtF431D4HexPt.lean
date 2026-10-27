module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4HexBase

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin

universe u v

variable {X : Type u} [Group X] {V : Type v} [MulAction X V] {Γ : SimpleGraph V}

structure HexPt (X : Type u) [Group X] {V : Type v} [MulAction X V] (Γ : SimpleGraph V)
    (a b₀ : V) : Prop where
  dist : Γ.dist a b₀ = 6
  card : (Γ.neighborSet a).ncard = 9
  orb : ∀ b, Γ.dist a b = 6 → ∃ g : X, g • a = a ∧ g • b₀ = b
  two : ∀ u₁ u₂ v₁ v₂, Γ.Adj a u₁ → Γ.Adj a u₂ → u₁ ≠ u₂ → Γ.Adj a v₁ → Γ.Adj a v₂ → v₁ ≠ v₂ →
    ∃ g : X, g • a = a ∧ g • b₀ = b₀ ∧ g • u₁ = v₁ ∧ g • u₂ = v₂

namespace HexPt

variable {a b₀ : V} (L : HexPt X Γ a b₀)

include L

theorem three_le_card : 3 ≤ (Γ.neighborSet a).ncard := by
  rw [L.card]
  norm_num

theorem flag {u u' : V} (hu : Γ.Adj a u) (hu' : Γ.Adj a u') : ∃ k : X, k • a = a ∧ k • u = u' := by
  obtain ⟨k, h1, -, h3⟩ := trans_of_two (by have := L.three_le_card; omega) L.two hu hu'
  exact ⟨k, h1, h3⟩

variable [GraphAction X Γ] (hP : IsGenPolygon Γ 6)

include hP

theorem pathTrans {q q' : GPath Γ 6} (hq : q ∈ GPath.nbPaths Γ a 6)
    (hq' : q' ∈ GPath.nbPaths Γ a 6) : ∃ g : X, g • a = a ∧ g • q = q' := by
  obtain ⟨h, hha, hhq⟩ := L.orb _ (end_dist hP le_rfl hq)
  obtain ⟨h', hha', hhq'⟩ := L.orb _ (end_dist hP le_rfl hq')
  have hh1 : h⁻¹ • a = a := by rw [inv_smul_eq_iff, hha]
  have hh1' : h'⁻¹ • a = a := by rw [inv_smul_eq_iff, hha']
  have hs : h⁻¹ • q ∈ GPath.nbPaths Γ a 6 := TitsGeo.smul_mem_nbPaths hq hh1
  have hs' : h'⁻¹ • q' ∈ GPath.nbPaths Γ a 6 := TitsGeo.smul_mem_nbPaths hq' hh1'
  have hs6 : (h⁻¹ • q) 6 = b₀ := by rw [GPath.smul_apply, inv_smul_eq_iff, hhq]
  have hs'6 : (h'⁻¹ • q') 6 = b₀ := by rw [GPath.smul_apply, inv_smul_eq_iff, hhq']
  have a1 : Γ.Adj a ((h⁻¹ • q) 1) := by
    have := (h⁻¹ • q).adj 0 (by norm_num)
    rwa [hs.1] at this
  have a2 : Γ.Adj a ((h'⁻¹ • q') 1) := by
    have := (h'⁻¹ • q').adj 0 (by norm_num)
    rwa [hs'.1] at this
  obtain ⟨k, hka, hkb, hkw⟩ := trans_of_two (by have := L.three_le_card; omega) L.two a1 a2
  have hk : k • (h⁻¹ • q) = h'⁻¹ • q' := by
    refine eq_of_first_last hP (TitsGeo.smul_mem_nbPaths hs hka) hs' ?_ ?_
    · rw [GPath.smul_apply]
      exact hkw
    · rw [GPath.smul_apply, hs6, hs'6]
      exact hkb
  refine ⟨h' * k * h⁻¹, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hh1, hka, hha']
  · rw [GPath.mul_smul', GPath.mul_smul', hk, ← GPath.mul_smul', mul_inv_cancel,
      GPath.one_smul']

theorem noFix {p : GPath Γ 6} (hp : p ∈ GPath.nbPaths Γ a 6) {y : V} (hy : Γ.Adj (p 6) y)
    (hne : y ≠ p 5) : ¬ ∀ g ∈ (p.stabPath : Subgroup X), g • y = y :=
  noFix_of_two hP L.three_le_card L.orb L.two hp hy hne

theorem transPair {p q : GPath Γ 6} (hp : p ∈ GPath.nbPaths Γ a 6)
    (hq : q ∈ GPath.nbPaths Γ a 6) (hpq : p 1 ≠ q 1) {y y' : V} (hy : Γ.Adj a y)
    (hy' : Γ.Adj a y') : ∃ g ∈ ((p.stabPath : Subgroup X) ⊔ q.stabPath), g • y = y' :=
  transPair_of_two hP L.three_le_card L.orb L.two hp hq hpq hy hy'

end HexPt

end CFSG.Quasithin.D4Hex
