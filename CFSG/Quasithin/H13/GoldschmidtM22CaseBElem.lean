module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.GM22

variable {G : Type} [Group G]

theorem eq_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).mp hZ
  have h1 := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
  have h2 := hy ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem relIndex_le_two_of_E {V T D E Z : Subgroup G}
    (hQab : ∀ x ∈ Subgroup.centralizer (V : Set G), ∀ y ∈ Subgroup.centralizer (V : Set G),
      x * y = y * x)
    (hEQ : E ≤ Subgroup.centralizer (V : Set G))
    (hQVE : ∀ q ∈ Subgroup.centralizer (V : Set G), ∃ v ∈ V, ∃ e ∈ E, q = v * e)
    (hZV : Z ≤ V) (hEV : ∀ x ∈ E, x ∈ V → x ∈ Z) (hZcard : Nat.card Z = 2)
    (hTE : ∀ t ∈ T, ∀ e ∈ E, t * e * t⁻¹ ∈ E)
    (hTQ : ∀ t ∈ T, ∀ q ∈ Subgroup.centralizer (V : Set G), t * q * t⁻¹ * q⁻¹ ∈ V)
    (hDE : ∀ p ∈ D, ∀ e ∈ E, p * e = e * p)
    (hEc : ∀ e ∈ E, (∀ t ∈ T, t * e = e * t) → e ∈ Z)
    (hcov : ∃ t₀ ∈ T, ∀ t ∈ T,
      (∃ p ∈ D, ∃ q ∈ Subgroup.centralizer (V : Set G), t = p * q) ∨
      ∃ p ∈ D, ∃ q ∈ Subgroup.centralizer (V : Set G), t = t₀ * p * q) :
    V.relIndex (Subgroup.centralizer (V : Set G)) ≤ 2 := by
  obtain ⟨t₀, ht₀, hcov⟩ := hcov
  have hθZ : ∀ e ∈ E, t₀ * e * t₀⁻¹ * e⁻¹ ∈ Z := fun e he =>
    hEV _ (E.mul_mem (hTE t₀ ht₀ e he) (E.inv_mem he)) (hTQ t₀ ht₀ e (hEQ he))
  have hθmul : ∀ e ∈ E, ∀ e' ∈ E, t₀ * (e * e') * t₀⁻¹ * (e * e')⁻¹ =
      (t₀ * e * t₀⁻¹ * e⁻¹) * (t₀ * e' * t₀⁻¹ * e'⁻¹) := by
    intro e he e' he'
    have hc : (t₀ * e' * t₀⁻¹ * e'⁻¹) * e = e * (t₀ * e' * t₀⁻¹ * e'⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hEQ he) _ (hZV (hθZ e' he'))
    calc t₀ * (e * e') * t₀⁻¹ * (e * e')⁻¹
        = (t₀ * e * t₀⁻¹ * e⁻¹) * (e * (t₀ * e' * t₀⁻¹ * e'⁻¹) * e⁻¹) := by group
      _ = (t₀ * e * t₀⁻¹ * e⁻¹) * (t₀ * e' * t₀⁻¹ * e'⁻¹) := by rw [← hc]; group
  have hθinv : ∀ e ∈ E, t₀ * e⁻¹ * t₀⁻¹ * (e⁻¹)⁻¹ = (t₀ * e * t₀⁻¹ * e⁻¹)⁻¹ := by
    intro e he
    have h1 := hθmul e he e⁻¹ (E.inv_mem he)
    rw [mul_inv_cancel] at h1
    have h2 : t₀ * (1 : G) * t₀⁻¹ * (1 : G)⁻¹ = 1 := by group
    rw [h2] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  have hker : ∀ e ∈ E, t₀ * e * t₀⁻¹ * e⁻¹ = 1 → e ∈ Z := by
    intro e he h1
    refine hEc e he fun t ht => ?_
    have h2 : t₀ * e = e * t₀ := by
      have := mul_inv_eq_one.mp h1
      calc t₀ * e = t₀ * e * t₀⁻¹ * t₀ := by group
        _ = e * t₀ := by rw [this]
    rcases hcov t ht with ⟨p, hp, q, hq, rfl⟩ | ⟨p, hp, q, hq, rfl⟩
    · have hqe := hQab q hq e (hEQ he)
      calc p * q * e = p * (q * e) := by group
        _ = p * (e * q) := by rw [hqe]
        _ = (p * e) * q := by group
        _ = (e * p) * q := by rw [hDE p hp e he]
        _ = e * (p * q) := by group
    · have hqe := hQab q hq e (hEQ he)
      calc t₀ * p * q * e = t₀ * p * (q * e) := by group
        _ = t₀ * p * (e * q) := by rw [hqe]
        _ = t₀ * (p * e) * q := by group
        _ = t₀ * (e * p) * q := by rw [hDE p hp e he]
        _ = (t₀ * e) * p * q := by group
        _ = (e * t₀) * p * q := by rw [h2]
        _ = e * (t₀ * p * q) := by group
  have key : ∀ x ∈ Subgroup.centralizer (V : Set G), x ∉ V →
      ∀ y ∈ Subgroup.centralizer (V : Set G), y ∉ V → x⁻¹ * y ∈ V := by
    intro x hx hxV y hy hyV
    obtain ⟨v₁, hv₁, e₁, he₁, rfl⟩ := hQVE x hx
    obtain ⟨v₂, hv₂, e₂, he₂, rfl⟩ := hQVE y hy
    have hne : ∀ e ∈ E, ∀ v ∈ V, v * e ∉ V → t₀ * e * t₀⁻¹ * e⁻¹ ≠ 1 := by
      intro e he v hv hve h1
      exact hve (V.mul_mem hv (hZV (hker e he h1)))
    have h1 := hne e₁ he₁ v₁ hv₁ hxV
    have h2 := hne e₂ he₂ v₂ hv₂ hyV
    have h3 := eq_of_card_two hZcard (hθZ e₁ he₁) (hθZ e₂ he₂) h1 h2
    have h4 : t₀ * (e₁⁻¹ * e₂) * t₀⁻¹ * (e₁⁻¹ * e₂)⁻¹ = 1 := by
      rw [hθmul e₁⁻¹ (E.inv_mem he₁) e₂ he₂, hθinv e₁ he₁, ← h3, inv_mul_cancel]
    have h5 : e₁⁻¹ * e₂ ∈ V := hZV (hker _ (E.mul_mem (E.inv_mem he₁) he₂) h4)
    have h6 : (v₁ * e₁)⁻¹ * (v₂ * e₂) = (v₁⁻¹ * v₂) * (e₁⁻¹ * e₂) := by
      have hc : e₁⁻¹ * v₂ = v₂ * e₁⁻¹ := by
        have := Subgroup.mem_centralizer_iff.mp (hEQ (E.inv_mem he₁)) v₂ hv₂
        exact this.symm
      calc (v₁ * e₁)⁻¹ * (v₂ * e₂) = e₁⁻¹ * (v₁⁻¹ * v₂) * e₂ := by group
        _ = (v₁⁻¹ * v₂) * (e₁⁻¹ * e₂) := by
          have hc' : e₁⁻¹ * (v₁⁻¹ * v₂) = (v₁⁻¹ * v₂) * e₁⁻¹ :=
            (Subgroup.mem_centralizer_iff.mp (hEQ (E.inv_mem he₁)) _
              (V.mul_mem (V.inv_mem hv₁) hv₂)).symm
          rw [hc']; group
    rw [h6]
    exact V.mul_mem (V.mul_mem (V.inv_mem hv₁) hv₂) h5
  by_cases hQV : Subgroup.centralizer (V : Set G) ≤ V
  · rw [Subgroup.relIndex_eq_one.mpr hQV]
    norm_num
  · obtain ⟨q₁, hq₁Q, hq₁V⟩ := Set.not_subset.mp hQV
    have : V.relIndex (Subgroup.centralizer (V : Set G)) = 2 := by
      refine Subgroup.relIndex_eq_two_iff'.mpr
        ⟨q₁⁻¹, (Subgroup.centralizer (V : Set G)).inv_mem hq₁Q, fun b hb => ?_⟩
      by_cases hbV : b ∈ V
      · right
        refine ⟨hbV, fun h => hq₁V ?_⟩
        have h1 : q₁⁻¹ ∈ V := by simpa using V.mul_mem h (V.inv_mem hbV)
        simpa using V.inv_mem h1
      · left
        exact ⟨key q₁ hq₁Q hq₁V b hb hbV, hbV⟩
    rw [this]

end CFSG.Quasithin.H13.GM22
