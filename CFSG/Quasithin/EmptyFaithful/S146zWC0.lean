module

public import CFSG.Quasithin.Background.C2PushY

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Quasithin.C2Push CFSG.QuasithinUnique

variable {K : Type} [Group K] [Finite K]

theorem card_centralizer_odd {X S : Subgroup K} (hX : X.Normal) (hO : CFSG.Open.pCore 2 K = ⊥)
    (hS : IsPGroup 2 S) (hK : ∀ k : K, ∃ x ∈ X, ∃ s ∈ S, k = x * s) :
    ¬ 2 ∣ Nat.card (Subgroup.centralizer (X : Set K)) := by
  obtain ⟨T, hT, hST⟩ := exists_isSylowTwoOf_ge_of_isPGroup (le_top : S ≤ ⊤) hS
  set E : Subgroup K := Subgroup.centralizer (X : Set K) with hE
  have hkey : ∀ (k e : K), e ∈ E → k * e * k⁻¹ ∈ E := by
    intro k e he
    rw [hE, Subgroup.mem_centralizer_iff] at he ⊢
    intro x hx
    have hx' : k⁻¹ * x * k ∈ X := by simpa using hX.conj_mem x hx k⁻¹
    have h1 := he _ hx'
    calc x * (k * e * k⁻¹) = k * ((k⁻¹ * x * k) * e) * k⁻¹ := by group
      _ = k * (e * (k⁻¹ * x * k)) * k⁻¹ := by rw [h1]
      _ = (k * e * k⁻¹) * x := by group
  have hEn : ∀ k : K, k ∈ Subgroup.normalizer (E : Set K) := by
    intro k
    rw [Subgroup.mem_normalizer_iff]
    intro e
    exact ⟨hkey k e, fun h => by simpa [mul_assoc] using hkey k⁻¹ _ h⟩
  have hTE : IsSylowTwoOf (T ⊓ E) E :=
    A4.isSylowTwoOf_inf_normal hT le_top (fun k _ => hEn k)
  have hnorm : ∀ k : K, k ∈ Subgroup.normalizer ((T ⊓ E : Subgroup K) : Set K) := by
    intro k
    obtain ⟨x, hxX, s, hsS, rfl⟩ := hK k
    refine Subgroup.mul_mem _ ?_ ?_
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      have hcomm : ∀ y ∈ E, x * y * x⁻¹ = y := by
        intro y hy
        rw [hE, Subgroup.mem_centralizer_iff] at hy
        rw [hy x hxX]
        group
      constructor
      · intro hy
        rw [hcomm y hy.2]
        exact hy
      · intro hy
        have hyE : y ∈ E := by
          have := hkey x⁻¹ _ hy.2
          simpa [mul_assoc] using this
        rw [hcomm y hyE] at hy
        exact hy
    · exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (hST hsS), hEn s⟩
  have hbot : T ⊓ E = ⊥ := by
    have hN : (T ⊓ E).Normal :=
      ⟨fun y hy k => (Subgroup.mem_normalizer_iff.mp (hnorm k) y).mp hy⟩
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hN hTE.2.1
    rw [hO] at hle
    exact le_bot_iff.mp hle
  have h := hTE.2.2
  rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
  exact h

theorem le_centralizer_of_normal {A₁ A₂ D : Subgroup K} (h₁ : CFSG.IsComponent A₁)
    (h₂ : CFSG.IsComponent A₂) (hD : D.Normal) (hD₁ : ¬ A₁ ≤ D) (hD₂ : ¬ A₂ ≤ D) :
    D ≤ Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup K) : Set K) := by
  have e1 : ⁅A₁, D⁆ = ⊥ := (CFSG.LocalCores.component_normal_subgroup h₁ hD).resolve_left hD₁
  have e2 : ⁅A₂, D⁆ = ⊥ := (CFSG.LocalCores.component_normal_subgroup h₂ hD).resolve_left hD₂
  rw [Subgroup.le_centralizer_iff]
  exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp e1)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp e2)

end CFSG.Quasithin.S146zW
