module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKLinA

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open Matrix

theorem natural_sum_embedding {Γ : Type*} [Group Γ] {m n j k : ℕ} (hm : 2 ≤ m) (hn : n < 2 * m)
    (hk : 0 < k) (ρ : Γ →* GL (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (σ : Γ →* GL (Fin n) (ZMod 2))
    (ϑ : (Fin k → Fin m → ZMod 2) →+ (Fin j → Fin n → ZMod 2)) (hϑ : Function.Injective ϑ)
    (hequi : ∀ (γ : Γ) (t : Fin k → Fin m → ZMod 2) (i : Fin j),
      ϑ (fun s => (ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec (t s)) i =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (ϑ t i)) :
    ∃ (Φ₀ : (Fin m → ZMod 2) →+ (Fin n → ZMod 2)) (i₀ : Fin j) (s₀ : Fin k),
      Function.Injective Φ₀ ∧ (∀ x, ϑ (Pi.single s₀ x) i₀ = Φ₀ x) ∧
        ∀ (t : Fin k → Fin m → ZMod 2) (i : Fin j), ϑ t i ∈ Φ₀.range := by
  classical
  let Φ : Fin j → Fin k → (Fin m → ZMod 2) →+ (Fin n → ZMod 2) := fun i s =>
    (Pi.evalAddMonoidHom (fun _ : Fin j => Fin n → ZMod 2) i).comp
      (ϑ.comp (AddMonoidHom.single (fun _ : Fin k => Fin m → ZMod 2) s))
  have hΦ : ∀ i s x, Φ i s x = ϑ (Pi.single s x) i := fun i s x => rfl
  have hsingle : ∀ (γ : Γ) (s : Fin k) (x : Fin m → ZMod 2),
      (fun s' => (ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec
        ((Pi.single s x : Fin k → Fin m → ZMod 2) s')) =
        (Pi.single s ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) :
          Fin k → Fin m → ZMod 2) := by
    intro γ s x
    funext s'
    by_cases h : s' = s
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hΦequi : ∀ i s (γ : Γ) x,
      Φ i s ((ρ γ : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec x) =
        (σ γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (Φ i s x) := by
    intro i s γ x
    rw [hΦ, hΦ, ← hsingle γ s x]
    exact hequi γ _ i
  have hsome : ∃ i s, Φ i s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ t, ϑ t = 0 := by
      intro t
      have ht : t = ∑ s, (Pi.single s (t s) : Fin k → Fin m → ZMod 2) :=
        (Finset.univ_sum_single t).symm
      funext i
      rw [ht, map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [← hΦ, hcon i s]
      rfl
    have h1 : (Pi.single (⟨0, hk⟩ : Fin k)
        (Pi.single (⟨0, by omega⟩ : Fin m) (1 : ZMod 2) : Fin m → ZMod 2) :
        Fin k → Fin m → ZMod 2) = 0 := by
      apply hϑ
      rw [map_zero]
      exact hzero _
    have h2 := congrFun (congrFun h1 ⟨0, hk⟩) ⟨0, by omega⟩
    simp at h2
  obtain ⟨i₀, s₀, h0⟩ := hsome
  have hall : ∀ i s, Φ i s = 0 ∨ Φ i s = Φ i₀ s₀ := by
    intro i s
    rcases natural_hom_zero_or_eq hm hn ρ hρ σ (Φ i s) (Φ i₀ s₀) (hΦequi i s) (hΦequi i₀ s₀) with
      h | h | h
    · exact Or.inl h
    · exact absurd h h0
    · exact Or.inr h
  refine ⟨Φ i₀ s₀, i₀, s₀, natural_hom_injective ρ hρ σ _ (hΦequi i₀ s₀) h0, fun x => rfl, ?_⟩
  intro t i
  have ht : t = ∑ s, (Pi.single s (t s) : Fin k → Fin m → ZMod 2) :=
    (Finset.univ_sum_single t).symm
  have hsum : ϑ t i = ∑ s, Φ i s (t s) := by
    conv_lhs => rw [ht, map_sum]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun s _ => (hΦ i s (t s)).symm
  rw [hsum]
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  rcases hall i s with h | h
  · rw [h]
    exact AddSubgroup.zero_mem _
  · rw [h]
    exact ⟨t s, rfl⟩

end CFSG.Quasithin.H13.Ch4.NSB
