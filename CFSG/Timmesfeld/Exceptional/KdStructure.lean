module

public import CFSG.Timmesfeld.Exceptional.CaseTwo

public section

namespace CFSG.Timmesfeld.Moufang

open scoped commutatorElement

variable {G : Type*} [Group G] {D : Set G}

theorem eq_mul_of_commute_of_noPlane (hD : IsRootInvolutionSet D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {a e f : G} (ha : a ∈ D) (he : e ∈ D) (hf : f ∈ D)
    (hae : Commute a e) (haf : Commute a f) (hef : Commute e f) (hea : e ≠ a) (hfa : f ≠ a)
    (hfe : f ≠ e) : f = a * e := by
  by_contra hne
  have h1 : a * e ∈ D := hNP a ha e he hae (Ne.symm hea)
  have h2 : a * f ∈ D := hNP a ha f hf haf (Ne.symm hfa)
  have h3 : e * f ∈ D := hNP e he f hf hef (Ne.symm hfe)
  have h4 : a * e * f ∈ D := by
    rw [mul_assoc]
    refine hNP a ha _ h3 (hae.mul_right haf) fun h => hne ?_
    calc f = e * (e * f) := by rw [← mul_assoc, hD.mul_self_eq_one he, one_mul]
      _ = e * a := by rw [← h]
      _ = a * e := hae.eq.symm
  exact hPl a ha e he f hf hae haf hef (Ne.symm hea) hfa hfe hne h1 h2 h3 h4

theorem NoLevi.centralizer_cases (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {a e f : G} (ha : a ∈ D) (he : e ∈ D) (hf : f ∈ D)
    (hae : Commute a e) (haf : Commute a f) (hea : e ≠ a) (hfa : f ≠ a) :
    f = e ∨ f = a * e ∨ (orderOf (e * f) = 4 ∧ (e * f) ^ 2 = a) := by
  by_cases hef : Commute e f
  · by_cases hfe : f = e
    · exact .inl hfe
    · exact .inr (.inl (eq_mul_of_commute_of_noPlane hD hNP hPl ha he hf hae haf hef hea hfa hfe))
  · have h4 := hNL.orderOf_eq_four hD ha he hf hae haf hef
    have heD : a * e ∈ D := hNP a ha e he hae (Ne.symm hea)
    exact .inr (.inr ⟨h4, eq_of_noPolar_noPlane hD hconj hNP hPl ha he hf hae heD haf h4⟩)

theorem NoLevi.commutatorElement_mem (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {a e f : G} (ha : a ∈ D) (he : e ∈ D) (hf : f ∈ D)
    (hae : Commute a e) (haf : Commute a f) : ⁅e, f⁆ = 1 ∨ ⁅e, f⁆ = a := by
  have he2 := hD.mul_self_eq_one he
  have hf2 := hD.mul_self_eq_one hf
  have hcomm : ⁅e, f⁆ = (e * f) ^ 2 := by
    rw [commutatorElement_def, pow_two, hD.inv_eq he, hD.inv_eq hf]
    simp only [mul_assoc]
  have hone : Commute e f → ⁅e, f⁆ = 1 := fun h => by
    rw [hcomm]; exact (commute_iff_mul_sq_eq_one he2 hf2).1 h
  by_cases hea : e = a
  · subst hea; exact .inl (hone haf)
  by_cases hfa : f = a
  · subst hfa; exact .inl (hone hae.symm)
  rcases NoLevi.centralizer_cases hD hconj hNL hNP hPl ha he hf hae haf hea hfa with
    rfl | rfl | ⟨-, h⟩
  · exact .inl (hone (Commute.refl _))
  · exact .inl (hone (hae.symm.mul_right (Commute.refl e)))
  · exact .inr (hcomm.trans h)

theorem commute_of_mem_closure_centralizer {a k : G}
    (hk : k ∈ Subgroup.closure {x | x ∈ D ∧ Commute x a}) : Commute a k := by
  have : k ∈ Subgroup.centralizer ({a} : Set G) :=
    (Subgroup.closure_le _).2 (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 hx.2) hk
  exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm

theorem NoLevi.commutator_le_zpowers (hD : IsRootInvolutionSet D)
    (hconj : ∀ g : G, ∀ x ∈ D, g * x * g⁻¹ ∈ D) (hNL : NoLevi D) (hNP : NoPolar D)
    (hPl : ExcNoPlane D) {a : G} (ha : a ∈ D) :
    ⁅Subgroup.closure {x | x ∈ D ∧ Commute x a}, Subgroup.closure {x | x ∈ D ∧ Commute x a}⁆ ≤
      Subgroup.zpowers a := by
  set K := Subgroup.closure {x | x ∈ D ∧ Commute x a}
  have hcen : ∀ n ∈ Subgroup.zpowers a, ∀ k ∈ K, k * n * k⁻¹ = n := by
    rintro _ ⟨m, rfl⟩ k hk
    have := ((commute_of_mem_closure_centralizer hk).zpow_left m).eq
    simp only [this.symm, mul_inv_cancel_right]
  have hstep : ∀ g₁ ∈ K, (∀ s ∈ {x | x ∈ D ∧ Commute x a}, ⁅g₁, s⁆ ∈ Subgroup.zpowers a) →
      ∀ g₂ ∈ K, ⁅g₁, g₂⁆ ∈ Subgroup.zpowers a := by
    intro g₁ hg₁ hgen g₂ hg₂
    induction hg₂ using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
      have e : ⁅g₁, x * y⁆ = ⁅g₁, x⁆ * (x * ⁅g₁, y⁆ * x⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e, hcen _ ihy x hx]
      exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
      have e : ⁅g₁, x⁻¹⁆ = x⁻¹ * ⁅g₁, x⁆⁻¹ * x⁻¹⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e, hcen _ (Subgroup.inv_mem _ ihx) _ (Subgroup.inv_mem _ hx)]
      exact Subgroup.inv_mem _ ihx
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  refine hstep g₁ hg₁ ?_ g₂ hg₂
  intro s hs
  have hs' : ⁅s, g₁⁆ ∈ Subgroup.zpowers a := by
    refine hstep s (Subgroup.subset_closure hs) (fun t ht => ?_) g₁ hg₁
    rcases NoLevi.commutatorElement_mem hD hconj hNL hNP hPl ha hs.1 ht.1 hs.2.symm ht.2.symm
      with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers a
  have e : ⁅g₁, s⁆ = ⁅s, g₁⁆⁻¹ := by simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.inv_mem _ hs'

end CFSG.Timmesfeld.Moufang
