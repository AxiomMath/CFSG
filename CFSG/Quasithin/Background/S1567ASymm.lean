module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

namespace S1567

open CFSG.Open CFSG.LieType.BorelTits

instance instNormalPCoreS1567A (p : ℕ) (X : Type*) [Group X] : (pCore p X).Normal :=
  pCore_normal p

private def swapA : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private def swapB : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private theorem perm3_conj_injective :
    ∀ g h : Equiv.Perm (Fin 3), (∀ x : Equiv.Perm (Fin 3), g * x * g⁻¹ = h * x * h⁻¹) → g = h := by
  decide

private theorem perm3_eq_word : ∀ x : Equiv.Perm (Fin 3), x = 1 ∨ x = swapA ∨ x = swapB ∨
    x = swapA * swapB ∨ x = swapB * swapA ∨ x = swapA * swapB * swapA := by
  decide

private theorem perm3_exists_conj : ∀ a b : Equiv.Perm (Fin 3),
    a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b →
      ∃ g : Equiv.Perm (Fin 3), g * swapA * g⁻¹ = a ∧ g * swapB * g⁻¹ = b := by
  decide +kernel

private theorem perm3_exists_inner (θ : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3))
    (hθ : Function.Injective θ) : ∃ g : Equiv.Perm (Fin 3), ∀ x, θ x = g * x * g⁻¹ := by
  have hA : swapA ≠ 1 := by decide
  have hB : swapB ≠ 1 := by decide
  have hAB : swapA ≠ swapB := by decide
  have hAA : swapA * swapA = 1 := by decide
  have hBB : swapB * swapB = 1 := by decide
  obtain ⟨g, hgA, hgB⟩ := perm3_exists_conj (θ swapA) (θ swapB)
    ⟨by rw [← map_mul, hAA, map_one], by rw [← map_mul, hBB, map_one],
      fun h => hA (hθ (h.trans θ.map_one.symm)), fun h => hB (hθ (h.trans θ.map_one.symm)),
      fun h => hAB (hθ h)⟩
  refine ⟨g, fun x => ?_⟩
  rcases perm3_eq_word x with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hgA.symm
  · exact hgB.symm
  · rw [map_mul, ← hgA, ← hgB]
    group
  · rw [map_mul, ← hgA, ← hgB]
    group
  · rw [map_mul, map_mul, ← hgA, ← hgB]
    group

private theorem perm3Sq_exists_order_three :
    ∀ x : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3), x ≠ 1 →
      ∃ g : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
        (x * (g * x * g⁻¹)) ^ 3 = 1 ∧ x * (g * x * g⁻¹) ≠ 1 := by
  decide +kernel

private theorem perm3Sq_eq_bot_of_normal_isPGroup
    (N : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) [N.Normal] (hN : IsPGroup 2 N) :
    N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨g, h3, h1⟩ := perm3Sq_exists_order_three x hx1
  have hy : x * (g * x * g⁻¹) ∈ N := N.mul_mem hx (Subgroup.Normal.conj_mem inferInstance x hx g)
  obtain ⟨k, hk⟩ := hN ⟨_, hy⟩
  have hk' : (x * (g * x * g⁻¹)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h := pow_gcd_eq_one.mpr ⟨hk', h3⟩
  rw [hcop.gcd_eq_one, pow_one] at h
  exact h1 h

private theorem exists_extension_of_perm3 {K : Type*} [Group K] (C : Subgroup K) [C.Normal]
    (ρ : ↥C →* Equiv.Perm (Fin 3)) (hρ : Function.Surjective ρ)
    (hker : ∀ (k : K) (c : ↥C), ρ c = 1 → ρ (MulAut.conjNormal k c) = 1) :
    ∃ ρ' : K →* Equiv.Perm (Fin 3), ∀ c : ↥C, ρ' (c : K) = ρ c := by
  have hθ : ∀ k : K, ∃ g : Equiv.Perm (Fin 3),
      ∀ c : ↥C, ρ (MulAut.conjNormal k c) = g * ρ c * g⁻¹ := by
    intro k
    let δ : ↥C →* Equiv.Perm (Fin 3) := ρ.comp (MulAut.conjNormal k).toMonoidHom
    have hδ : ρ.ker ≤ δ.ker := fun c hc => hker k c hc
    let θ : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3) :=
      ρ.liftOfRightInverse (Function.surjInv hρ) (Function.rightInverse_surjInv hρ) ⟨δ, hδ⟩
    have hθc : ∀ c : ↥C, θ (ρ c) = ρ (MulAut.conjNormal k c) := fun c =>
      MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨δ, hδ⟩ c
    have hinj : Function.Injective θ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      obtain ⟨c, rfl⟩ := hρ y
      rw [hθc] at hy
      have h := hker k⁻¹ _ hy
      have hc : MulAut.conjNormal k⁻¹ (MulAut.conjNormal k c) = c := by
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
      rwa [hc] at h
    obtain ⟨g, hg⟩ := perm3_exists_inner θ hinj
    exact ⟨g, fun c => by rw [← hθc, hg]⟩
  choose g hg using hθ
  have hmul : ∀ k₁ k₂ : K, g (k₁ * k₂) = g k₁ * g k₂ := by
    intro k₁ k₂
    apply perm3_conj_injective
    intro x
    obtain ⟨c, rfl⟩ := hρ x
    calc g (k₁ * k₂) * ρ c * (g (k₁ * k₂))⁻¹ = ρ (MulAut.conjNormal (k₁ * k₂) c) := (hg _ c).symm
      _ = ρ (MulAut.conjNormal k₁ (MulAut.conjNormal k₂ c)) := by
        rw [map_mul, MulAut.mul_apply]
      _ = g k₁ * ρ (MulAut.conjNormal k₂ c) * (g k₁)⁻¹ := hg _ _
      _ = g k₁ * (g k₂ * ρ c * (g k₂)⁻¹) * (g k₁)⁻¹ := by rw [hg k₂ c]
      _ = g k₁ * g k₂ * ρ c * (g k₁ * g k₂)⁻¹ := by group
  refine ⟨MonoidHom.mk' g hmul, fun c => ?_⟩
  show g (c : K) = ρ c
  apply perm3_conj_injective
  intro x
  obtain ⟨c', rfl⟩ := hρ x
  have hconj : MulAut.conjNormal (c : K) c' = c * c' * c⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  calc g (c : K) * ρ c' * (g (c : K))⁻¹ = ρ (MulAut.conjNormal (c : K) c') := (hg _ c').symm
    _ = ρ c * ρ c' * (ρ c)⁻¹ := by rw [hconj]; simp

theorem oTwoQuot_equiv_S3S3 {K : Type*} [Group K] [Finite K] (C : Subgroup K) [C.Normal]
    (hK : Nonempty (K ⧸ C ≃* Equiv.Perm (Fin 3)))
    (hC : Nonempty (↥C ⧸ CFSG.Open.pCore 2 ↥C ≃* Equiv.Perm (Fin 3))) :
    Nonempty (K ⧸ CFSG.Open.pCore 2 K ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := hC
  let ρ : ↥C →* Equiv.Perm (Fin 3) := e₂.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥C))
  have hρs : Function.Surjective ρ := e₂.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρker : ∀ c : ↥C, ρ c = 1 ↔ c ∈ pCore 2 ↥C := by
    intro c
    change e₂ (QuotientGroup.mk' (pCore 2 ↥C) c) = 1 ↔ _
    rw [map_eq_one_iff _ e₂.injective]
    exact QuotientGroup.eq_one_iff c
  have hker : ∀ (k : K) (c : ↥C), ρ c = 1 → ρ (MulAut.conjNormal k c) = 1 := by
    intro k c hc
    rw [hρker] at hc ⊢
    have hchar : (pCore 2 ↥C).Characteristic := pCore_characteristic 2
    exact Subgroup.characteristic_iff_map_le.mp hchar (MulAut.conjNormal k) ⟨c, hc, rfl⟩
  obtain ⟨ρ', hρ'⟩ := exists_extension_of_perm3 C ρ hρs hker
  let π₁ : K →* Equiv.Perm (Fin 3) := e₁.toMonoidHom.comp (QuotientGroup.mk' C)
  let Φ : K →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := π₁.prod ρ'
  have hπ₁ : ∀ k : K, π₁ k = 1 ↔ k ∈ C := by
    intro k
    change e₁ (QuotientGroup.mk' C k) = 1 ↔ _
    rw [map_eq_one_iff _ e₁.injective]
    exact QuotientGroup.eq_one_iff k
  have hπ₁C : ∀ c : ↥C, π₁ (c : K) = 1 := fun c => (hπ₁ _).2 c.2
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    obtain ⟨k, hk⟩ := e₁.surjective.comp (QuotientGroup.mk'_surjective C) a
    obtain ⟨c, hc⟩ := hρs ((ρ' k)⁻¹ * b)
    refine ⟨k * c, Prod.ext ?_ ?_⟩
    · show π₁ (k * c) = a
      rw [map_mul, hπ₁C, mul_one]
      exact hk
    · show ρ' (k * c) = b
      rw [map_mul, hρ', hc]
      simp
  have hΦker : Φ.ker = pCoreOf 2 C := by
    ext k
    constructor
    · intro hk
      have hk1 : π₁ k = 1 := congrArg Prod.fst hk
      have hk2 : ρ' k = 1 := congrArg Prod.snd hk
      have hkC : k ∈ C := (hπ₁ k).1 hk1
      refine ⟨⟨k, hkC⟩, (hρker _).1 ?_, rfl⟩
      rw [← hρ' ⟨k, hkC⟩]
      exact hk2
    · rintro ⟨c, hcQ, rfl⟩
      refine Prod.ext (hπ₁C c) ?_
      show ρ' (c : K) = 1
      rw [hρ']
      exact (hρker c).2 hcQ
  have hle1 : pCore 2 K ≤ Φ.ker := by
    have : ((pCore 2 K).map Φ).Normal := Subgroup.Normal.map inferInstance Φ hΦsurj
    exact (Subgroup.map_eq_bot_iff _).mp
      (perm3Sq_eq_bot_of_normal_isPGroup _ ((pCore_isPGroup (G := K) 2).map Φ))
  have hle2 : Φ.ker ≤ pCore 2 K := by
    refine le_pCore 2 inferInstance ?_
    rw [hΦker]
    exact pCoreOf_isPGroup 2 C
  have hEq : pCore 2 K = Φ.ker := le_antisymm hle1 hle2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hEq).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hΦsurj)⟩

end S1567

end CFSG.Quasithin
