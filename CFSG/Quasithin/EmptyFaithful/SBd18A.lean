module

public import CFSG.Quasithin.EmptyFaithful.SBd17Syl

public section

namespace CFSG.Quasithin.SBd18

variable {G : Type} [Group G]

theorem mem_sup_zpowers_cases [Finite G] {L : Subgroup G} {σ : G} (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    (hN : σ ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L ⊔ Subgroup.zpowers σ) :
    x ∈ L ∨ x * σ ∈ L := by
  have hle : Subgroup.zpowers σ ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr hN
  rw [sup_comm] at hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers σ) L hle
  have hx' : x ∈ ((Subgroup.zpowers σ ⊔ L : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨y, hy, l, hl, rfl⟩ := hx'
  rcases SBd14.eq_one_or_self_of_mem_zpowers_involution hσ1 hσ2 hy with rfl | rfl
  · left
    simpa using hl
  · right
    have h1 : y * l * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp hN l).mp hl
      have e : y * l * y⁻¹ = y * l * y := by
        have : y⁻¹ = y := eq_inv_of_mul_eq_one_left hσ2 |>.symm
        rw [this]
      rwa [e] at this
    exact h1

theorem not_conj_into_V₁ [Finite G] {V₁ L F : Subgroup G} {σ : G}
    (hV₄ : Nat.card ↥V₁ = 4) (hVsq : ∀ v ∈ V₁, v * v = 1) (hV₁L : V₁ ≤ L)
    (hVcL : ∀ l ∈ L, ∀ v ∈ V₁, l * v = v * l)
    (hσ2 : σ * σ = 1) (hσL : σ ∉ L) (hσV : ∀ v ∈ V₁, σ * v = v * σ)
    (hσN : σ ∈ Subgroup.normalizer (L : Set G))
    (hcl : Subgroup.centralizer (V₁ : Set G) = L ⊔ Subgroup.zpowers σ)
    (hK1 : ∀ v ∈ V₁, v ≠ 1 → Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (V₁ : Set G))
    (hTI : ∀ (g x : G), x ∈ V₁ → x ≠ 1 → g⁻¹ * x * g ∈ V₁ → g ∈ Subgroup.normalizer (V₁ : Set G))
    (hFL : F ≤ L) (hF3 : IsPGroup 3 ↥F) (hFσ : ∀ x ∈ F, σ * x = x * σ)
    (hFC : ∀ l ∈ L, (∀ x ∈ F, l * x = x * l) → ∃ f₀ ∈ F, ∃ v ∈ V₁, l = f₀ * v) :
    ∀ g : G, g⁻¹ * σ * g ∉ V₁ := by
  classical
  intro g hv
  have hσ1 : σ ≠ 1 := fun h => hσL (h ▸ L.one_mem)
  set v : G := g⁻¹ * σ * g with hvdef
  have hv1 : v ≠ 1 := by
    intro h
    apply hσ1
    calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      _ = 1 := by rw [← hvdef, h]; group
  set A : Subgroup G := V₁.map (MulAut.conj g).toMonoidHom with hA
  have hmemA : ∀ x : G, x ∈ A ↔ g⁻¹ * x * g ∈ V₁ := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      simpa [e] using hy
    · intro hx
      refine ⟨g⁻¹ * x * g, hx, ?_⟩
      simp [mul_assoc]
  have hA4 : Nat.card ↥A = 4 := by
    rw [hA, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV₄]
  have hAsq : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    have h1 := hVsq _ ((hmemA a).mp ha)
    calc a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hσA : σ ∈ A := (hmemA σ).mpr hv
  have hN : ∀ x ∈ V₁, ∀ a ∈ A, x * a * x⁻¹ ∈ A := by
    intro x hx a ha
    have hxc : g⁻¹ * x * g ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hσV x hx
      calc g⁻¹ * x * g * v = g⁻¹ * (x * σ) * g := by rw [hvdef]; group
        _ = g⁻¹ * (σ * x) * g := by rw [← h1]
        _ = v * (g⁻¹ * x * g) := by rw [hvdef]; group
    have hxN : g⁻¹ * x * g ∈ Subgroup.normalizer (V₁ : Set G) := hK1 v hv hv1 hxc
    rw [hmemA] at ha ⊢
    have := (Subgroup.mem_normalizer_iff.mp hxN _).mp ha
    have e : g⁻¹ * x * g * (g⁻¹ * a * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * a * x⁻¹) * g := by group
    rwa [e] at this
  by_cases hAV : A ⊓ V₁ = ⊥
  ·
    have hcomm := SBd16.commute_of_normalizes hV₄ hA4 hTI (by rw [inf_comm]; exact hAV) hN
    have hAcl : ∀ a ∈ A, a ∈ L ⊔ Subgroup.zpowers σ := by
      intro a ha
      rw [← hcl, Subgroup.mem_centralizer_iff]
      intro x hx
      exact hcomm x hx a ha
    set F' : Subgroup G := F.map (MulAut.conj g⁻¹).toMonoidHom with hF'
    have hmemF' : ∀ y : G, y ∈ F' ↔ g * y * g⁻¹ ∈ F := by
      intro y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [mul_assoc] using hx
      · intro hy
        refine ⟨g * y * g⁻¹, hy, ?_⟩
        simp [mul_assoc]
    have hF'odd : ∀ y ∈ F', Odd (orderOf y) := by
      intro y hy
      have hx : g * y * g⁻¹ ∈ F := (hmemF' y).mp hy
      obtain ⟨k, hk⟩ := hF3 ⟨g * y * g⁻¹, hx⟩
      have hk' : (g * y * g⁻¹) ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have hyk : y ^ (3 ^ k) = 1 := by
        have : g * y ^ (3 ^ k) * g⁻¹ = 1 := by rw [← conj_pow]; simpa using hk'
        calc y ^ (3 ^ k) = g⁻¹ * (g * y ^ (3 ^ k) * g⁻¹) * g := by group
          _ = 1 := by rw [this]; group
      exact Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hyk)
    have hstar : ∀ b ∈ V₁, ∀ f' ∈ F', b * f' = f' * b := by
      refine SBd16.centralizes_of_centralizes_nonidentity hV₄ hVsq hTI ?_ hv hv1 ?_
      · intro K hK y hy
        exact hK y hy (hF'odd y hy)
      · intro f' hf'
        have hx : g * f' * g⁻¹ ∈ F := (hmemF' f').mp hf'
        have h1 := hFσ _ hx
        calc v * f' = g⁻¹ * (σ * (g * f' * g⁻¹)) * g := by rw [hvdef]; group
          _ = g⁻¹ * ((g * f' * g⁻¹) * σ) * g := by rw [h1]
          _ = f' * v := by rw [hvdef]; group
    have hAF : ∀ a ∈ A, ∀ x ∈ F, a * x = x * a := by
      intro a ha x hx
      have hb : g⁻¹ * a * g ∈ V₁ := (hmemA a).mp ha
      have hx' : g⁻¹ * x * g ∈ F' := (hmemF' _).mpr (by simpa [mul_assoc] using hx)
      have h1 := hstar _ hb _ hx'
      calc a * x = g * ((g⁻¹ * a * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
        _ = x * a := by group
    obtain ⟨b, hbA, hb1, hbσ⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ σ := by
      by_contra hcon
      push Not at hcon
      have hle : A ≤ Subgroup.zpowers σ := by
        intro a ha
        by_cases ha1 : a = 1
        · rw [ha1]; exact Subgroup.one_mem _
        · rw [hcon a ha ha1]; exact Subgroup.mem_zpowers σ
      have h1 := Subgroup.card_le_of_le hle
      have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
      rw [hA4, Nat.card_zpowers, hord] at h1
      omega
    obtain ⟨a', ha'A, ha'1, ha'L⟩ : ∃ a' ∈ A, a' ≠ 1 ∧ a' ∈ L := by
      rcases mem_sup_zpowers_cases hσ1 hσ2 hσN (hAcl b hbA) with h | h
      · exact ⟨b, hbA, hb1, h⟩
      · refine ⟨b * σ, A.mul_mem hbA hσA, ?_, h⟩
        intro h1
        apply hbσ
        have : b = σ⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact (eq_inv_of_mul_eq_one_left hσ2).symm
    obtain ⟨f₀, hf₀, v', hv', hfv⟩ := hFC a' ha'L (fun x hx => hAF a' ha'A x hx)
    have hsq : a' * a' = 1 := hAsq a' ha'A
    have hf₀v' : f₀ * v' = v' * f₀ := hVcL f₀ (hFL hf₀) v' hv'
    have hf₀2 : f₀ * f₀ = 1 := by
      have h1 : a' * a' = f₀ * f₀ * (v' * v') := by
        rw [hfv]
        calc f₀ * v' * (f₀ * v') = f₀ * (v' * f₀) * v' := by group
          _ = f₀ * (f₀ * v') * v' := by rw [hf₀v']
          _ = f₀ * f₀ * (v' * v') := by group
      rw [hsq, hVsq v' hv', mul_one] at h1
      exact h1.symm
    have hf₀1 : f₀ = 1 := by
      obtain ⟨k, hk⟩ := hF3 ⟨f₀, hf₀⟩
      have hk' : f₀ ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨m, hm⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
      rw [hm, pow_succ, pow_mul, pow_two, hf₀2, one_pow, one_mul] at hk'
      exact hk'
    have ha'V : a' ∈ V₁ := by
      rw [hfv, hf₀1, one_mul]
      exact hv'
    have : a' ∈ A ⊓ V₁ := ⟨ha'A, ha'V⟩
    rw [hAV, Subgroup.mem_bot] at this
    exact ha'1 this
  ·
    obtain ⟨y, hyAV, hy1⟩ : ∃ y ∈ A ⊓ V₁, y ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hAV ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    have hgN : g ∈ Subgroup.normalizer (V₁ : Set G) := hTI g y hyAV.2 hy1 ((hmemA y).mp hyAV.1)
    have hσV₁ : σ ∈ V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
      have e : g * v * g⁻¹ = σ := by rw [hvdef]; group
      rwa [e] at this
    exact hσL (hV₁L hσV₁)

end CFSG.Quasithin.SBd18
