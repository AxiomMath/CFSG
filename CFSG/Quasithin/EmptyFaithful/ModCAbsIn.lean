module

public import CFSG.Quasithin.EmptyFaithful.ModCAbs
public import CFSG.Quasithin.EmptyFaithful.ModCStd6
public import CFSG.Quasithin.EmptyFaithful.ModCIn6
public import CFSG.Quasithin.H13.A6Model

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

section AbsIn

variable {W : Type*} [CommGroup W]

@[expose] def Xgen (Kb : Subgroup (MulAut W)) (V : Subgroup W) (u : W) : Subgroup W :=
  Subgroup.closure {x | ∃ σ ∈ Kb, σ u = u ∧ ∃ q ∈ V, x = σ q}

@[expose] def CenN (Kb : Subgroup (MulAut W)) (X : Subgroup W) : Set (MulAut W) :=
  {p | (∀ k ∈ Kb, p * k * p⁻¹ ∈ Kb ∧ p⁻¹ * k * p ∈ Kb) ∧ ∀ x ∈ X, p x = x}

theorem exists_perm_of_normalizes6 (Φ : W ≃* ↥(coreMod 6)) {Θ : Perm (Fin 6) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct 6 σ (Φ w)) {Kb : Subgroup (MulAut W)}
    (hKb : Kb = (alternatingGroup (Fin 6)).map Θ) {p : MulAut W}
    (hp : ∀ k ∈ Kb, p * k * p⁻¹ ∈ Kb ∧ p⁻¹ * k * p ∈ Kb) : ∃ π : Perm (Fin 6), p = Θ π := by
  classical
  have hmemrev : ∀ k ∈ Kb, ∃ σ ∈ alternatingGroup (Fin 6), Θ σ = k := by
    intro k hk
    rw [hKb] at hk
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hk
    exact ⟨σ, hσ, rfl⟩
  have hmem : ∀ σ ∈ alternatingGroup (Fin 6), Θ σ ∈ Kb := fun σ hσ => by
    rw [hKb]
    exact Subgroup.mem_map_of_mem _ hσ
  have hΘsymm : ∀ (σ : Perm (Fin 6)) (u : W), Φ.symm (coreAct 6 σ (Φ u)) = Θ σ u := fun σ u => by
    rw [← hΘ]
    simp
  let ρ : MulAut ↥(coreMod 6) := MulAut.congr Φ p
  have hρ : ∀ u, ρ u = Φ (p (Φ.symm u)) := fun u => rfl
  have hcomm : ∀ (σ τ : Perm (Fin 6)), Θ τ = p * Θ σ * p⁻¹ →
      ∀ x, ρ (coreAct 6 σ x) = coreAct 6 τ (ρ x) := by
    intro σ τ hτ x
    obtain ⟨w, rfl⟩ := Φ.surjective x
    have h1 : Θ τ (p w) = p (Θ σ w) := by
      rw [hτ]
      show p (Θ σ (p⁻¹ (p w))) = p (Θ σ w)
      rw [show p⁻¹ (p w) = w from by simp]
    rw [hρ, hρ, hΘsymm, MulEquiv.symm_apply_apply, ← hΘ τ (p w), h1]
  have h1 : ∀ σ ∈ alternatingGroup (Fin 6), ∃ τ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (coreAct 6 σ x) = coreAct 6 τ (ρ x) := by
    intro σ hσ
    obtain ⟨τ, hτ, hτe⟩ := hmemrev _ (hp (Θ σ) (hmem σ hσ)).1
    exact ⟨τ, hτ, hcomm σ τ hτe⟩
  have h2 : ∀ τ ∈ alternatingGroup (Fin 6), ∃ σ ∈ alternatingGroup (Fin 6),
      ∀ x, ρ (coreAct 6 σ x) = coreAct 6 τ (ρ x) := by
    intro τ hτ
    obtain ⟨σ, hσ, hσe⟩ := hmemrev _ (hp (Θ τ) (hmem τ hτ)).2
    refine ⟨σ, hσ, hcomm σ τ ?_⟩
    rw [hσe]
    group
  obtain ⟨π, hπ⟩ := CFSG.Quasithin.H13.A6.exists_perm_of_normalizes_core ρ h1 h2
  refine ⟨π, MulEquiv.ext fun w => Φ.injective ?_⟩
  rw [hΘ, ← hπ, hρ, MulEquiv.symm_apply_apply]

theorem std_core6 (Φ : W ≃* ↥(coreMod 6)) {Θ : Perm (Fin 6) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct 6 σ (Φ w)) {Kb : Subgroup (MulAut W)}
    (hKb : Kb = (alternatingGroup (Fin 6)).map Θ) {z v : W} {V : Subgroup W}
    (hz1 : z ≠ 1) (hv1 : v ≠ 1) (hvz : v ≠ z) (hzV : z ∈ V) (hvV : v ∈ V)
    (hz : ((Φ z : ↥(coreMod 6)) : PermMod 6) = M6.a)
    (hv : ((Φ v : ↥(coreMod 6)) : PermMod 6) = M6.w ∨
      ((Φ v : ↥(coreMod 6)) : PermMod 6) = M6.a * M6.w) :
    (Xgen Kb V z ⊔ Xgen Kb V v = ⊤) ∧ (Xgen Kb V z ⊔ Xgen Kb V (z * v) = ⊤) ∧
    (Xgen Kb V v ⊔ Xgen Kb V (z * v) = ⊤) ∧
    ∀ p : MulAut W,
      (∃ p₁ ∈ CenN Kb (Xgen Kb V z), ∃ p₂ ∈ CenN Kb (Xgen Kb V v), p = p₁ * p₂) →
      (∃ p₁ ∈ CenN Kb (Xgen Kb V z), ∃ p₃ ∈ CenN Kb (Xgen Kb V (z * v)), p = p₁ * p₃) →
      (∃ p₂ ∈ CenN Kb (Xgen Kb V v), ∃ p₃ ∈ CenN Kb (Xgen Kb V (z * v)), p = p₂ * p₃) → p = 1 := by
  classical
  have hΘinj : Function.Injective Θ := theta_injective (by norm_num) Φ hΘ
  let Ψ : W → PermMod 6 := fun w => ((Φ w : ↥(coreMod 6)) : PermMod 6)
  have hΨinj : Function.Injective Ψ := fun a b h => Φ.injective (Subtype.ext h)
  have hΨmul : ∀ a b : W, Ψ (a * b) = Ψ a * Ψ b := fun a b => by simp [Ψ]
  have hΨ1 : Ψ 1 = 1 := by simp [Ψ]
  have hΨΘ : ∀ (τ : Perm (Fin 6)) (w : W), Ψ (Θ τ w) = permAct 6 τ (Ψ w) := fun τ w => by
    simp only [Ψ]
    rw [hΘ]
    rfl
  have hΨcore : ∀ w, ∑ i, Multiplicative.toAdd (Ψ w) i = 0 := fun w => mem_coreMod.mp (Φ w).2
  have hz' : Ψ z = M6.a := hz
  have hΨz : Ψ z ∈ [M6.a, M6.w, M6.a * M6.w] := by rw [hz']; simp
  have hΨv : Ψ v ∈ [M6.a, M6.w, M6.a * M6.w] := by
    rcases hv with h | h
    · rw [show Ψ v = M6.w from h]; simp
    · rw [show Ψ v = M6.a * M6.w from h]; simp
  have hΨzv : Ψ (z * v) ∈ [M6.a, M6.w, M6.a * M6.w] := by
    rw [hΨmul, hz']
    rcases hv with h | h
    · rw [show Ψ v = M6.w from h]; simp
    · rw [show Ψ v = M6.a * M6.w from h, M6.a_mul_a_mul_w]; simp
  have hVimg : ∀ q ∈ V4 M6.a M6.w, ∃ q' ∈ V, Ψ q' = q := by
    intro q hq
    simp only [V4, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨1, V.one_mem, hΨ1⟩
    · exact ⟨z, hzV, hz'⟩
    · rcases hv with h | h
      · exact ⟨v, hvV, h⟩
      · exact ⟨z * v, V.mul_mem hzV hvV, by rw [hΨmul, hz', show Ψ v = M6.a * M6.w from h,
          M6.a_mul_a_mul_w]⟩
    · rcases hv with h | h
      · exact ⟨z * v, V.mul_mem hzV hvV, by rw [hΨmul, hz', show Ψ v = M6.w from h]⟩
      · exact ⟨v, hvV, h⟩
  have hgen : ∀ u : W, Ψ u ∈ [M6.a, M6.w, M6.a * M6.w] →
      ∀ g ∈ M6.Gen (Ψ u), ∃ x ∈ Xgen Kb V u, Ψ x = g := by
    intro u hu g hg
    obtain ⟨σ, hσ1, hσu, q, hq, rfl⟩ := M6.mem_Gen.mp hg
    obtain ⟨q', hq'V, hq'⟩ := hVimg q hq
    have hσA : σ ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr hσ1
    have hΘσ : Θ σ ∈ Kb := by
      rw [hKb]
      exact Subgroup.mem_map_of_mem _ hσA
    have hfix : Θ σ u = u := hΨinj (by rw [hΨΘ, hσu])
    refine ⟨Θ σ q', Subgroup.subset_closure ⟨Θ σ, hΘσ, hfix, q', hq'V, rfl⟩, ?_⟩
    rw [hΨΘ, hq']
  have hH : ∀ u : W, Ψ u ∈ [M6.a, M6.w, M6.a * M6.w] →
      ∀ h : PermMod 6, M6.Hy (Ψ u) h → ∃ x ∈ Xgen Kb V u, Ψ x = h := by
    intro u hu h hh
    obtain ⟨g₁, h₁, g₂, h₂, g₃, h₃, rfl⟩ := M6.span_of hu h hh
    obtain ⟨x₁, hx₁, rfl⟩ := hgen u hu g₁ h₁
    obtain ⟨x₂, hx₂, rfl⟩ := hgen u hu g₂ h₂
    obtain ⟨x₃, hx₃, rfl⟩ := hgen u hu g₃ h₃
    exact ⟨x₁ * x₂ * x₃, mul_mem (mul_mem hx₁ hx₂) hx₃, by rw [hΨmul, hΨmul]⟩
  have hdec : ∀ u u' : W, Ψ u ∈ [M6.a, M6.w, M6.a * M6.w] → Ψ u' ∈ [M6.a, M6.w, M6.a * M6.w] →
      Ψ u ≠ Ψ u' → Xgen Kb V u ⊔ Xgen Kb V u' = ⊤ := by
    intro u u' hu hu' hne
    rw [eq_top_iff]
    intro x _
    obtain ⟨h₁, h₂, hh₁, hh₂, hx⟩ := M6.sum_of hu hu' hne (Ψ x) (hΨcore x)
    obtain ⟨x₁, hx₁, rfl⟩ := hH u hu h₁ hh₁
    obtain ⟨x₂, hx₂, rfl⟩ := hH u' hu' h₂ hh₂
    have : x = x₁ * x₂ := hΨinj (by rw [hΨmul]; exact hx)
    rw [this]
    exact Subgroup.mul_mem_sup hx₁ hx₂
  have hcen : ∀ u : W, Ψ u ∈ [M6.a, M6.w, M6.a * M6.w] → ∀ p : MulAut W,
      p ∈ CenN Kb (Xgen Kb V u) → ∃ π : Perm (Fin 6), (π = 1 ∨ π = M6.tau (Ψ u)) ∧ p = Θ π := by
    intro u hu p hp
    obtain ⟨π, rfl⟩ := exists_perm_of_normalizes6 Φ hΘ hKb hp.1
    refine ⟨π, M6.cent_of_gen hu π fun g hg => ?_, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hgen u hu g hg
    have := hp.2 x hx
    rw [← hΨΘ, this]
  have hne12 : Ψ z ≠ Ψ v := fun h => hvz (hΨinj h).symm
  have hne13 : Ψ z ≠ Ψ (z * v) := fun h => hv1 (mul_eq_left.mp (hΨinj h).symm)
  have hne23 : Ψ v ≠ Ψ (z * v) := fun h => hz1 (mul_eq_right.mp (hΨinj h).symm)
  refine ⟨hdec z v hΨz hΨv hne12, hdec z (z * v) hΨz hΨzv hne13, hdec v (z * v) hΨv hΨzv hne23, ?_⟩
  intro p h12 h13 h23
  obtain ⟨p₁, hp₁, p₂, hp₂, e12⟩ := h12
  obtain ⟨π₁, hπ₁, rfl⟩ := hcen z hΨz p₁ hp₁
  obtain ⟨π₂, hπ₂, rfl⟩ := hcen v hΨv p₂ hp₂
  obtain ⟨p₁', hp₁', p₃, hp₃, e13⟩ := h13
  obtain ⟨π₁', hπ₁', rfl⟩ := hcen z hΨz p₁' hp₁'
  obtain ⟨π₃, hπ₃, rfl⟩ := hcen (z * v) hΨzv p₃ hp₃
  obtain ⟨p₂', hp₂', p₃', hp₃', e23⟩ := h23
  obtain ⟨π₂', hπ₂', rfl⟩ := hcen v hΨv p₂' hp₂'
  obtain ⟨π₃', hπ₃', rfl⟩ := hcen (z * v) hΨzv p₃' hp₃'
  have e1 : π₁ * π₂ = π₁' * π₃ := hΘinj (by rw [map_mul, map_mul, ← e12, ← e13])
  have e2 : π₁ * π₂ = π₂' * π₃' := hΘinj (by rw [map_mul, map_mul, ← e12, ← e23])
  have hE12 : M6.E2 (M6.tau (Ψ z)) (M6.tau (Ψ v)) (π₁ * π₂) := by
    rcases hπ₁ with rfl | rfl <;> rcases hπ₂ with rfl | rfl <;> simp [M6.E2]
  have hE13 : M6.E2 (M6.tau (Ψ z)) (M6.tau (Ψ (z * v))) (π₁ * π₂) := by
    rw [e1]
    rcases hπ₁' with rfl | rfl <;> rcases hπ₃ with rfl | rfl <;> simp [M6.E2]
  have hE23 : M6.E2 (M6.tau (Ψ v)) (M6.tau (Ψ (z * v))) (π₁ * π₂) := by
    rw [e2]
    rcases hπ₂' with rfl | rfl <;> rcases hπ₃' with rfl | rfl <;> simp [M6.E2]
  have h1 : π₁ * π₂ = 1 := M6.triple3 _ hΨz _ hΨv _ hΨzv hne12 hne13 hne23 _ hE12 hE13 hE23
  rw [e12, ← map_mul, h1, map_one]

theorem abstractIn6 (Φ : W ≃* ↥(coreMod 6)) {Θ : Perm (Fin 6) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct 6 σ (Φ w)) {Kb Bf : Subgroup (MulAut W)}
    (hKb : Kb = (alternatingGroup (Fin 6)).map Θ) (hB2 : IsPGroup 2 Bf)
    (h8 : 8 ≤ Nat.card ↥(Kb ⊓ Bf)) {z v : W} (hz1 : z ≠ 1) (hv1 : v ≠ 1) (hvz : v ≠ z)
    {V : Subgroup W} (hzV : z ∈ V) (hvV : v ∈ V)
    (hV : ∀ a ∈ V, a = 1 ∨ a = z ∨ a = v ∨ a = z * v)
    (hBz : ∀ τ ∈ Bf, τ z = z) (hBV : ∀ τ ∈ Bf, ∀ a ∈ V, τ a ∈ V) (hwt : ∃ k ∈ Kb, k z = v) :
    (Xgen Kb V z ⊔ Xgen Kb V v = ⊤) ∧ (Xgen Kb V z ⊔ Xgen Kb V (z * v) = ⊤) ∧
    (Xgen Kb V v ⊔ Xgen Kb V (z * v) = ⊤) ∧
    ∀ p : MulAut W,
      (∃ p₁ ∈ CenN Kb (Xgen Kb V z), ∃ p₂ ∈ CenN Kb (Xgen Kb V v), p = p₁ * p₂) →
      (∃ p₁ ∈ CenN Kb (Xgen Kb V z), ∃ p₃ ∈ CenN Kb (Xgen Kb V (z * v)), p = p₁ * p₃) →
      (∃ p₂ ∈ CenN Kb (Xgen Kb V v), ∃ p₃ ∈ CenN Kb (Xgen Kb V (z * v)), p = p₂ * p₃) → p = 1 := by
  classical
  have hΘinj : Function.Injective Θ := theta_injective (by norm_num) Φ hΘ
  let Ψ : W → PermMod 6 := fun w => ((Φ w : ↥(coreMod 6)) : PermMod 6)
  have hΨinj : Function.Injective Ψ := fun a b h => Φ.injective (Subtype.ext h)
  have hΨmul : ∀ a b : W, Ψ (a * b) = Ψ a * Ψ b := fun a b => by simp [Ψ]
  have hΨ1 : Ψ 1 = 1 := by simp [Ψ]
  have hΨcore : ∀ w, ∑ i, Multiplicative.toAdd (Ψ w) i = 0 := fun w => mem_coreMod.mp (Φ w).2
  have hΨΘ : ∀ (τ : Perm (Fin 6)) (w : W), Ψ (Θ τ w) = permAct 6 τ (Ψ w) := fun τ w => by
    simp only [Ψ]
    rw [hΘ]
    rfl
  have hKbmem : ∀ k ∈ Kb, ∃ σ ∈ alternatingGroup (Fin 6), Θ σ = k := by
    intro k hk
    rw [hKb] at hk
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hk
    exact ⟨σ, hσ, rfl⟩
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 8 * 45 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hD8 : Nat.card ↥(Bf.comap Θ ⊓ alternatingGroup (Fin 6)) = 8 :=
    card_D hΘinj hB2 ⟨22, by norm_num⟩ hcardA (by rw [← hKb]; exact h8)
  have hDe : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin 6), sign d = 1 := fun d hd =>
    Perm.mem_alternatingGroup.mp hd.2
  have hz1' : Ψ z ≠ 1 := fun h => hz1 (hΨinj (h.trans hΨ1.symm))
  have hv1' : Ψ v ≠ 1 := fun h => hv1 (hΨinj (h.trans hΨ1.symm))
  have hvz' : Ψ v ≠ Ψ z := fun h => hvz (hΨinj h)
  have hDV : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin 6),
      permAct 6 d (Ψ z) = Ψ z ∧ (permAct 6 d (Ψ v) = Ψ v ∨ permAct 6 d (Ψ v) = Ψ z * Ψ v) := by
    intro d hd
    have hτ : Θ d ∈ Bf := hd.1
    have h1 : Θ d z = z := hBz _ hτ
    have h2 : Θ d v ∈ V := hBV _ hτ v hvV
    refine ⟨by rw [← hΨΘ, h1], ?_⟩
    rcases hV _ h2 with h | h | h | h
    · exact absurd ((Θ d).injective (h.trans (map_one (Θ d)).symm)) hv1
    · exact absurd ((Θ d).injective (h.trans h1.symm)) hvz
    · left
      rw [← hΨΘ, h]
    · right
      rw [← hΨΘ, h, hΨmul]
  have hwt' : wt (Ψ v) = wt (Ψ z) ∨ wt (Ψ z * Ψ v) = wt (Ψ z) := by
    left
    obtain ⟨k, hk, hkz⟩ := hwt
    obtain ⟨σ, -, rfl⟩ := hKbmem k hk
    have : Ψ v = permAct 6 σ (Ψ z) := by rw [← hkz, hΨΘ]
    rw [this, wt_permAct]
  obtain ⟨τ, hτz, hτv⟩ := std_position6 _ hDe hD8 (Ψ z) (Ψ v) (hΨcore z) hz1' (hΨcore v) hv1' hvz' hDV
    hwt'
  let Φ' : W ≃* ↥(coreMod 6) := Φ.trans (coreAct 6 τ)
  let Θ' : Perm (Fin 6) →* MulAut W := Θ.comp (MulAut.conj τ⁻¹).toMonoidHom
  have hΘ' : ∀ σ w, Φ' (Θ' σ w) = coreAct 6 σ (Φ' w) := by
    intro σ w
    show coreAct 6 τ (Φ (Θ (τ⁻¹ * σ * τ⁻¹⁻¹) w)) = coreAct 6 σ (coreAct 6 τ (Φ w))
    rw [hΘ, ← MulAut.mul_apply, ← map_mul, ← MulAut.mul_apply, ← map_mul]
    congr 2
    group
  have hKb' : Kb = (alternatingGroup (Fin 6)).map Θ' := by
    rw [hKb]
    ext g
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨τ * σ * τ⁻¹, (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem σ hσ τ, ?_⟩
      show Θ (τ⁻¹ * (τ * σ * τ⁻¹) * τ⁻¹⁻¹) = Θ σ
      congr 1
      group
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨τ⁻¹ * σ * τ⁻¹⁻¹, (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem σ hσ τ⁻¹, rfl⟩
  exact std_core6 Φ' hΘ' hKb' hz1 hv1 hvz hzV hvV hτz hτv

end AbsIn

end CFSG.Quasithin.ModC
