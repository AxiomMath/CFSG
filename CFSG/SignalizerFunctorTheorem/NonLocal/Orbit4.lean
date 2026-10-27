module

public import CFSG.SignalizerFunctorTheorem.NonLocal.AbelianLift

public section

open Module
open scoped IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {F W G : Type*} [Field F] [AddCommGroup W] [Module F W] [Group G]

theorem four_le_finrank_of_inverting [IsAlgClosed F] [FiniteDimensional F W] (ρ : G →* End F W)
    (E : Subgroup G) [Finite E] (hE : IsMulCommutative E) (hinv : (Nat.card E : F) ≠ 0)
    (hinj : ∀ e ∈ E, ρ e = 1 → e = 1) (hodd : ∀ e ∈ E, e * e = 1 → e = 1) (hnt : E ≠ ⊥)
    (g : G) (hgE : ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hg2 : ∀ e ∈ E, g * g * e * (g * g)⁻¹ = e⁻¹) : 4 ≤ finrank F W := by
  classical
  have hgE' : ∀ e ∈ E, g⁻¹ * e * g ∈ E := by
    intro e he
    have h1 : g⁻¹ * e * g = g * e⁻¹ * g⁻¹ := by
      have := hg2 e⁻¹ (E.inv_mem he)
      rw [inv_inv] at this
      calc g⁻¹ * e * g = g⁻¹ * (g * g * e⁻¹ * (g * g)⁻¹) * g := by rw [this]
        _ = g * e⁻¹ * g⁻¹ := by group
    rw [h1]
    exact hgE _ (E.inv_mem he)
  have hgg : ∀ e ∈ E, g⁻¹ * g⁻¹ * e * (g⁻¹ * g⁻¹)⁻¹ = e⁻¹ := by
    intro e he
    have := hg2 e⁻¹ (E.inv_mem he)
    rw [inv_inv] at this
    calc g⁻¹ * g⁻¹ * e * (g⁻¹ * g⁻¹)⁻¹ = g⁻¹ * g⁻¹ * (g * g * e⁻¹ * (g * g)⁻¹) *
          (g⁻¹ * g⁻¹)⁻¹ := by rw [this]
      _ = e⁻¹ := by group
  obtain ⟨e₀, he₀, hne₀⟩ : ∃ e₀ ∈ E, e₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hnt ((Subgroup.eq_bot_iff_forall E).mpr h)
  have hρe₀ : ρ e₀ ≠ 1 := fun h => hne₀ (hinj e₀ he₀ h)
  obtain ⟨χ, w, hw, hTw⟩ := exists_jointEigenvector_apply_ne_zero ρ E hE hinv (ρ e₀ - 1)
    (sub_ne_zero.mpr hρe₀)
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hTw (by simp)
  have hχ : IsWeight ρ E χ := ⟨w, hw0, hw⟩
  have hχe₀ : χ ⟨e₀, he₀⟩ ≠ 1 := by
    intro h
    apply hTw
    rw [LinearMap.sub_apply, Module.End.one_apply, hw ⟨e₀, he₀⟩, h, one_smul, sub_self]
  have hcardodd : Odd (Nat.card E) := by
    by_contra h
    have h2 : 2 ∣ Nat.card E := by
      rcases Nat.even_or_odd (Nat.card E) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho h
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 h2
    have h3 : e * e = 1 := by rw [← pow_two]; exact he ▸ pow_orderOf_eq_one e
    have h4 : (e : G) * e = 1 := congrArg Subtype.val h3
    have h5 : (e : G) = 1 := hodd e e.2 h4
    have h6 : e = 1 := Subtype.ext h5
    rw [h6, orderOf_one] at he
    omega
  have hA : χ ⟨e₀, he₀⟩ * χ ⟨e₀, he₀⟩ ≠ 1 := by
    intro h
    apply hχe₀
    obtain ⟨k, hk⟩ := hcardodd
    have h1 : χ ⟨e₀, he₀⟩ ^ Nat.card E = 1 := by
      rw [← hχ.pow, pow_card_eq_one', hχ.one]
    have h2 : χ ⟨e₀, he₀⟩ ^ 2 = 1 := by rw [pow_two]; exact h
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  let c : E → E := fun a => ⟨g * a * g⁻¹, hgE _ a.2⟩
  have hcc : ∀ a : E, χ (c (c a)) = (χ a)⁻¹ := by
    intro a
    have h1 : c (c a) = a⁻¹ := by
      apply Subtype.ext
      have := hg2 a a.2
      calc g * (g * (a : G) * g⁻¹) * g⁻¹ = g * g * a * (g * g)⁻¹ := by group
        _ = a⁻¹ := this
    rw [h1, hχ.inv]
  have hB : ¬ ∀ a : E, χ (c a) = χ a := by
    intro h
    have h1 : χ ⟨e₀, he₀⟩ = (χ ⟨e₀, he₀⟩)⁻¹ := by
      rw [← hcc ⟨e₀, he₀⟩, h (c ⟨e₀, he₀⟩), h ⟨e₀, he₀⟩]
    apply hA
    nth_rewrite 1 [h1]
    exact inv_mul_cancel₀ (hχ.ne_zero _)
  have hC : ¬ ∀ a : E, χ (c a) = (χ a)⁻¹ := by
    intro h
    have h1 : χ ⟨e₀, he₀⟩ = (χ ⟨e₀, he₀⟩)⁻¹ := by
      have h2 := hcc ⟨e₀, he₀⟩
      rw [h (c ⟨e₀, he₀⟩), h ⟨e₀, he₀⟩, inv_inv] at h2
      exact h2
    apply hA
    nth_rewrite 1 [h1]
    exact inv_mul_cancel₀ (hχ.ne_zero _)
  have hD : ∃ a : E, χ (c a) * χ (c a) ≠ 1 := by
    refine ⟨⟨g⁻¹ * e₀ * g, hgE' e₀ he₀⟩, ?_⟩
    have : c ⟨g⁻¹ * e₀ * g, hgE' e₀ he₀⟩ = ⟨e₀, he₀⟩ := by
      apply Subtype.ext
      show g * (g⁻¹ * e₀ * g) * g⁻¹ = e₀
      group
    rw [this]
    exact hA
  let f : Fin 4 → E → F := ![χ, fun a => χ (c a), fun a => (χ a)⁻¹, fun a => (χ (c a))⁻¹]
  have hshift : ∀ (h : E → F) (v : W), (∀ a : E, ρ a v = h a • v) →
      ∀ a : E, ρ a (ρ g⁻¹ v) = h (c a) • ρ g⁻¹ v := by
    intro h v hv a
    have h1 : ρ (a : G) * ρ g⁻¹ = ρ g⁻¹ * ρ (g * a * g⁻¹) := by
      rw [← map_mul, ← map_mul]
      congr 1
      group
    have h2 : ρ (g * (a : G) * g⁻¹) v = h (c a) • v := hv (c a)
    rw [← Module.End.mul_apply, h1, Module.End.mul_apply, h2, map_smul]
  have hρg : ∀ v : W, v ≠ 0 → ρ g⁻¹ v ≠ 0 := by
    intro v hv h
    apply hv
    have h1 : ρ g (ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, h, map_zero]
  let v : Fin 4 → W := ![w, ρ g⁻¹ w, ρ g⁻¹ (ρ g⁻¹ w), ρ g⁻¹ (ρ g⁻¹ (ρ g⁻¹ w))]
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i
    fin_cases i
    · exact hw0
    · exact hρg _ hw0
    · exact hρg _ (hρg _ hw0)
    · exact hρg _ (hρg _ (hρg _ hw0))
  have hev : ∀ (i : Fin 4) (a : E), ρ a (v i) = f i a • v i := by
    intro i a
    fin_cases i
    · exact hw a
    · exact hshift χ w hw a
    · have h1 := hshift (fun a => χ (c a)) (ρ g⁻¹ w) (hshift χ w hw) a
      show ρ a (ρ g⁻¹ (ρ g⁻¹ w)) = (χ a)⁻¹ • ρ g⁻¹ (ρ g⁻¹ w)
      rw [h1, hcc a]
    · have h2 : ∀ a : E, ρ a (ρ g⁻¹ (ρ g⁻¹ w)) = (χ a)⁻¹ • ρ g⁻¹ (ρ g⁻¹ w) := by
        intro a
        have h1 := hshift (fun a => χ (c a)) (ρ g⁻¹ w) (hshift χ w hw) a
        rw [h1, hcc a]
      exact hshift (fun a => (χ a)⁻¹) _ h2 a
  have hχne : ∀ a : E, χ a ≠ 0 := fun a => hχ.ne_zero a
  have hinvsq : ∀ x : F, x ≠ 0 → x = x⁻¹ → x * x = 1 := fun x hx h =>
    calc x * x = x * x⁻¹ := congrArg (x * ·) h
      _ = 1 := mul_inv_cancel₀ hx
  have h01 : f 0 ≠ f 1 := fun h => hB fun a => (congrFun h a).symm
  have h02 : f 0 ≠ f 2 := by
    intro h
    apply hA
    have h1 : χ ⟨e₀, he₀⟩ = (χ ⟨e₀, he₀⟩)⁻¹ := congrFun h ⟨e₀, he₀⟩
    exact hinvsq _ (hχne _) h1
  have h03 : f 0 ≠ f 3 := by
    intro h
    apply hC
    intro a
    have h1 : χ a = (χ (c a))⁻¹ := congrFun h a
    rw [h1, inv_inv]
  have h12 : f 1 ≠ f 2 := fun h => hC fun a => congrFun h a
  have h13 : f 1 ≠ f 3 := by
    intro h
    obtain ⟨a, ha⟩ := hD
    apply ha
    have h1 : χ (c a) = (χ (c a))⁻¹ := congrFun h a
    exact hinvsq _ (hχne _) h1
  have h23 : f 2 ≠ f 3 := by
    intro h
    apply hB
    intro a
    have h1 : (χ a)⁻¹ = (χ (c a))⁻¹ := congrFun h a
    exact (inv_inj.mp h1).symm
  have hinjf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij h01
    · exact absurd hij h02
    · exact absurd hij h03
    · exact absurd hij.symm h01
    · rfl
    · exact absurd hij h12
    · exact absurd hij h13
    · exact absurd hij.symm h02
    · exact absurd hij.symm h12
    · rfl
    · exact absurd hij h23
    · exact absurd hij.symm h03
    · exact absurd hij.symm h13
    · exact absurd hij.symm h23
    · rfl
  have hli := linearIndependent_of_distinct_weights ρ E hE v f hv0 hev hinjf
  have := hli.fintype_card_le_finrank
  simpa using this

end CFSG.SignalizerFunctorTheorem.NonLocal
