module

public import CFSG.Quasithin.EmptyFaithful.S1422LocAutM12

public section

namespace CFSG.Quasithin

namespace S1422Loc

section Ker

variable {G : Type*} [Group G]

theorem commutes_of_step_of_odd {A B : Subgroup G} {g : G} (hodd : Odd (orderOf g))
    (hA2 : IsPGroup 2 A) (hcA : ∀ a ∈ A, g * a = a * g)
    (hstep : ∀ b ∈ B, g * b * g⁻¹ * b⁻¹ ∈ A) : ∀ b ∈ B, g * b = b * g := by
  intro b hb
  have h1 := hstep b hb
  obtain ⟨a', ha'⟩ : ∃ a' : G, a' = (g * b * g⁻¹) * b⁻¹ := ⟨_, rfl⟩
  rw [← ha'] at h1
  have hc : g * b * g⁻¹ = a' * b := by rw [ha']; group
  have hga' : g * a' = a' * g := hcA a' h1
  have hpow : ∀ k : ℕ, g ^ k * b * (g ^ k)⁻¹ = a' ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : g * a' ^ k * g⁻¹ = a' ^ k := by
        have := (Commute.pow_right (show Commute g a' from hga') k).eq
        rw [this]; group
      calc g ^ (k + 1) * b * (g ^ (k + 1))⁻¹ = g * (g ^ k * b * (g ^ k)⁻¹) * g⁻¹ := by group
        _ = g * (a' ^ k * b) * g⁻¹ := by rw [ih]
        _ = (g * a' ^ k * g⁻¹) * (g * b * g⁻¹) := by group
        _ = a' ^ k * (a' * b) := by rw [hk, hc]
        _ = a' ^ (k + 1) * b := by group
  have h2 := hpow (orderOf g)
  rw [pow_orderOf_eq_one] at h2
  have h3 : a' ^ orderOf g = 1 := by
    have : a' ^ orderOf g * b = 1 * b := by simpa using h2.symm
    exact mul_right_cancel this
  have h4 : a' = 1 := eq_one_of_pow_odd hA2 h1 hodd h3
  rw [h4] at hc
  calc g * b = (g * b * g⁻¹) * g := by group
    _ = b * g := by rw [hc]; simp

end Ker

section KerFinite

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_trivial_on_quotient {P E F Z : Subgroup G} (hP2 : IsPGroup 2 P)
    (hEP : E ≤ P) (hEF : E ≤ F) (hFP : F ≤ P) (hZ2 : IsPGroup 2 Z)
    (hZcen : ∀ z ∈ Z, ∀ x ∈ P, x * z = z * x)
    (hEZ : ∀ e ∈ E, ∀ x ∈ P, e * x * e⁻¹ * x⁻¹ ∈ Z)
    (hFE : ∀ u ∈ F, ∀ e ∈ E, u * e = e * u)
    (hCE : ∀ x ∈ E, (∀ y ∈ P, x * y = y * x) → x ∈ Z)
    (hFE2 : Nat.card F ≤ 2 * Nat.card E)
    {g : G} (hodd : Odd (orderOf g)) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hgF : g ∈ Subgroup.normalizer (F : Set G)) (hgZ : ∀ z ∈ Z, g * z = z * g)
    (hgtriv : ∀ x ∈ P, g * x * g⁻¹ * x⁻¹ ∈ F) : ∀ x ∈ P, g * x = x * g := by
  have hstepA : ∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Z := by
    intro e he
    have he' : g * e * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE e).mp he
    have hb : (g * e * g⁻¹)⁻¹ * e ∈ Z := by
      refine hCE _ (E.mul_mem (E.inv_mem he') he) fun x hx => ?_
      have huF : g * x * g⁻¹ * x⁻¹ ∈ F := hgtriv x hx
      have hux : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      have hζ1 : e * x * e⁻¹ * x⁻¹ ∈ Z := hEZ e he x hx
      have hζ2 : (g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹ * x⁻¹ ∈ Z := hEZ _ he' x hx
      have h1 : g * (e * x * e⁻¹ * x⁻¹) * g⁻¹ = e * x * e⁻¹ * x⁻¹ := by
        have := hgZ _ hζ1
        rw [this]; group
      have h2 : g * (e * x * e⁻¹ * x⁻¹) * g⁻¹ =
          (g * e * g⁻¹) * ((g * x * g⁻¹ * x⁻¹) * x) * (g * e * g⁻¹)⁻¹ *
            ((g * x * g⁻¹ * x⁻¹) * x)⁻¹ := by
        calc g * (e * x * e⁻¹ * x⁻¹) * g⁻¹
            = (g * e * g⁻¹) * (g * x * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ := by group
          _ = _ := by rw [← hux]
      have hue : (g * x * g⁻¹ * x⁻¹) * (g * e * g⁻¹) = (g * e * g⁻¹) * (g * x * g⁻¹ * x⁻¹) :=
        hFE _ huF _ he'
      have h3 : (g * e * g⁻¹) * ((g * x * g⁻¹ * x⁻¹) * x) * (g * e * g⁻¹)⁻¹ *
          ((g * x * g⁻¹ * x⁻¹) * x)⁻¹ =
          (g * x * g⁻¹ * x⁻¹) * ((g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹ * x⁻¹) *
            (g * x * g⁻¹ * x⁻¹)⁻¹ := by
        calc (g * e * g⁻¹) * ((g * x * g⁻¹ * x⁻¹) * x) * (g * e * g⁻¹)⁻¹ *
              ((g * x * g⁻¹ * x⁻¹) * x)⁻¹
            = ((g * e * g⁻¹) * (g * x * g⁻¹ * x⁻¹)) * x * (g * e * g⁻¹)⁻¹ * x⁻¹ *
                (g * x * g⁻¹ * x⁻¹)⁻¹ := by group
          _ = ((g * x * g⁻¹ * x⁻¹) * (g * e * g⁻¹)) * x * (g * e * g⁻¹)⁻¹ * x⁻¹ *
                (g * x * g⁻¹ * x⁻¹)⁻¹ := by rw [hue]
          _ = _ := by group
      have h4 : (g * x * g⁻¹ * x⁻¹) * ((g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹ * x⁻¹) *
          (g * x * g⁻¹ * x⁻¹)⁻¹ = (g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹ * x⁻¹ := by
        have := hZcen _ hζ2 _ (hFP huF)
        rw [this]; group
      have h5 : e * x * e⁻¹ * x⁻¹ = (g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹ * x⁻¹ := by
        rw [← h1, h2, h3, h4]
      have h6 : e * x * e⁻¹ = (g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹ := by
        have := congrArg (fun w => w * x) h5
        simpa [mul_assoc] using this
      calc (g * e * g⁻¹)⁻¹ * e * x
          = (g * e * g⁻¹)⁻¹ * (e * x * e⁻¹) * e := by group
        _ = (g * e * g⁻¹)⁻¹ * ((g * e * g⁻¹) * x * (g * e * g⁻¹)⁻¹) * e := by rw [h6]
        _ = x * ((g * e * g⁻¹)⁻¹ * e) := by group
    have e1 : g * e * g⁻¹ * e⁻¹ = e * ((g * e * g⁻¹)⁻¹ * e)⁻¹ * e⁻¹ := by group
    rw [e1]
    have hbi : ((g * e * g⁻¹)⁻¹ * e)⁻¹ ∈ Z := Z.inv_mem hb
    have := hZcen _ hbi e (hEP he)
    rw [this]
    simpa using hbi
  have hcE : ∀ e ∈ E, g * e = e * g :=
    commutes_of_step_of_odd hodd hZ2 hgZ hstepA
  have hstepB : ∀ f ∈ F, g * f * g⁻¹ * f⁻¹ ∈ E := by
    intro f hf
    have h := card_eq_card_mul_relIndex hEF
    have hEpos : 0 < Nat.card E := Nat.card_pos
    have hr1 : E.relIndex F ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h
      exact (Nat.card_pos (α := F)).ne' h
    have hr2 : E.relIndex F ≤ 2 := by
      by_contra hcon
      have h3 : 3 ≤ E.relIndex F := by omega
      have h4 : Nat.card E * 3 ≤ Nat.card E * E.relIndex F := Nat.mul_le_mul_left _ h3
      omega
    have hr : E.relIndex F = 1 ∨ E.relIndex F = 2 := by omega
    rcases hr with hr | hr
    · have hFE' : F ≤ E := Subgroup.relIndex_eq_one.mp hr
      exact hFE' (F.mul_mem ((Subgroup.mem_normalizer_iff.mp hgF f).mp hf) (F.inv_mem hf))
    · exact conj_comm_mem_of_relIndex_two hr hgE hgF hf
  have hcF : ∀ f ∈ F, g * f = f * g :=
    commutes_of_step_of_odd hodd (hP2.to_le hEP) hcE hstepB
  exact commutes_of_step_of_odd hodd (hP2.to_le hFP) hcF hgtriv

end KerFinite

end S1422Loc

end CFSG.Quasithin
