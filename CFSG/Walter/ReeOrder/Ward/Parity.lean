module

public import CFSG.Walter.ReeOrder.Ward.Columns

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers

theorem sum_hom_mul_inv {H : Type*} [Group H] [Fintype H] (ν μ : H →* ℂˣ) :
    ∑ ρ : H, ((ν ρ : ℂˣ) : ℂ) * (((μ ρ)⁻¹ : ℂˣ) : ℂ) =
      if ν = μ then (Fintype.card H : ℂ) else 0 := by
  have h := sum_hom_units ((Units.coeHom ℂ).comp (ν / μ))
  have hcoe : ∀ ρ : H, ((Units.coeHom ℂ).comp (ν / μ)) ρ =
      ((ν ρ : ℂˣ) : ℂ) * (((μ ρ)⁻¹ : ℂˣ) : ℂ) := by
    intro ρ
    simp [div_eq_mul_inv]
  simp only [hcoe] at h
  rw [h]
  have hiff : (Units.coeHom ℂ).comp (ν / μ) = 1 ↔ ν = μ := by
    constructor
    · intro h1
      rw [← div_eq_one]
      ext ρ
      have := congrArg (fun f : H →* ℂ => f ρ) h1
      simpa using this
    · intro h1
      rw [h1]
      ext ρ
      simp
  by_cases hνμ : ν = μ
  · rw [ite_eq_left (hiff.mpr hνμ), ite_eq_left hνμ]
  · rw [ite_eq_right (fun h => hνμ (hiff.mp h)), ite_eq_right hνμ, Nat.cast_zero]

theorem sum_inv_hom {H : Type*} [Group H] [Fintype H] {μ : H →* ℂˣ} (hμ : μ ≠ 1) :
    ∑ ρ : H, (((μ ρ)⁻¹ : ℂˣ) : ℂ) = 0 := by
  have h := sum_hom_mul_inv (1 : H →* ℂˣ) μ
  rw [ite_eq_right (Ne.symm hμ)] at h
  simpa using h

theorem sum_off_one {H : Type*} [Group H] [Fintype H] (μ : H →* ℂˣ) (f g : H → ℂ)
    (h : ∀ ρ, ρ ≠ 1 → f ρ = g ρ) :
    ∑ ρ : H, f ρ * (((μ ρ)⁻¹ : ℂˣ) : ℂ) = ∑ ρ : H, g ρ * (((μ ρ)⁻¹ : ℂˣ) : ℂ) + (f 1 - g 1) := by
  have hsplit : ∀ ρ : H, f ρ * (((μ ρ)⁻¹ : ℂˣ) : ℂ) =
      g ρ * (((μ ρ)⁻¹ : ℂˣ) : ℂ) + (if ρ = 1 then f 1 - g 1 else 0) := by
    intro ρ
    by_cases hρ : ρ = 1
    · subst hρ
      simp
    · rw [h ρ hρ, ite_eq_right hρ, add_zero]
  rw [Finset.sum_congr rfl fun ρ _ => hsplit ρ, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem sum_const_off_one {H : Type*} [Group H] [Fintype H] {μ : H →* ℂˣ} (hμ : μ ≠ 1)
    (f : H → ℂ) (c : ℂ) (h : ∀ ρ, ρ ≠ 1 → f ρ = c) :
    ∑ ρ : H, f ρ * (((μ ρ)⁻¹ : ℂˣ) : ℂ) = f 1 - c := by
  rw [sum_off_one μ f (fun _ => c) h, ← Finset.mul_sum, sum_inv_hom hμ, mul_zero, zero_add]

theorem sum_pair {H : Type*} [Group H] [Fintype H] (ν μ : H →* ℂˣ) :
    ∑ ρ : H, (((ν ρ : ℂˣ) : ℂ) + (((ν ρ)⁻¹ : ℂˣ) : ℂ)) * (((μ ρ)⁻¹ : ℂˣ) : ℂ) =
      (if ν = μ then (Fintype.card H : ℂ) else 0) +
        (if ν⁻¹ = μ then (Fintype.card H : ℂ) else 0) := by
  rw [← sum_hom_mul_inv, ← sum_hom_mul_inv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [MonoidHom.inv_apply]
  ring

theorem hom_eq_one_of_sq {H : Type*} [Group H] [Fintype H] (hodd : Odd (Fintype.card H))
    {ν : H →* ℂˣ} (h : ν * ν = 1) : ν = 1 := by
  ext ρ
  obtain ⟨k, hk⟩ := hodd
  have hρ : ρ = (ρ ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, show (k + 1) * 2 = Fintype.card H + 1 by omega, pow_succ, pow_card_eq_one,
      one_mul]
  have h2 : ν (ρ ^ (k + 1)) * ν (ρ ^ (k + 1)) = 1 := by
    have := congrArg (fun f : H →* ℂˣ => f (ρ ^ (k + 1))) h
    simpa using this
  rw [hρ, map_pow, sq, h2]
  rfl

theorem exists_faithful {H : Type*} [Group H] [Fintype H] [IsCyclic H] :
    ∃ ν : H →* ℂˣ, Function.Injective ν := by
  have hpos : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  let e : H ≃* rootsOfUnity (Nat.card H) ℂ :=
    mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity (Nat.card H)).symm
  refine ⟨(rootsOfUnity (Nat.card H) ℂ).subtype.comp e.toMonoidHom, ?_⟩
  intro a b hab
  apply e.injective
  exact Subtype.ext hab

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

noncomputable def αfun (ρ : S.W.So) : S.W.So :=
  ⟨(S.A_So ρ.1 ρ.2).choose, (S.A_So ρ.1 ρ.2).choose_spec.1⟩

theorem αfun_spec (ρ : S.W.So) : S.A⁻¹ * S.κ ρ * S.A = S.κ (S.αfun ρ) :=
  (S.A_So ρ.1 ρ.2).choose_spec.2

noncomputable def α : S.W.So →* S.W.So where
  toFun := S.αfun
  map_one' := by
    apply Subtype.ext
    apply S.κ_inj
    rw [← S.αfun_spec 1]
    simp
  map_mul' ρ₁ ρ₂ := by
    apply Subtype.ext
    apply S.κ_inj
    rw [← S.αfun_spec, Subgroup.coe_mul, map_mul, Subgroup.coe_mul, map_mul, ← S.αfun_spec,
      ← S.αfun_spec]
    group

theorem α_spec (ρ : S.W.So) : S.A⁻¹ * S.κ ρ * S.A = S.κ (S.α ρ) := S.αfun_spec ρ

theorem α_injective : Function.Injective S.α := by
  intro ρ₁ ρ₂ h
  apply Subtype.ext
  apply S.κ_inj
  have h' : S.A⁻¹ * S.κ ρ₁ * S.A = S.A⁻¹ * S.κ ρ₂ * S.A := by
    rw [S.α_spec, S.α_spec, h]
  simpa using h'

theorem α_bijective : Function.Bijective S.α := Finite.injective_iff_bijective.mp S.α_injective

theorem α_eq_one_iff (ρ : S.W.So) : S.α ρ = 1 ↔ ρ = 1 := by
  constructor
  · intro h
    apply S.α_injective
    rw [h, map_one]
  · rintro rfl
    exact map_one _

theorem α_cube (ρ : S.W.So) : S.α (S.α (S.α ρ)) = ρ := by
  apply Subtype.ext
  apply S.κ_inj
  rw [← S.α_spec, ← S.α_spec, ← S.α_spec]
  have h3 : S.A * S.A * S.A = 1 := by
    rw [← pow_three', ← S.orderOf_A]
    exact pow_orderOf_eq_one _
  have h3' : S.A⁻¹ * S.A⁻¹ * S.A⁻¹ = 1 := by
    rw [← mul_inv_rev, ← mul_inv_rev, ← mul_assoc, h3, inv_one]
  calc S.A⁻¹ * (S.A⁻¹ * (S.A⁻¹ * S.κ ρ * S.A) * S.A) * S.A
      = (S.A⁻¹ * S.A⁻¹ * S.A⁻¹) * S.κ ρ * (S.A * S.A * S.A) := by simp only [mul_assoc]
    _ = S.κ ρ := by rw [h3, h3', one_mul, mul_one]

theorem α_ne_id : ∃ ρ : S.W.So, S.α ρ ≠ ρ := by
  obtain ⟨ρ, hρ, hne⟩ := S.A_not_comm
  refine ⟨⟨ρ, hρ⟩, fun h => hne ?_⟩
  have h1 := S.α_spec ⟨ρ, hρ⟩
  rw [h] at h1
  have : S.κ ρ * S.A = S.A * S.κ ρ := by
    calc S.κ ρ * S.A = S.A * (S.A⁻¹ * S.κ ρ * S.A) := by group
      _ = S.A * S.κ ρ := by rw [h1]
  exact this.symm

theorem So_odd : Odd (Fintype.card S.W.So) := by
  rw [Fintype.card_eq_nat_card]
  have h := S.W.So_card
  have h2 := S.W.q_mod
  have hq := S.W.q_odd
  obtain ⟨k, hk⟩ := hq
  rcases S.W.e_eq with he | he <;> subst he
  · refine Nat.odd_iff.mpr ?_
    omega
  · refine Nat.odd_iff.mpr ?_
    omega

theorem So_card_pos : 0 < Fintype.card S.W.So := Fintype.card_pos

theorem conj_A (ρ : S.W.So) :
    S.A⁻¹ * (S.J * S.κ (S.W.J' * ρ)) * S.A = S.J * S.κ (S.α ρ) := by
  have hJ' : S.κ S.W.J' * S.κ S.W.J' = 1 := by
    rw [← map_mul, ← sq, ← S.W.orderOf_J', pow_orderOf_eq_one, map_one]
  rw [map_mul]
  calc S.A⁻¹ * (S.J * (S.κ S.W.J' * S.κ ρ)) * S.A
      = (S.A⁻¹ * S.J * S.A) * (S.A⁻¹ * S.κ S.W.J' * S.A) * (S.A⁻¹ * S.κ ρ * S.A) := by group
    _ = S.κ S.W.J' * (S.J * S.κ S.W.J') * S.κ (S.α ρ) := by rw [S.A_J, S.A_J', S.α_spec]
    _ = S.J * (S.κ S.W.J' * S.κ S.W.J') * S.κ (S.α ρ) := by
        rw [← mul_assoc (S.κ S.W.J'), S.κ_comm, mul_assoc S.J]
    _ = S.J * S.κ (S.α ρ) := by rw [hJ', mul_one]

theorem σ_J'_So {χ : G → ℂ} (hχ : BlocksIsClassFunction χ) (ρ : S.W.So) :
    S.σ χ (S.W.J' * ρ) = S.σ χ (S.α ρ) := by
  simp only [σ]
  rw [← S.conj_A ρ]
  have h := hχ (S.J * S.κ (S.W.J' * ρ)) S.A⁻¹
  rw [inv_inv] at h
  exact h.symm

theorem M_identity {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (ρ : S.W.So) :
    ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * θ (S.W.J' * ρ) =
      ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * θ (S.α ρ) := by
  rw [← S.σ_expand hχ, ← S.σ_expand hχ]
  exact S.σ_J'_So (blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ)) ρ

variable {S}

noncomputable def LF (μ : S.W.So →* ℂˣ) (θ : L → ℂ) : ℂ :=
  ∑ ρ : S.W.So, θ (S.W.J' * ρ) * (((μ ρ)⁻¹ : ℂˣ) : ℂ)

noncomputable def RF (μ : S.W.So →* ℂˣ) (θ : L → ℂ) : ℂ :=
  ∑ ρ : S.W.So, θ (S.α ρ) * (((μ ρ)⁻¹ : ℂˣ) : ℂ)

variable (S) in
theorem fourier_identity {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (μ : S.W.So →* ℂˣ) :
    ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * LF (S := S) μ θ =
      ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * RF (S := S) μ θ := by
  simp only [LF, RF, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := (irreducibles_finite L).toFinset)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have h := S.M_identity hχ ρ
  calc ∑ θ ∈ (irreducibles_finite L).toFinset,
        (S.M χ θ : ℂ) * (θ (S.W.J' * ρ) * (((μ ρ)⁻¹ : ℂˣ) : ℂ))
      = (∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * θ (S.W.J' * ρ)) *
          (((μ ρ)⁻¹ : ℂˣ) : ℂ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun θ _ => by ring
    _ = (∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * θ (S.α ρ)) *
          (((μ ρ)⁻¹ : ℂˣ) : ℂ) := by rw [h]
    _ = _ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun θ _ => by ring

section Coefficients

variable {μ : S.W.So →* ℂˣ} (hμ : μ ≠ 1)
include hμ

theorem LF_const (θ : L → ℂ) (c : ℂ) (h : ∀ ρ : S.W.So, θ (S.W.J' * ρ) = c) :
    LF (S := S) μ θ = 0 := by
  simp only [LF, h, ← Finset.mul_sum, sum_inv_hom hμ, mul_zero]

theorem LF_one : LF (S := S) μ 1 = 0 := LF_const hμ 1 1 (fun _ => rfl)

theorem LF_θ2 : LF (S := S) μ S.W.θ2 = 0 :=
  LF_const hμ _ (-e) (fun ρ => (S.W.val_J'So ρ ρ.2).1)

theorem LF_θ3 : LF (S := S) μ S.W.θ3 = 0 :=
  LF_const hμ _ (-e) (fun ρ => (S.W.val_J'So ρ ρ.2).2.1)

theorem LF_θ4 : LF (S := S) μ S.W.θ4 = 0 :=
  LF_const hμ _ e (fun ρ => (S.W.val_J'So ρ ρ.2).2.2.1)

theorem LF_R {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) : LF (S := S) μ θ = 0 :=
  LF_const hμ _ 0 (fun ρ => (S.W.val_J'So ρ ρ.2).2.2.2 θ hθ)

omit hμ in
theorem LF_S {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    LF (S := S) μ θ = e * S.W.eps θ * ((if S.W.lam θ = μ then (Fintype.card S.W.So : ℂ) else 0) +
      (if (S.W.lam θ)⁻¹ = μ then (Fintype.card S.W.So : ℂ) else 0)) := by
  simp only [LF, S.W.valS_J'So θ hθ]
  rw [← sum_pair, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => by ring

theorem RF_off {θ : L → ℂ} (c : ℂ) (h : ∀ ρ : S.W.So, ρ ≠ 1 → θ ρ = c) :
    RF (S := S) μ θ = θ 1 - c := by
  rw [RF, sum_const_off_one hμ (fun ρ => θ (S.α ρ)) c
    (fun ρ hρ => h _ (fun h1 => hρ ((S.α_eq_one_iff ρ).mp h1)))]
  simp

theorem RF_one : RF (S := S) μ 1 = 0 := by
  rw [RF_off hμ 1 (fun _ _ => rfl)]
  simp

theorem RF_θ2 : RF (S := S) μ S.W.θ2 = ((q : ℂ) - e) / 2 := by
  rw [RF_off hμ e (fun ρ hρ => (S.W.val_So ρ ρ.2 (fun h => hρ (Subtype.ext h))).1), S.W.deg2]
  ring

theorem RF_θ3 : RF (S := S) μ S.W.θ3 = ((q : ℂ) - e) / 2 := by
  rw [RF_off hμ e (fun ρ hρ => (S.W.val_So ρ ρ.2 (fun h => hρ (Subtype.ext h))).2.1), S.W.deg3]
  ring

theorem RF_θ4 : RF (S := S) μ S.W.θ4 = (q : ℂ) - e := by
  rw [RF_off hμ e (fun ρ hρ => (S.W.val_So ρ ρ.2 (fun h => hρ (Subtype.ext h))).2.2.1),
    S.W.deg4]

theorem RF_R {θ : L → ℂ} (hθ : θ ∈ S.W.RFam) : RF (S := S) μ θ = (q : ℂ) - e := by
  rw [RF_off hμ 0 (fun ρ hρ => (S.W.val_So ρ ρ.2 (fun h => hρ (Subtype.ext h))).2.2.2 θ hθ),
    S.W.degR θ hθ, sub_zero]

omit hμ in
theorem RF_S {θ : L → ℂ} (hθ : θ ∈ S.W.SFam) :
    RF (S := S) μ θ = e * ((if (S.W.lam θ).comp S.α = μ then (Fintype.card S.W.So : ℂ) else 0) +
      (if ((S.W.lam θ).comp S.α)⁻¹ = μ then (Fintype.card S.W.So : ℂ) else 0)) + ((q : ℂ) - e) := by
  have h := sum_off_one μ (fun ρ => θ (S.α ρ))
    (fun ρ => e * ((((S.W.lam θ).comp S.α ρ : ℂˣ) : ℂ) +
      ((((S.W.lam θ).comp S.α ρ)⁻¹ : ℂˣ) : ℂ)))
    (fun ρ hρ => by
      rw [S.W.valS_So θ hθ (S.α ρ) (fun h1 => hρ ((S.α_eq_one_iff ρ).mp h1))]
      rfl)
  rw [RF, h]
  simp only [map_one, Units.val_one, inv_one, OneMemClass.coe_one]
  rw [S.W.degS θ hθ, ← sum_pair, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun ρ _ => by ring
  · ring

end Coefficients

theorem lam_eq_iff {θ₀ θ : L → ℂ} (h₀ : θ₀ ∈ S.W.SFam) (hθ : θ ∈ S.W.SFam) :
    S.W.lam θ = S.W.lam θ₀ ↔ θ = θ₀ ∨ θ = S.W.sbar θ₀ := by
  constructor
  · intro h
    exact S.W.lam_inj θ₀ h₀ θ hθ (Or.inl h)
  · rintro (rfl | rfl)
    · rfl
    · exact S.W.lam_sbar θ₀ h₀

theorem lam_ne_inv {θ₀ θ : L → ℂ} (h₀ : θ₀ ∈ S.W.SFam) (hθ : θ ∈ S.W.SFam) :
    S.W.lam θ ≠ (S.W.lam θ₀)⁻¹ := by
  intro h
  have h' := S.W.lam_inj θ₀ h₀ θ hθ (Or.inr h)
  have heq : S.W.lam θ = S.W.lam θ₀ := (lam_eq_iff h₀ hθ).mpr h'
  rw [heq] at h
  apply S.W.lam_ne θ₀ h₀
  apply hom_eq_one_of_sq S.So_odd
  nth_rewrite 2 [h]
  exact mul_inv_cancel (S.W.lam θ₀)

theorem sum_lam_eq (f : (L → ℂ) → ℂ) {θ₀ : L → ℂ} (h₀ : θ₀ ∈ S.W.SFam) (c : ℂ) :
    ∑ θ ∈ S.W.SFam, f θ * ((if S.W.lam θ = S.W.lam θ₀ then c else 0) +
      (if (S.W.lam θ)⁻¹ = S.W.lam θ₀ then c else 0)) = (f θ₀ + f (S.W.sbar θ₀)) * c := by
  have h2 : ∀ θ ∈ S.W.SFam, ¬ (S.W.lam θ)⁻¹ = S.W.lam θ₀ := by
    intro θ hθ h
    apply lam_ne_inv h₀ hθ
    rw [← h]
    exact (inv_inv (S.W.lam θ)).symm
  rw [Finset.sum_congr rfl fun θ hθ => by rw [ite_eq_right (h2 θ hθ), add_zero]]
  have hne : θ₀ ≠ S.W.sbar θ₀ := (S.W.sbar_ne θ₀ h₀).symm
  rw [← Finset.sum_filter_add_sum_filter_not S.W.SFam (fun θ => S.W.lam θ = S.W.lam θ₀)]
  have hfilt : S.W.SFam.filter (fun θ => S.W.lam θ = S.W.lam θ₀) = {θ₀, S.W.sbar θ₀} := by
    ext θ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hθ, h⟩
      exact (lam_eq_iff h₀ hθ).mp h
    · rintro (rfl | rfl)
      · exact ⟨h₀, rfl⟩
      · exact ⟨S.W.sbar_mem θ₀ h₀, S.W.lam_sbar θ₀ h₀⟩
  rw [hfilt, Finset.sum_pair hne, Finset.sum_eq_zero (fun θ hθ => by
    rw [Finset.mem_filter] at hθ
    rw [ite_eq_right hθ.2, mul_zero])]
  rw [ite_eq_left rfl, ite_eq_left (S.W.lam_sbar θ₀ h₀)]
  ring

theorem comp_α_inj (ν ν' : S.W.So →* ℂˣ) : ν.comp S.α = ν'.comp S.α ↔ ν = ν' := by
  constructor
  · intro h
    ext ρ
    obtain ⟨ρ', rfl⟩ := S.α_bijective.2 ρ
    have := congrArg (fun f : S.W.So →* ℂˣ => f ρ') h
    simp only [MonoidHom.comp_apply] at this
    rw [this]
  · intro h
    rw [h]

theorem comp_α_inv (ν : S.W.So →* ℂˣ) : (ν.comp S.α)⁻¹ = ν⁻¹.comp S.α := by
  ext ρ
  simp

theorem sum_lam_comp_eq (f : (L → ℂ) → ℂ) {θ₁ : L → ℂ} (h₁ : θ₁ ∈ S.W.SFam) (c : ℂ) :
    ∑ θ ∈ S.W.SFam, f θ * ((if (S.W.lam θ).comp S.α = (S.W.lam θ₁).comp S.α then c else 0) +
      (if ((S.W.lam θ).comp S.α)⁻¹ = (S.W.lam θ₁).comp S.α then c else 0)) =
      (f θ₁ + f (S.W.sbar θ₁)) * c := by
  rw [← sum_lam_eq f h₁ c]
  refine Finset.sum_congr rfl fun θ _ => ?_
  simp only [comp_α_inj, comp_α_inv]

theorem sum_lam_comp_inv_eq (f : (L → ℂ) → ℂ) {θ₁ : L → ℂ} (h₁ : θ₁ ∈ S.W.SFam) (c : ℂ) :
    ∑ θ ∈ S.W.SFam, f θ * ((if (S.W.lam θ).comp S.α = ((S.W.lam θ₁).comp S.α)⁻¹ then c else 0) +
      (if ((S.W.lam θ).comp S.α)⁻¹ = ((S.W.lam θ₁).comp S.α)⁻¹ then c else 0)) =
      (f θ₁ + f (S.W.sbar θ₁)) * c := by
  rw [← sum_lam_eq f h₁ c]
  refine Finset.sum_congr rfl fun θ _ => ?_
  have hc1 : (S.W.lam θ).comp S.α = ((S.W.lam θ₁).comp S.α)⁻¹ ↔
      (S.W.lam θ)⁻¹ = S.W.lam θ₁ := by
    rw [comp_α_inv, comp_α_inj]
    constructor
    · intro h
      rw [h]
      exact inv_inv (S.W.lam θ₁)
    · intro h
      rw [← h]
      exact (inv_inv (S.W.lam θ)).symm
  have hc2 : ((S.W.lam θ).comp S.α)⁻¹ = ((S.W.lam θ₁).comp S.α)⁻¹ ↔
      S.W.lam θ = S.W.lam θ₁ := by
    rw [comp_α_inv, comp_α_inv, comp_α_inj]
    constructor
    · intro h
      have h' := congrArg (fun x : S.W.So →* ℂˣ => x⁻¹) h
      calc S.W.lam θ = (S.W.lam θ)⁻¹⁻¹ := (inv_inv (S.W.lam θ)).symm
        _ = (S.W.lam θ₁)⁻¹⁻¹ := h'
        _ = S.W.lam θ₁ := inv_inv (S.W.lam θ₁)
    · intro h
      rw [h]
  simp only [hc1, hc2]
  ring

variable (S) in
theorem dS_parity {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {θ₀ θ₁ : L → ℂ} (h₀ : θ₀ ∈ S.W.SFam)
    (h₁ : θ₁ ∈ S.W.SFam)
    (hα : (S.W.lam θ₁).comp S.α = S.W.lam θ₀ ∨ (S.W.lam θ₁).comp S.α = (S.W.lam θ₀)⁻¹) :
    ∃ k : ℤ, S.dS χ θ₀ = S.dS χ θ₁ + 2 * k := by
  set μ := S.W.lam θ₀ with hμdef
  have hμ : μ ≠ 1 := S.W.lam_ne θ₀ h₀
  set m : ℂ := (Fintype.card S.W.So : ℂ) with hm
  have h := S.fourier_identity hχ μ
  have hLS : ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * LF (S := S) μ θ =
      ∑ θ ∈ S.W.SFam, (S.W.eps θ * S.M χ θ : ℂ) * (e * ((if S.W.lam θ = μ then m else 0) +
        (if (S.W.lam θ)⁻¹ = μ then m else 0))) :=
    Finset.sum_congr rfl fun θ hθ => by rw [LF_S hθ]; ring
  have hLR : ∑ θ ∈ S.W.RFam, (S.M χ θ : ℂ) * LF (S := S) μ θ = 0 :=
    Finset.sum_eq_zero fun θ hθ => by rw [LF_R hμ hθ, mul_zero]
  have hL : ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * LF (S := S) μ θ =
      (S.W.eps θ₀ * S.M χ θ₀ + S.W.eps (S.W.sbar θ₀) * S.M χ (S.W.sbar θ₀)) * (e * m) := by
    rw [S.W.sum_irr, LF_one hμ, LF_θ2 hμ, LF_θ3 hμ, LF_θ4 hμ, hLR, hLS]
    have := sum_lam_eq (fun θ => (S.W.eps θ * S.M χ θ : ℂ)) h₀ (e * m)
    rw [← this]
    simp only [mul_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl fun θ _ => ?_
    split_ifs <;> ring
  have hRS : ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * RF (S := S) μ θ =
      ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * (e * ((if (S.W.lam θ).comp S.α = μ then m else 0) +
        (if ((S.W.lam θ).comp S.α)⁻¹ = μ then m else 0))) +
        ((q : ℂ) - e) * ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun θ hθ => by rw [RF_S hθ]; ring
  have hRR : ∑ θ ∈ S.W.RFam, (S.M χ θ : ℂ) * RF (S := S) μ θ =
      ((q : ℂ) - e) * ∑ θ ∈ S.W.RFam, (S.M χ θ : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun θ hθ => by rw [RF_R hμ hθ]; ring
  have hR1 : ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ) * (e * ((if (S.W.lam θ).comp S.α = μ then m else 0) +
        (if ((S.W.lam θ).comp S.α)⁻¹ = μ then m else 0))) =
      (S.M χ θ₁ + S.M χ (S.W.sbar θ₁)) * (e * m) := by
    rcases hα with hα | hα
    · have := sum_lam_comp_eq (fun θ => (S.M χ θ : ℂ)) h₁ (e * m)
      rw [← hα, ← this]
      refine Finset.sum_congr rfl fun θ _ => ?_
      split_ifs <;> ring
    · have hμ' : μ = ((S.W.lam θ₁).comp S.α)⁻¹ := by rw [hα]; exact (inv_inv μ).symm
      have := sum_lam_comp_inv_eq (fun θ => (S.M χ θ : ℂ)) h₁ (e * m)
      rw [hμ', ← this]
      refine Finset.sum_congr rfl fun θ _ => ?_
      split_ifs <;> ring
  have hR : ∑ θ ∈ (irreducibles_finite L).toFinset, (S.M χ θ : ℂ) * RF (S := S) μ θ =
      (S.M χ S.W.θ2 + S.M χ S.W.θ3) * (((q : ℂ) - e) / 2) + S.M χ S.W.θ4 * ((q : ℂ) - e) +
        ((q : ℂ) - e) * ∑ θ ∈ S.W.RFam, (S.M χ θ : ℂ) +
        ((S.M χ θ₁ + S.M χ (S.W.sbar θ₁)) * (e * m) +
          ((q : ℂ) - e) * ∑ θ ∈ S.W.SFam, (S.M χ θ : ℂ)) := by
    rw [S.W.sum_irr, RF_one hμ, RF_θ2 hμ, RF_θ3 hμ, RF_θ4 hμ, hRR, hRS, hR1]
    ring
  rw [hL, hR] at h
  have hqm : (q : ℂ) - e = 4 * m := by
    have := S.W.So_card
    rw [hm, Fintype.card_eq_nat_card]
    have h' : ((q : ℤ) - e : ℤ) = 4 * (Nat.card S.W.So : ℤ) := by linarith
    exact_mod_cast h'
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact_mod_cast S.So_card_pos.ne'
  have heps : S.W.eps (S.W.sbar θ₀) = -S.W.eps θ₀ := S.W.eps_sbar θ₀ h₀
  rw [heps, hqm] at h
  have hdiv : ((e * (S.W.eps θ₀ * (S.M χ θ₀ - S.M χ (S.W.sbar θ₀))) -
      e * (S.M χ θ₁ + S.M χ (S.W.sbar θ₁)) : ℤ) : ℂ) =
      ((2 * (S.M χ S.W.θ2 + S.M χ S.W.θ3) + 4 * S.M χ S.W.θ4 +
        4 * ∑ θ ∈ S.W.RFam, S.M χ θ + 4 * ∑ θ ∈ S.W.SFam, S.M χ θ : ℤ) : ℂ) := by
    apply mul_left_cancel₀ hm0
    push_cast at h ⊢
    linear_combination h
  have hdiv' := Int.cast_injective hdiv
  have he2 : e * e = 1 := S.W.e_sq
  simp only [dS]
  rcases S.W.eps_eq θ₀ h₀ with hε | hε <;> rw [hε] at hdiv'
  · exact ⟨S.M χ (S.W.sbar θ₀) + e * ((S.M χ S.W.θ2 + S.M χ S.W.θ3) + 2 * S.M χ S.W.θ4 +
      2 * ∑ θ ∈ S.W.RFam, S.M χ θ + 2 * ∑ θ ∈ S.W.SFam, S.M χ θ),
      by linear_combination e * hdiv' - (S.M χ θ₀ - S.M χ (S.W.sbar θ₀) -
        (S.M χ θ₁ + S.M χ (S.W.sbar θ₁))) * he2⟩
  · exact ⟨S.M χ θ₀ + e * ((S.M χ S.W.θ2 + S.M χ S.W.θ3) + 2 * S.M χ S.W.θ4 +
      2 * ∑ θ ∈ S.W.RFam, S.M χ θ + 2 * ∑ θ ∈ S.W.SFam, S.M χ θ),
      by linear_combination e * hdiv' - (S.M χ (S.W.sbar θ₀) - S.M χ θ₀ -
        (S.M χ θ₁ + S.M χ (S.W.sbar θ₁))) * he2⟩

variable (S) in
theorem So_card_gt : 1 < Fintype.card S.W.So := by
  rw [Fintype.card_eq_nat_card]
  have h1 := S.W.So_card
  have h2 := S.q_ge
  rcases S.W.e_eq with he | he <;> subst he <;> omega

variable (S) in
theorem So_eq_one_of_sq {ρ : S.W.So} (h : ρ * ρ = 1) : ρ = 1 := by
  have h2 : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h])
  have hodd : orderOf ρ ∣ Fintype.card S.W.So := orderOf_dvd_card
  have h1 : orderOf ρ = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd
      exact absurd (even_iff_two_dvd.mpr hodd) (Nat.not_even_iff_odd.mpr S.So_odd)
  exact orderOf_eq_one_iff.mp h1

variable (S) in
theorem α_ne_inv : ¬ ∀ ρ : S.W.So, S.α ρ = ρ⁻¹ := by
  intro h
  have hall : ∀ ρ : S.W.So, ρ = 1 := by
    intro ρ
    apply S.So_eq_one_of_sq
    have h3 := S.α_cube ρ
    rw [h ρ, map_inv, h ρ, inv_inv, h ρ] at h3
    calc ρ * ρ = ρ * ρ⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel ρ
  have := S.So_card_gt
  rw [Fintype.one_lt_card_iff] at this
  obtain ⟨a, b, hab⟩ := this
  exact hab (by rw [hall a, hall b])

variable (S) in
theorem faithful_comp_ne {ν : S.W.So →* ℂˣ} (hν : Function.Injective ν) :
    ν.comp S.α ≠ ν ∧ ν.comp S.α ≠ ν⁻¹ := by
  constructor
  · intro h
    obtain ⟨ρ, hρ⟩ := S.α_ne_id
    apply hρ
    apply hν
    have := congrArg (fun f : S.W.So →* ℂˣ => f ρ) h
    simpa using this
  · intro h
    apply S.α_ne_inv
    intro ρ
    apply hν
    have := congrArg (fun f : S.W.So →* ℂˣ => f ρ) h
    simp only [MonoidHom.comp_apply, MonoidHom.inv_apply] at this
    rw [this, map_inv]

variable (S) in
theorem faithful_comp_comp_ne {ν : S.W.So →* ℂˣ} (hν : Function.Injective ν) :
    (ν.comp S.α).comp S.α ≠ ν ∧ (ν.comp S.α).comp S.α ≠ ν⁻¹ := by
  constructor
  · intro h
    obtain ⟨ρ, hρ⟩ := S.α_ne_id
    apply hρ
    have h2 : ∀ x : S.W.So, S.α (S.α x) = x := by
      intro x
      apply hν
      have := congrArg (fun f : S.W.So →* ℂˣ => f x) h
      simpa using this
    have := S.α_cube ρ
    rw [h2 (S.α ρ)] at this
    exact this
  · intro h
    apply S.α_ne_inv
    have h2 : ∀ x : S.W.So, S.α (S.α x) = x⁻¹ := by
      intro x
      apply hν
      have := congrArg (fun f : S.W.So →* ℂˣ => f x) h
      simp only [MonoidHom.comp_apply, MonoidHom.inv_apply] at this
      rw [this, map_inv]
    intro ρ
    have h4 := h2 (S.α ρ)
    rw [S.α_cube] at h4
    calc S.α ρ = ((S.α ρ)⁻¹)⁻¹ := (inv_inv _).symm
      _ = ρ⁻¹ := by rw [← h4]

theorem injective_of_comp {ν ν' : S.W.So →* ℂˣ} (hν : Function.Injective ν)
    (h : ν'.comp S.α = ν ∨ ν'.comp S.α = ν⁻¹) : Function.Injective ν' := by
  intro a b hab
  obtain ⟨a', rfl⟩ := S.α_bijective.2 a
  obtain ⟨b', rfl⟩ := S.α_bijective.2 b
  congr 1
  rcases h with h | h
  · apply hν
    rw [← h]
    simpa using hab
  · apply hν
    have ha := congrArg (fun f : S.W.So →* ℂˣ => f a') h
    have hb := congrArg (fun f : S.W.So →* ℂˣ => f b') h
    simp only [MonoidHom.comp_apply, MonoidHom.inv_apply] at ha hb
    rw [hab] at ha
    rw [ha] at hb
    exact inv_injective hb

theorem injective_inv {ν : S.W.So →* ℂˣ} (hν : Function.Injective ν) :
    Function.Injective ν⁻¹ := by
  intro a b hab
  apply hν
  simpa using hab

variable (S) in
theorem exists_lift {ν : S.W.So →* ℂˣ} (hν : Function.Injective ν) :
    ∃ θ ∈ S.W.SFam, (S.W.lam θ).comp S.α = ν ∨ (S.W.lam θ).comp S.α = ν⁻¹ := by
  let αe : S.W.So ≃* S.W.So := MulEquiv.ofBijective S.α S.α_bijective
  have hν1 : ν.comp αe.symm.toMonoidHom ≠ 1 := by
    intro h
    have hcard := S.So_card_gt
    rw [Fintype.one_lt_card_iff] at hcard
    obtain ⟨a, b, hab⟩ := hcard
    apply hab
    apply αe.symm.injective
    apply hν
    have ha := congrArg (fun f : S.W.So →* ℂˣ => f a) h
    have hb := congrArg (fun f : S.W.So →* ℂˣ => f b) h
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply] at ha hb
    rw [MulEquiv.coe_toMonoidHom] at ha hb
    rw [ha, hb]
  have hsymm : ∀ ρ : S.W.So, αe.symm (S.α ρ) = ρ := fun ρ => αe.symm_apply_apply ρ
  obtain ⟨θ, hθ, h | h⟩ := S.W.lam_surj _ hν1
  · refine ⟨θ, hθ, Or.inl ?_⟩
    rw [h]
    ext ρ
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm]
  · refine ⟨θ, hθ, Or.inr ?_⟩
    rw [h]
    ext ρ
    simp only [MonoidHom.comp_apply, MonoidHom.inv_apply, MulEquiv.coe_toMonoidHom, hsymm]

variable (S) in
theorem exists_orbit : ∃ θ₀ ∈ S.W.SFam, ∃ θ₁ ∈ S.W.SFam, ∃ θ₂ ∈ S.W.SFam,
    ((S.W.lam θ₁).comp S.α = S.W.lam θ₀ ∨ (S.W.lam θ₁).comp S.α = (S.W.lam θ₀)⁻¹) ∧
    ((S.W.lam θ₂).comp S.α = S.W.lam θ₁ ∨ (S.W.lam θ₂).comp S.α = (S.W.lam θ₁)⁻¹) ∧
    S.W.lam θ₀ ≠ S.W.lam θ₁ ∧ S.W.lam θ₁ ≠ S.W.lam θ₂ ∧ S.W.lam θ₀ ≠ S.W.lam θ₂ := by
  have := S.W.So_cyclic
  obtain ⟨ν, hν⟩ := exists_faithful (H := S.W.So)
  have hν1 : ν ≠ 1 := by
    intro h
    have hcard := S.So_card_gt
    rw [Fintype.one_lt_card_iff] at hcard
    obtain ⟨a, b, hab⟩ := hcard
    apply hab
    apply hν
    rw [h]
    rfl
  obtain ⟨θ₀, h₀, hθ₀⟩ := S.W.lam_surj ν hν1
  have hinj₀ : Function.Injective (S.W.lam θ₀) := by
    rcases hθ₀ with h | h
    · rw [h]; exact hν
    · rw [h]; exact injective_inv hν
  obtain ⟨θ₁, h₁, hα₁⟩ := S.exists_lift hinj₀
  have hinj₁ : Function.Injective (S.W.lam θ₁) := injective_of_comp hinj₀ hα₁
  obtain ⟨θ₂, h₂, hα₂⟩ := S.exists_lift hinj₁
  refine ⟨θ₀, h₀, θ₁, h₁, θ₂, h₂, hα₁, hα₂, ?_, ?_, ?_⟩
  · intro h
    rw [← h] at hα₁
    exact hα₁.elim (S.faithful_comp_ne hinj₀).1 (S.faithful_comp_ne hinj₀).2
  · intro h
    rw [← h] at hα₂
    exact hα₂.elim (S.faithful_comp_ne hinj₁).1 (S.faithful_comp_ne hinj₁).2
  · intro h
    rw [← h] at hα₂
    have hcc : (S.W.lam θ₀).comp S.α = S.W.lam θ₁ ∨ (S.W.lam θ₀).comp S.α = (S.W.lam θ₁)⁻¹ :=
      hα₂
    have key : ((S.W.lam θ₀).comp S.α).comp S.α = S.W.lam θ₀ ∨
        ((S.W.lam θ₀).comp S.α).comp S.α = (S.W.lam θ₀)⁻¹ := by
      rcases hcc with h1 | h1 <;> rcases hα₁ with h2 | h2
      · left; rw [h1, h2]
      · right; rw [h1, h2]
      · right; rw [h1, ← comp_α_inv, h2]
      · left; rw [h1, ← comp_α_inv, h2]; exact inv_inv (S.W.lam θ₀)
    exact key.elim (S.faithful_comp_comp_ne hinj₀).1 (S.faithful_comp_comp_ne hinj₀).2

end WardSetup

end CFSG.Walter.Ward
