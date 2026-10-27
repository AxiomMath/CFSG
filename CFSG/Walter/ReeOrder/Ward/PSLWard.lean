module

public import CFSG.Walter.ReeOrder.Ward.PSLData

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG

@[expose] def invSetoid (A : Type*) [Group A] : Setoid A where
  r a b := b = a ∨ b = a⁻¹
  iseqv := by
    refine ⟨fun a => Or.inl rfl, fun {a b} h => ?_, fun {a b c} h1 h2 => ?_⟩
    · rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (inv_inv a).symm
    · rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (inv_inv a)

@[expose] noncomputable def nrm {A : Type*} [Group A] (a : A) : A :=
  (Quotient.mk (invSetoid A) a).out

theorem nrm_cases {A : Type*} [Group A] (a : A) : nrm a = a ∨ nrm a = a⁻¹ := by
  have h : a = nrm a ∨ a = (nrm a)⁻¹ := @Quotient.mk_out _ (invSetoid A) a
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (inv_eq_iff_eq_inv.mpr h).symm

theorem nrm_inv {A : Type*} [Group A] (a : A) : nrm a⁻¹ = nrm a := by
  unfold nrm
  congr 1
  exact Quotient.sound (Or.inr (inv_inv a).symm)

theorem eq_or_eq_inv_of_nrm {A : Type*} [Group A] {a b : A}
    (h : nrm a = nrm b ∨ nrm a = (nrm b)⁻¹) : a = b ∨ a = b⁻¹ := by
  rcases nrm_cases a with ha | ha <;> rcases nrm_cases b with hb | hb <;>
    rw [ha, hb] at h <;> rcases h with h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inl (by rw [h, inv_inv])
  · exact Or.inr (by rw [← h, inv_inv])
  · exact Or.inl (inv_injective h)
  · exact Or.inl (inv_injective h)
  · exact Or.inr (by rw [← inv_inv a, h, inv_inv])

theorem conj_units_hom' {K : Type} [Group K] [Finite K] (χ : K →* ℂˣ) (g : K) :
    starRingEnd ℂ (χ g : ℂ) = ((χ g)⁻¹ : ℂˣ) := by
  have hfin : (χ g) ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hnorm : ‖(χ g : ℂ)‖ = 1 := by
    have h1 : ‖(χ g : ℂ)‖ ^ orderOf g = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, hfin, Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (orderOf_pos g).ne').mp h1
  rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj hnorm]

theorem conj_sym {K : Type} [Group K] [Finite K] (χ : K →* ℂˣ) (g : K) :
    starRingEnd ℂ ((χ g : ℂ) + ((χ g)⁻¹ : ℂˣ)) = (χ g : ℂ) + ((χ g)⁻¹ : ℂˣ) := by
  rw [map_add, conj_units_hom', Units.val_inv_eq_inv_val, map_inv₀, conj_units_hom',
    Units.val_inv_eq_inv_val, inv_inv, add_comm]

namespace PSLData

variable {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ} (D : PSLData L q e)

@[expose] noncomputable def J'E : D.E := ⟨D.J', D.J'_mem⟩

theorem beta_J'_cases (β : D.E →* ℂˣ) : β D.J'E = 1 ∨ β D.J'E = -1 := by
  apply units_sq_eq_one
  rw [← map_pow]
  have : D.J'E ^ 2 = 1 := Subtype.ext (by
    change D.J' ^ 2 = 1
    rw [sq, D.J'_mul_J'])
  rw [this, map_one]

theorem χ₀_J'E : D.χ₀ D.J'E = -1 := D.χ₀_J'

theorem beta_J'_inv (β : D.E →* ℂˣ) : (β D.J'E)⁻¹ = β D.J'E := by
  rcases D.beta_J'_cases β with h | h <;> rw [h] <;> simp

@[expose] noncomputable def res (β : D.E →* ℂˣ) : D.So →* ℂˣ :=
  β.comp (Subgroup.inclusion D.So_le_E)

theorem res_apply (β : D.E →* ℂˣ) (ρ : D.So) : D.res β ρ = β ⟨ρ, D.So_le_E ρ.2⟩ := rfl

theorem res_mul (β β' : D.E →* ℂˣ) : D.res (β * β') = D.res β * D.res β' := by
  ext ρ
  rfl

theorem res_inv (β : D.E →* ℂˣ) : D.res β⁻¹ = (D.res β)⁻¹ := by
  ext ρ
  rfl

theorem res_χ₀ : D.res D.χ₀ = 1 := by
  ext ρ
  rw [res_apply, D.χ₀_So ρ.2]
  rfl

theorem sq_eq_one_of_res {β : D.E →* ℂˣ} (h : D.res β = 1) : β ^ 2 = 1 := by
  ext ⟨x, hx⟩
  rw [MonoidHom.pow_apply, ← map_pow]
  have h1 : (⟨x, hx⟩ : D.E) ^ 2 = ⟨x ^ 2, D.So_le_E (D.sq_mem_So hx)⟩ := rfl
  rw [h1]
  have := congrArg (fun μ : D.So →* ℂˣ => μ ⟨x ^ 2, D.sq_mem_So hx⟩) h
  simp only [res_apply, MonoidHom.one_apply] at this
  rw [this]
  rfl

theorem eq_one_or_χ₀ {ψ : D.E →* ℂˣ} (h : D.res ψ = 1) : ψ = 1 ∨ ψ = D.χ₀ := by
  have hS : ∀ {ρ : L} (hρ : ρ ∈ D.So), ψ ⟨ρ, D.So_le_E hρ⟩ = 1 := fun {ρ} hρ => by
    have := congrArg (fun μ : D.So →* ℂˣ => μ ⟨ρ, hρ⟩) h
    simpa only [res_apply, MonoidHom.one_apply] using this
  have hsplit : ∀ x : D.E, x.1 ∈ D.So ∨
      ∃ ρ, ∃ hρ : ρ ∈ D.So, x = D.J'E * ⟨ρ, D.So_le_E hρ⟩ := by
    intro x
    rcases D.mem_E_cases x.2 with hx | ⟨ρ, hρ, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨ρ, hρ, Subtype.ext hx⟩
  rcases D.beta_J'_cases ψ with hJ | hJ
  · left
    ext x
    rcases hsplit x with hx | ⟨ρ, hρ, rfl⟩
    · rw [show x = ⟨x.1, D.So_le_E hx⟩ from rfl, hS hx]
      simp
    · rw [map_mul, hJ, hS hρ]
      simp
  · right
    ext x
    rcases hsplit x with hx | ⟨ρ, hρ, rfl⟩
    · rw [show x = ⟨x.1, D.So_le_E hx⟩ from rfl, hS hx, D.χ₀_So hx]
    · rw [map_mul, map_mul, hJ, hS hρ, D.χ₀_J'E, D.χ₀_So hρ]

theorem χ₀_inv : D.χ₀⁻¹ = D.χ₀ := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.inv_apply]
  have h := D.χ₀_sq_apply x
  rw [sq] at h
  exact inv_eq_of_mul_eq_one_right h

theorem res_mul_χ₀ (β : D.E →* ℂˣ) : D.res (β * D.χ₀) = D.res β := by
  refine MonoidHom.ext fun ρ => ?_
  simp only [res_apply, MonoidHom.mul_apply, D.χ₀_So ρ.2, mul_one]

theorem mul_χ₀_χ₀ (β : D.E →* ℂˣ) : β * D.χ₀ * D.χ₀ = β := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.mul_apply, mul_assoc, ← sq, D.χ₀_sq_apply, mul_one]

theorem inv_mul_χ₀ (β : D.E →* ℂˣ) : (β * D.χ₀)⁻¹ * D.χ₀ = β⁻¹ := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_mul_cancel_right]

theorem sq_mul_χ₀ (β : D.E →* ℂˣ) : (β * D.χ₀) ^ 2 = β ^ 2 := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.pow_apply, MonoidHom.mul_apply, mul_pow, D.χ₀_sq_apply, mul_one]

theorem XE_inv {β : D.E →* ℂˣ} (hβ : β ^ 2 ≠ 1) : D.XE β⁻¹ = D.XE β :=
  (D.XE_eq_iff β β⁻¹ hβ).mpr (Or.inr rfl)

theorem XE_mem {β : D.E →* ℂˣ} (hβ : β ^ 2 ≠ 1) : D.XE β ∈ D.SFam :=
  (D.mem_SFam _).mpr ⟨β, hβ, rfl⟩

@[expose] noncomputable def betaOf (θ : L → ℂ) : D.E →* ℂˣ :=
  if h : ∃ β : D.E →* ℂˣ, β ^ 2 ≠ 1 ∧ D.XE β = θ then h.choose else 1

theorem betaOf_spec {θ : L → ℂ} (hθ : θ ∈ D.SFam) :
    (D.betaOf θ) ^ 2 ≠ 1 ∧ D.XE (D.betaOf θ) = θ := by
  have h := (D.mem_SFam θ).mp hθ
  rw [betaOf, dite_eq_left h]
  exact h.choose_spec

theorem betaOf_XE {β : D.E →* ℂˣ} (hβ : β ^ 2 ≠ 1) :
    D.betaOf (D.XE β) = β ∨ D.betaOf (D.XE β) = β⁻¹ :=
  (D.XE_eq_iff β _ hβ).mp (D.betaOf_spec (D.XE_mem hβ)).2

@[expose] noncomputable def lam (θ : L → ℂ) : D.So →* ℂˣ := nrm (D.res (D.betaOf θ))

@[expose] noncomputable def eps (θ : L → ℂ) : ℤ := if D.betaOf θ D.J'E = 1 then 1 else -1

@[expose] noncomputable def sbar (θ : L → ℂ) : L → ℂ := D.XE (D.betaOf θ * D.χ₀)

theorem eps_val (θ : L → ℂ) : ((D.eps θ : ℤ) : ℂ) = (D.betaOf θ D.J'E : ℂ) := by
  unfold eps
  rcases D.beta_J'_cases (D.betaOf θ) with h | h
  · rw [ite_eq_left h, h]
    simp
  · have hne : D.betaOf θ D.J'E ≠ 1 := by
      rw [h]
      intro h'
      have := congrArg Units.val h'
      norm_num at this
    rw [ite_eq_right hne, h]
    simp

theorem sym_lam (θ : L → ℂ) (ρ : D.So) :
    ((D.lam θ ρ : ℂˣ) : ℂ) + (((D.lam θ ρ)⁻¹ : ℂˣ) : ℂ) =
      ((D.betaOf θ ⟨ρ, D.So_le_E ρ.2⟩ : ℂˣ) : ℂ) +
        (((D.betaOf θ ⟨ρ, D.So_le_E ρ.2⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold lam
  rcases nrm_cases (D.res (D.betaOf θ)) with h | h <;> rw [h]
  · rfl
  · rw [MonoidHom.inv_apply, inv_inv, res_apply, add_comm]

theorem lam_ne {θ : L → ℂ} (hθ : θ ∈ D.SFam) : D.lam θ ≠ 1 := by
  intro h
  have hres : D.res (D.betaOf θ) = 1 := by
    unfold lam at h
    rcases nrm_cases (D.res (D.betaOf θ)) with h' | h'
    · rw [← h', h]
    · exact inv_eq_one.mp (h'.symm.trans h)
  exact (D.betaOf_spec hθ).1 (D.sq_eq_one_of_res hres)

theorem sbar_mem {θ : L → ℂ} (hθ : θ ∈ D.SFam) : D.sbar θ ∈ D.SFam :=
  D.XE_mem (by rw [D.sq_mul_χ₀]; exact (D.betaOf_spec hθ).1)

theorem betaOf_sbar {θ : L → ℂ} (hθ : θ ∈ D.SFam) :
    D.betaOf (D.sbar θ) = D.betaOf θ * D.χ₀ ∨ D.betaOf (D.sbar θ) = (D.betaOf θ * D.χ₀)⁻¹ :=
  D.betaOf_XE (by rw [D.sq_mul_χ₀]; exact (D.betaOf_spec hθ).1)

theorem lam_sbar {θ : L → ℂ} (hθ : θ ∈ D.SFam) : D.lam (D.sbar θ) = D.lam θ := by
  unfold lam
  rcases D.betaOf_sbar hθ with h | h <;> rw [h]
  · rw [res_mul_χ₀]
  · rw [res_inv, res_mul_χ₀, nrm_inv]

theorem eps_sbar {θ : L → ℂ} (hθ : θ ∈ D.SFam) : D.eps (D.sbar θ) = -D.eps θ := by
  have hne : (-1 : ℂˣ) ≠ 1 := fun h => by
    have := congrArg Units.val h
    norm_num at this
  have hval : D.betaOf (D.sbar θ) D.J'E = -D.betaOf θ D.J'E := by
    rcases D.betaOf_sbar hθ with h | h <;> rw [h]
    · rw [MonoidHom.mul_apply, D.χ₀_J'E, mul_neg_one]
    · rw [MonoidHom.inv_apply, MonoidHom.mul_apply, D.χ₀_J'E, mul_neg_one, inv_neg,
        D.beta_J'_inv]
  unfold eps
  rw [hval]
  rcases D.beta_J'_cases (D.betaOf θ) with hb | hb
  · rw [hb, ite_eq_left rfl, ite_eq_right hne]
  · rw [hb, neg_neg, ite_eq_left rfl, ite_eq_right hne]
    norm_num

theorem sbar_ne {θ : L → ℂ} (hθ : θ ∈ D.SFam) : D.sbar θ ≠ θ := by
  obtain ⟨hβ, hθβ⟩ := D.betaOf_spec hθ
  intro h
  have h' : D.XE (D.betaOf θ * D.χ₀) = D.XE (D.betaOf θ) := h.trans hθβ.symm
  rcases (D.XE_eq_iff _ _ hβ).mp h' with h'' | h''
  · apply D.χ₀_ne
    refine MonoidHom.ext fun x => ?_
    have := congrArg (fun ψ : D.E →* ℂˣ => ψ x) h''
    simp only [MonoidHom.mul_apply] at this
    rw [MonoidHom.one_apply]
    exact mul_eq_left.mp this
  · have := congrArg (fun ψ : D.E →* ℂˣ => ψ D.J'E) h''
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, D.beta_J'_inv, D.χ₀_J'E,
      mul_neg_one] at this
    rcases D.beta_J'_cases (D.betaOf θ) with hb | hb <;> rw [hb] at this <;>
    · have := congrArg Units.val this
      norm_num at this

theorem sbar_sbar {θ : L → ℂ} (hθ : θ ∈ D.SFam) : D.sbar (D.sbar θ) = θ := by
  obtain ⟨hβ, hθβ⟩ := D.betaOf_spec hθ
  have e1 : D.sbar (D.sbar θ) = D.XE (D.betaOf (D.sbar θ) * D.χ₀) := rfl
  rw [e1]
  rcases D.betaOf_sbar hθ with h | h <;> rw [h]
  · rw [D.mul_χ₀_χ₀, hθβ]
  · rw [D.inv_mul_χ₀, D.XE_inv hβ, hθβ]

theorem valS_So {θ : L → ℂ} (hθ : θ ∈ D.SFam) (ρ : D.So) (hρ : ρ ≠ 1) :
    θ ρ = e * (((D.lam θ ρ : ℂˣ) : ℂ) + (((D.lam θ ρ)⁻¹ : ℂˣ) : ℂ)) := by
  obtain ⟨-, hθβ⟩ := D.betaOf_spec hθ
  have hρ1 : (ρ : L) ≠ 1 := fun h => hρ (Subtype.ext h)
  have h1 : θ ρ = D.XE (D.betaOf θ) ρ := by rw [hθβ]
  rw [h1, D.XE_E _ _ (D.So_le_E ρ.2) hρ1, D.sym_lam]

theorem valS_J'So {θ : L → ℂ} (hθ : θ ∈ D.SFam) (ρ : D.So) :
    θ (D.J' * ρ) = e * D.eps θ * (((D.lam θ ρ : ℂˣ) : ℂ) + (((D.lam θ ρ)⁻¹ : ℂˣ) : ℂ)) := by
  obtain ⟨-, hθβ⟩ := D.betaOf_spec hθ
  have hmem : D.J' * ρ ∈ D.E := D.E.mul_mem D.J'_mem (D.So_le_E ρ.2)
  have h1 : θ (D.J' * ρ) = D.XE (D.betaOf θ) (D.J' * ρ) := by rw [hθβ]
  rw [h1, D.XE_E _ _ hmem (D.J'_mul_ne_one ρ.2), D.sym_lam, D.eps_val]
  have hsplit : (⟨D.J' * ρ, hmem⟩ : D.E) = D.J'E * ⟨ρ, D.So_le_E ρ.2⟩ := rfl
  rw [hsplit, map_mul, mul_inv, D.beta_J'_inv, Units.val_mul, Units.val_mul]
  ring

@[expose] noncomputable def proj : D.E →* D.So where
  toFun x := ⟨(x : L) ^ (D.m + 1), by
    obtain ⟨k, hk⟩ := D.m_odd
    rw [show D.m + 1 = 2 * (k + 1) by omega, pow_mul]
    exact Subgroup.pow_mem _ (D.sq_mem_So x.2) _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by
    change ((x : L) * y) ^ (D.m + 1) = (x : L) ^ (D.m + 1) * (y : L) ^ (D.m + 1)
    exact (Commute.mul_pow (D.E_comm x.2 y.2) _))

theorem proj_So (ρ : D.So) : D.proj ⟨ρ, D.So_le_E ρ.2⟩ = ρ := Subtype.ext (by
  change (ρ : L) ^ (D.m + 1) = ρ
  rw [pow_succ, D.pow_m_of_mem_So ρ.2, one_mul])

theorem pow_m_hom (μ : D.So →* ℂˣ) : μ ^ D.m = 1 := by
  ext ρ
  rw [MonoidHom.pow_apply, ← map_pow]
  have : ρ ^ D.m = 1 := Subtype.ext (by
    change (ρ : L) ^ D.m = 1
    exact D.pow_m_of_mem_So ρ.2)
  rw [this, map_one]
  rfl

theorem lam_surj (μ : D.So →* ℂˣ) (hμ : μ ≠ 1) :
    ∃ θ ∈ D.SFam, D.lam θ = μ ∨ D.lam θ = μ⁻¹ := by
  set β := μ.comp D.proj with hβdef
  have hres : D.res β = μ := by
    ext ρ
    rw [res_apply, hβdef, MonoidHom.comp_apply, D.proj_So]
  have hβ : β ^ 2 ≠ 1 := by
    intro h
    apply hμ
    refine MonoidHom.ext fun ρ => ?_
    have h2 : μ ρ ^ 2 = 1 := by
      have := congrArg (fun ψ : D.E →* ℂˣ => ψ ⟨ρ, D.So_le_E ρ.2⟩) h
      simp only [MonoidHom.pow_apply, MonoidHom.one_apply] at this
      rw [← hres]
      exact this
    have hm : μ ρ ^ D.m = 1 := by
      have := congrArg (fun ψ : D.So →* ℂˣ => ψ ρ) (D.pow_m_hom μ)
      simpa only [MonoidHom.pow_apply, MonoidHom.one_apply] using this
    obtain ⟨k, hk⟩ := D.m_odd
    rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at hm
    rw [MonoidHom.one_apply]
    exact hm
  refine ⟨D.XE β, D.XE_mem hβ, ?_⟩
  unfold lam
  rcases D.betaOf_XE hβ with h | h <;> rw [h]
  · rw [hres]
    exact nrm_cases μ
  · rw [res_inv, nrm_inv, hres]
    exact nrm_cases μ

theorem lam_inj {θ : L → ℂ} (hθ : θ ∈ D.SFam) {θ' : L → ℂ} (hθ' : θ' ∈ D.SFam)
    (h : D.lam θ' = D.lam θ ∨ D.lam θ' = (D.lam θ)⁻¹) : θ' = θ ∨ θ' = D.sbar θ := by
  obtain ⟨hβ, hθβ⟩ := D.betaOf_spec hθ
  obtain ⟨hβ', hθβ'⟩ := D.betaOf_spec hθ'
  set β := D.betaOf θ
  set β' := D.betaOf θ'
  have hr : D.res β' = D.res β ∨ D.res β' = (D.res β)⁻¹ := eq_or_eq_inv_of_nrm h
  rcases hr with hr | hr
  · rcases D.eq_one_or_χ₀ (ψ := β' * β⁻¹)
      (by rw [res_mul, res_inv, hr]; exact mul_inv_cancel (D.res β)) with h1 | h1
    · left
      have hb : β' = β := mul_inv_eq_one.mp h1
      rw [← hθβ', ← hθβ, hb]
    · right
      have hb : β' = D.χ₀ * β := by
        refine MonoidHom.ext fun x => ?_
        have := congrArg (fun ψ : D.E →* ℂˣ => ψ x) h1
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
        exact mul_inv_eq_iff_eq_mul.mp this
      have hc : D.χ₀ * β = β * D.χ₀ := MonoidHom.ext fun x => by
        simp only [MonoidHom.mul_apply]
        exact mul_comm _ _
      rw [← hθβ', sbar, hb, hc]
  · rcases D.eq_one_or_χ₀ (ψ := β' * β)
      (by rw [res_mul, hr]; exact inv_mul_cancel (D.res β)) with h1 | h1
    · left
      have hb : β' = β⁻¹ := by
        refine MonoidHom.ext fun x => ?_
        have := congrArg (fun ψ : D.E →* ℂˣ => ψ x) h1
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.one_apply] at this ⊢
        exact eq_inv_of_mul_eq_one_left this
      rw [← hθβ', ← hθβ, hb, D.XE_inv hβ]
    · right
      have hb : β' = D.χ₀ * β⁻¹ := by
        refine MonoidHom.ext fun x => ?_
        have := congrArg (fun ψ : D.E →* ℂˣ => ψ x) h1
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply] at this ⊢
        exact eq_mul_inv_of_mul_eq this
      have hβ'eq : β' = (β * D.χ₀)⁻¹ := by
        rw [hb]
        refine MonoidHom.ext fun x => ?_
        have hx : (D.χ₀ x)⁻¹ = D.χ₀ x := by
          have := congrArg (fun ψ : D.E →* ℂˣ => ψ x) D.χ₀_inv
          simpa only [MonoidHom.inv_apply] using this
        simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
        rw [mul_inv, hx, mul_comm]
      rw [← hθβ', sbar, hβ'eq, D.XE_inv (by rw [D.sq_mul_χ₀]; exact hβ)]

end PSLData

end CFSG.Walter.Ward
