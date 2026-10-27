module

public import CFSG.Quasithin.Vol2.Ch3zShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique G6 RegularWreathProduct

namespace Ch3z

section WreathGroup

abbrev Q2 : Type := Multiplicative (ZMod 2)

@[expose] def gQ : Q2 := Multiplicative.ofAdd 1

theorem Q2_cases (q : Q2) : q = 1 ∨ q = gQ := by
  revert q
  decide

theorem gQ_mul_gQ : gQ * gQ = 1 := by decide

theorem gQ_ne_one : gQ ≠ 1 := by decide

theorem mem_sup_of_commute {M' : Type*} [Group M'] {A B : Subgroup M'}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {y : M'} (hy : y ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, y = a * b := by
  let S : Subgroup M' :=
    { carrier := {y | ∃ a ∈ A, ∃ b ∈ B, y = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have e : b * a' = a' * b := (h a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [e]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        rw [← mul_inv_rev, h a ha b hb] }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact this hy

variable {Γ D : Type*} [Group Γ] [Group D]

structure WreathSetup (X H₁ H₂ : Subgroup Γ) (t : Γ) : Prop where
  h1X : H₁ ≤ X
  h2X : H₂ ≤ X
  htX : t ∈ X
  comm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a
  inf : H₁ ⊓ H₂ = ⊥
  tt : t * t = 1
  c₁ : ∀ a ∈ H₁, t * a * t⁻¹ ∈ H₂
  c₂ : ∀ b ∈ H₂, t * b * t⁻¹ ∈ H₁
  ne : H₁ ≠ ⊥
  cover : ∀ x ∈ X, x ∈ H₁ ⊔ H₂ ∨ t * x ∈ H₁ ⊔ H₂

variable {X H₁ H₂ : Subgroup Γ} {t : Γ}

@[expose] def wrE₁ (θ : ↥H₁ ≃* D) : D →* Γ := H₁.subtype.comp θ.symm.toMonoidHom

@[expose] def wrE₂ (θ : ↥H₁ ≃* D) (t : Γ) : D →* Γ := (MulAut.conj t).toMonoidHom.comp (wrE₁ θ)

theorem wrE₁_mem (θ : ↥H₁ ≃* D) (σ : D) : wrE₁ θ σ ∈ H₁ := (θ.symm σ).2

theorem wrE₂_apply (θ : ↥H₁ ≃* D) (t : Γ) (σ : D) : wrE₂ θ t σ = t * wrE₁ θ σ * t⁻¹ := rfl

@[expose] def Tq (t : Γ) (q : Q2) : Γ := if q = 1 then 1 else t

theorem Tq_one (t : Γ) : Tq t 1 = 1 := by simp [Tq]

theorem Tq_gQ (t : Γ) : Tq t gQ = t := by simp [Tq, gQ_ne_one]

theorem WreathSetup.t_inv (h : WreathSetup X H₁ H₂ t) : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.tt

theorem WreathSetup.wrE₂_mem (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (σ : D) : wrE₂ θ t σ ∈ H₂ :=
  h.c₁ _ (wrE₁_mem θ σ)

theorem WreathSetup.comm₁₂ (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (σ τ : D) :
    wrE₁ θ σ * wrE₂ θ t τ = wrE₂ θ t τ * wrE₁ θ σ := h.comm _ (wrE₁_mem θ σ) _ (h.wrE₂_mem θ τ)

theorem wr_t₁ (θ : ↥H₁ ≃* D) (σ : D) : t * wrE₁ θ σ = wrE₂ θ t σ * t := by
  rw [wrE₂_apply]; group

theorem WreathSetup.t₂ (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (σ : D) :
    t * wrE₂ θ t σ = wrE₁ θ σ * t := by
  rw [wrE₂_apply]
  calc t * (t * wrE₁ θ σ * t⁻¹) = (t * t) * wrE₁ θ σ * t⁻¹ := by group
    _ = wrE₁ θ σ * t := by rw [h.tt, one_mul, h.t_inv]

theorem wrapPsi_mul (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (a b : D ≀ᵣ Q2) :
    wrE₁ θ ((a * b).left 1) * wrE₂ θ t ((a * b).left gQ) * Tq t (a * b).right =
      (wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * Tq t a.right) *
        (wrE₁ θ (b.left 1) * wrE₂ θ t (b.left gQ) * Tq t b.right) := by
  have hmul₁ : (a * b).left 1 = a.left 1 * b.left (a.right⁻¹ * 1) := rfl
  have hmul₂ : (a * b).left gQ = a.left gQ * b.left (a.right⁻¹ * gQ) := rfl
  have hr : (a * b).right = a.right * b.right := rfl
  have hc := h.comm₁₂ θ
  have hc' : ∀ σ τ, wrE₂ θ t τ * wrE₁ θ σ = wrE₁ θ σ * wrE₂ θ t τ := fun σ τ => (hc σ τ).symm
  have e0 : ∀ x : Q2, (1 : Q2)⁻¹ * x = x := by decide
  have e0' : ∀ x : Q2, (1 : Q2)⁻¹ * x = x := e0
  have g1 : gQ⁻¹ * 1 = gQ := by decide
  have g2 : gQ⁻¹ * gQ = 1 := by decide
  have gg : gQ * gQ = 1 := gQ_mul_gQ
  have t1 := wr_t₁ (t := t) θ
  have t2 := h.t₂ θ
  rcases Q2_cases a.right with ha | ha <;> rcases Q2_cases b.right with hb | hb
  ·
    have l1 : (a * b).left 1 = a.left 1 * b.left 1 := by rw [hmul₁, ha, e0 1]
    have l2 : (a * b).left gQ = a.left gQ * b.left gQ := by rw [hmul₂, ha, e0 gQ]
    have hr' : (a * b).right = 1 := by rw [hr, ha, hb, mul_one]
    rw [l1, l2, hr', ha, hb, Tq_one]
    simp only [map_mul, mul_one]
    calc wrE₁ θ (a.left 1) * wrE₁ θ (b.left 1) * (wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left gQ))
        = wrE₁ θ (a.left 1) * (wrE₁ θ (b.left 1) * wrE₂ θ t (a.left gQ)) * wrE₂ θ t (b.left gQ) := by
          group
      _ = wrE₁ θ (a.left 1) * (wrE₂ θ t (a.left gQ) * wrE₁ θ (b.left 1)) * wrE₂ θ t (b.left gQ) := by
          rw [hc (b.left 1) (a.left gQ)]
      _ = _ := by group
  ·
    have l1 : (a * b).left 1 = a.left 1 * b.left 1 := by rw [hmul₁, ha, e0 1]
    have l2 : (a * b).left gQ = a.left gQ * b.left gQ := by rw [hmul₂, ha, e0 gQ]
    have hr' : (a * b).right = gQ := by rw [hr, ha, hb, one_mul]
    rw [l1, l2, hr', ha, hb, Tq_one, Tq_gQ]
    simp only [map_mul, mul_one]
    calc wrE₁ θ (a.left 1) * wrE₁ θ (b.left 1) * (wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left gQ)) * t
        = wrE₁ θ (a.left 1) * (wrE₁ θ (b.left 1) * wrE₂ θ t (a.left gQ)) * wrE₂ θ t (b.left gQ) * t := by
          group
      _ = wrE₁ θ (a.left 1) * (wrE₂ θ t (a.left gQ) * wrE₁ θ (b.left 1)) * wrE₂ θ t (b.left gQ) * t := by
          rw [hc (b.left 1) (a.left gQ)]
      _ = _ := by group
  ·
    have l1 : (a * b).left 1 = a.left 1 * b.left gQ := by rw [hmul₁, ha, g1]
    have l2 : (a * b).left gQ = a.left gQ * b.left 1 := by rw [hmul₂, ha, g2]
    have hr' : (a * b).right = gQ := by rw [hr, ha, hb, mul_one]
    rw [l1, l2, hr', ha, hb, Tq_one, Tq_gQ]
    simp only [map_mul, mul_one]
    have hcc : wrE₁ θ (b.left gQ) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) =
        wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * wrE₁ θ (b.left gQ) := by
      rw [hc (b.left gQ) (a.left gQ), mul_assoc, hc (b.left gQ) (b.left 1), ← mul_assoc]
    calc wrE₁ θ (a.left 1) * wrE₁ θ (b.left gQ) * (wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1)) * t
        = wrE₁ θ (a.left 1) * (wrE₁ θ (b.left gQ) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1)) * t := by
          group
      _ = wrE₁ θ (a.left 1) * (wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * wrE₁ θ (b.left gQ)) * t := by
          rw [hcc]
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * (wrE₁ θ (b.left gQ) * t) := by
          group
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * (t * wrE₂ θ t (b.left gQ)) := by
          rw [t2]
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * (wrE₂ θ t (b.left 1) * t) * wrE₂ θ t (b.left gQ) := by
          group
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * (t * wrE₁ θ (b.left 1)) * wrE₂ θ t (b.left gQ) := by
          rw [t1]
      _ = _ := by group
  ·
    have l1 : (a * b).left 1 = a.left 1 * b.left gQ := by rw [hmul₁, ha, g1]
    have l2 : (a * b).left gQ = a.left gQ * b.left 1 := by rw [hmul₂, ha, g2]
    have hr' : (a * b).right = 1 := by rw [hr, ha, hb, gg]
    rw [l1, l2, hr', ha, hb, Tq_one, Tq_gQ]
    simp only [map_mul, mul_one]
    have hcc : wrE₁ θ (b.left gQ) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) =
        wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * wrE₁ θ (b.left gQ) := by
      rw [hc (b.left gQ) (a.left gQ), mul_assoc, hc (b.left gQ) (b.left 1), ← mul_assoc]
    calc wrE₁ θ (a.left 1) * wrE₁ θ (b.left gQ) * (wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1))
        = wrE₁ θ (a.left 1) * (wrE₁ θ (b.left gQ) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1)) := by
          group
      _ = wrE₁ θ (a.left 1) * (wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * wrE₁ θ (b.left gQ)) := by
          rw [hcc]
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * (wrE₁ θ (b.left gQ) * t * t) := by
          have : wrE₁ θ (b.left gQ) * t * t = wrE₁ θ (b.left gQ) := by rw [mul_assoc, h.tt, mul_one]
          rw [this]
          group
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * wrE₂ θ t (b.left 1) * (t * wrE₂ θ t (b.left gQ) * t) := by
          rw [t2]
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * (wrE₂ θ t (b.left 1) * t) * wrE₂ θ t (b.left gQ) * t := by
          group
      _ = wrE₁ θ (a.left 1) * wrE₂ θ t (a.left gQ) * (t * wrE₁ θ (b.left 1)) * wrE₂ θ t (b.left gQ) * t := by
          rw [t1]
      _ = _ := by group

@[expose] noncomputable def wrapPsi (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) : (D ≀ᵣ Q2) →* Γ where
  toFun w := wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ) * Tq t w.right
  map_one' := by
    have h1 : (1 : D ≀ᵣ Q2).left 1 = 1 := rfl
    have h2 : (1 : D ≀ᵣ Q2).left gQ = 1 := rfl
    have h3 : (1 : D ≀ᵣ Q2).right = 1 := rfl
    rw [h1, h2, h3, Tq_one]
    simp
  map_mul' := wrapPsi_mul h θ

theorem wrapPsi_apply (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (w : D ≀ᵣ Q2) :
    wrapPsi h θ w = wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ) * Tq t w.right := rfl

theorem wrE₁_injective (θ : ↥H₁ ≃* D) : Function.Injective (wrE₁ θ) := fun _ _ hab =>
  θ.symm.injective (Subtype.ext hab)

theorem wrE₂_injective (θ : ↥H₁ ≃* D) (t : Γ) : Function.Injective (wrE₂ θ t) := fun a b hab =>
  wrE₁_injective θ (by simpa [wrE₂_apply] using hab)

theorem WreathSetup.t_not_mem (h : WreathSetup X H₁ H₂ t) : t ∉ H₁ ⊔ H₂ := by
  intro ht
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute h.comm ht
  apply h.ne
  rw [eq_bot_iff]
  intro a' ha'
  have h1 : t * a' * t⁻¹ ∈ H₂ := h.c₁ a' ha'
  have h2 : t * a' * t⁻¹ = a * a' * a⁻¹ := by
    rw [hab]
    have e : b * a' = a' * b := (h.comm a' ha' b hb).symm
    calc a * b * a' * (a * b)⁻¹ = a * (b * a') * b⁻¹ * a⁻¹ := by group
      _ = a * (a' * b) * b⁻¹ * a⁻¹ := by rw [e]
      _ = a * a' * a⁻¹ := by group
  have h3 : a * a' * a⁻¹ ∈ H₁ ⊓ H₂ :=
    ⟨H₁.mul_mem (H₁.mul_mem ha ha') (H₁.inv_mem ha), h2 ▸ h1⟩
  rw [h.inf, Subgroup.mem_bot] at h3
  have : a' = 1 := by
    calc a' = a⁻¹ * (a * a' * a⁻¹) * a := by group
      _ = 1 := by rw [h3]; group
  simpa using this

theorem wrapPsi_injective (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) :
    Function.Injective (wrapPsi h θ) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have hw' : wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ) * Tq t w.right = 1 := hw
  rcases Q2_cases w.right with hr | hr
  · rw [hr, Tq_one, mul_one] at hw'
    have h1 : wrE₁ θ (w.left 1) = (wrE₂ θ t (w.left gQ))⁻¹ := eq_inv_of_mul_eq_one_left hw'
    have h2 : wrE₁ θ (w.left 1) ∈ H₁ ⊓ H₂ :=
      ⟨wrE₁_mem θ _, h1 ▸ H₂.inv_mem (h.wrE₂_mem θ _)⟩
    rw [h.inf, Subgroup.mem_bot] at h2
    have h3 : w.left 1 = 1 := wrE₁_injective θ (h2.trans (map_one _).symm)
    have h4 : wrE₂ θ t (w.left gQ) = 1 := by
      rw [h2, one_mul] at hw'
      exact hw'
    have h5 : w.left gQ = 1 := wrE₂_injective θ t (h4.trans (map_one _).symm)
    refine RegularWreathProduct.ext ?_ hr
    funext q
    rcases Q2_cases q with rfl | rfl
    · exact h3
    · exact h5
  · exfalso
    rw [hr, Tq_gQ] at hw'
    apply h.t_not_mem
    have : t = (wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ))⁻¹ := eq_inv_of_mul_eq_one_right hw'
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem_sup (wrE₁_mem θ _) (h.wrE₂_mem θ _))

theorem wrapPsi_mem (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (w : D ≀ᵣ Q2) :
    wrapPsi h θ w ∈ X := by
  rw [wrapPsi_apply]
  refine X.mul_mem (X.mul_mem (h.h1X (wrE₁_mem θ _)) (h.h2X (h.wrE₂_mem θ _))) ?_
  unfold Tq
  split_ifs
  · exact X.one_mem
  · exact h.htX

theorem wrapPsi_surjective (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) :
    ∀ x ∈ X, ∃ w, wrapPsi h θ w = x := by
  intro x hxX
  rcases h.cover x hxX with hx | hx
  · obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.comm hx
    have hb' : t * b * t⁻¹ ∈ H₁ := h.c₂ b hb
    let σ : D := θ ⟨a, ha⟩
    let τ : D := θ ⟨t * b * t⁻¹, hb'⟩
    refine ⟨⟨fun q => if q = 1 then σ else τ, 1⟩, ?_⟩
    rw [wrapPsi_apply]
    show wrE₁ θ (if (1 : Q2) = 1 then σ else τ) * wrE₂ θ t (if gQ = 1 then σ else τ) * Tq t 1 = a * b
    have hite1 : (if (1 : Q2) = 1 then σ else τ) = σ := by simp
    have hite2 : (if gQ = 1 then σ else τ) = τ := by simp [gQ_ne_one]
    rw [hite1, hite2, Tq_one, mul_one, wrE₂_apply]
    have e1 : wrE₁ θ σ = a := by simp [σ, wrE₁]
    have e2 : wrE₁ θ τ = t * b * t⁻¹ := by simp [τ, wrE₁]
    rw [e1, e2]
    congr 1
    calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t⁻¹ * t⁻¹) := by group
      _ = b := by rw [h.tt, h.t_inv, h.tt]; group
  · obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute h.comm hx
    have ha' : t * a * t⁻¹ ∈ H₂ := h.c₁ a ha
    have hb' : t * b * t⁻¹ ∈ H₁ := h.c₂ b hb
    let σ : D := θ ⟨a, ha⟩
    let τ : D := θ ⟨t * b * t⁻¹, hb'⟩
    refine ⟨⟨fun q => if q = 1 then τ else σ, gQ⟩, ?_⟩
    rw [wrapPsi_apply]
    show wrE₁ θ (if (1 : Q2) = 1 then τ else σ) * wrE₂ θ t (if gQ = 1 then τ else σ) * Tq t gQ = x
    have hite1 : (if (1 : Q2) = 1 then τ else σ) = τ := by simp
    have hite2 : (if gQ = 1 then τ else σ) = σ := by simp [gQ_ne_one]
    rw [hite1, hite2, Tq_gQ, wrE₂_apply]
    have e1 : wrE₁ θ σ = a := by simp [σ, wrE₁]
    have e2 : wrE₁ θ τ = t * b * t⁻¹ := by simp [τ, wrE₁]
    rw [e1, e2]
    have hx' : x = t * (a * b) := by
      have : t * x = a * b := hab
      calc x = (t * t) * x := by rw [h.tt, one_mul]
        _ = t * (t * x) := by group
        _ = t * (a * b) := by rw [this]
    rw [hx']
    have hcomm : (t * b * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * b * t⁻¹) :=
      (h.comm _ hb' _ ha')
    calc t * b * t⁻¹ * (t * a * t⁻¹) * t = (t * a * t⁻¹) * (t * b * t⁻¹) * t := by rw [hcomm]
      _ = t * (a * b) := by
        rw [h.t_inv]
        calc t * a * t * (t * b * t) * t = t * a * (t * t) * b * (t * t) := by group
          _ = t * (a * b) := by rw [h.tt]; group

@[expose] noncomputable def wrapEquiv (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) : (D ≀ᵣ Q2) ≃* ↥X :=
  MulEquiv.ofBijective ((wrapPsi h θ).codRestrict X (wrapPsi_mem h θ))
    ⟨fun a b hab => wrapPsi_injective h θ (congrArg Subtype.val hab), fun ⟨x, hx⟩ => by
      obtain ⟨w, hw⟩ := wrapPsi_surjective h θ x hx
      exact ⟨w, Subtype.ext hw⟩⟩

theorem wrapEquiv_coe (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (w : D ≀ᵣ Q2) :
    ((wrapEquiv h θ w : ↥X) : Γ) = wrapPsi h θ w := rfl

@[expose] def wrI₁ (σ : D) : D ≀ᵣ Q2 := ⟨fun q => if q = 1 then σ else 1, 1⟩

@[expose] def wrI₂ (σ : D) : D ≀ᵣ Q2 := ⟨fun q => if q = 1 then 1 else σ, 1⟩

theorem wrapEquiv_wrI₁ (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (σ : D) :
    ((wrapEquiv h θ (wrI₁ σ) : ↥X) : Γ) = wrE₁ θ σ := by
  rw [wrapEquiv_coe]
  rw [wrapPsi_apply]
  have h1 : (wrI₁ σ).left 1 = σ := by simp [wrI₁]
  have h2 : (wrI₁ σ).left gQ = 1 := by simp [wrI₁, gQ_ne_one]
  have h3 : (wrI₁ σ).right = 1 := rfl
  rw [h1, h2, h3, Tq_one, map_one]
  simp

theorem wrapEquiv_wrI₂ (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (σ : D) :
    ((wrapEquiv h θ (wrI₂ σ) : ↥X) : Γ) = wrE₂ θ t σ := by
  rw [wrapEquiv_coe]
  rw [wrapPsi_apply]
  have h1 : (wrI₂ σ).left 1 = 1 := by simp [wrI₂]
  have h2 : (wrI₂ σ).left gQ = σ := by simp [wrI₂, gQ_ne_one]
  have h3 : (wrI₂ σ).right = 1 := rfl
  rw [h1, h2, h3, Tq_one, map_one]
  simp

theorem wrapEquiv_mem_iff (h : WreathSetup X H₁ H₂ t) (θ : ↥H₁ ≃* D) (w : D ≀ᵣ Q2) :
    ((wrapEquiv h θ w : ↥X) : Γ) ∈ H₁ ⊔ H₂ ↔ w.right = 1 := by
  rw [wrapEquiv_coe, wrapPsi_apply]
  have hY : wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ) ∈ H₁ ⊔ H₂ :=
    Subgroup.mul_mem_sup (wrE₁_mem θ _) (h.wrE₂_mem θ _)
  rcases Q2_cases w.right with hr | hr
  · rw [hr, Tq_one, mul_one]
    exact ⟨fun _ => rfl, fun _ => hY⟩
  · rw [hr, Tq_gQ]
    constructor
    · intro hmem
      exfalso
      apply h.t_not_mem
      have : t = (wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ))⁻¹ *
          (wrE₁ θ (w.left 1) * wrE₂ θ t (w.left gQ) * t) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hY) hmem
    · intro hg
      exact absurd hg gQ_ne_one

end WreathGroup

section TwoBlocks

variable {V : Type} [CommGroup V]

structure TwoBlk (X H₁ H₂ : Subgroup (MulAut V)) (m : ℕ) : Prop where
  m35 : m = 3 ∨ m = 5
  h1X : H₁ ≤ X
  h2X : H₂ ≤ X
  Ynorm : ∀ x ∈ X, ∀ y ∈ H₁ ⊔ H₂, x * y * x⁻¹ ∈ H₁ ⊔ H₂
  comm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a
  inf : H₁ ⊓ H₂ = ⊥
  supV : commV H₁ ⊔ commV H₂ = ⊤
  infV : commV H₁ ⊓ commV H₂ = ⊥
  act₁ : ∀ a ∈ H₁, ∀ v ∈ commV H₂, a v = v
  act₂ : ∀ a ∈ H₂, ∀ v ∈ commV H₁, a v = v
  sym₁ : IsSymCore H₁ (commV H₁) m
  sym₂ : IsSymCore H₂ (commV H₂) m

variable {X H₁ H₂ : Subgroup (MulAut V)} {m : ℕ}

theorem TwoBlk.symm (h : TwoBlk X H₁ H₂ m) : TwoBlk X H₂ H₁ m where
  m35 := h.m35
  h1X := h.h2X
  h2X := h.h1X
  Ynorm := fun x hx y hy => by rw [sup_comm] at hy ⊢; exact h.Ynorm x hx y hy
  comm := fun a ha b hb => (h.comm b hb a ha).symm
  inf := by rw [inf_comm]; exact h.inf
  supV := by rw [sup_comm]; exact h.supV
  infV := by rw [inf_comm]; exact h.infV
  act₁ := h.act₂
  act₂ := h.act₁
  sym₁ := h.sym₂
  sym₂ := h.sym₁

theorem TwoBlk.sym_faithful (h : TwoBlk X H₁ H₂ m) {a : MulAut V} (ha : a ∈ H₁)
    (hfix : ∀ u ∈ commV H₁, a u = u) : a = 1 := by
  obtain ⟨θ, β, hβeq, hβr, hβk⟩ := h.sym₁
  have hodd : Odd m := by rcases h.m35 with rfl | rfl <;> decide
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have : u ∈ β.ker := hu
    rw [hβk] at this
    simpa using this
  have h1 : coreAct m (θ ⟨a, ha⟩) = 1 := by
    refine MulEquiv.ext fun w => hβinj ?_
    rw [hβeq]
    show a (β w) = β w
    exact hfix _ (hβr ▸ ⟨w, rfl⟩)
  have h2 : θ ⟨a, ha⟩ = 1 := (coreAct_eq_one_iff m hodd _).mp h1
  have h3 : (⟨a, ha⟩ : ↥H₁) = 1 := θ.injective (h2.trans (map_one θ).symm)
  exact congrArg Subtype.val h3

theorem TwoBlk.preserve₁ (h : TwoBlk X H₁ H₂ m) {y : MulAut V} (hy : y ∈ H₁ ⊔ H₂) {w : V}
    (hw : w ∈ commV H₁) : y w ∈ commV H₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.comm hy
  rw [MulAut.mul_apply, h.act₂ b hb w hw]
  exact G6.apply_mem_commV (fun x hx => H₁.mul_mem (H₁.mul_mem ha hx) (H₁.inv_mem ha)) hw

theorem TwoBlk.centralizer₂ (h : TwoBlk X H₁ H₂ m) {y : MulAut V} (hy : y ∈ H₁ ⊔ H₂)
    (hfix : ∀ w ∈ commV H₂, y w = w) : y ∈ H₁ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.comm hy
  have hb1 : b = 1 := by
    refine h.symm.sym_faithful hb fun w hw => ?_
    have h1 := hfix w hw
    rw [MulAut.mul_apply] at h1
    have h2 : b w ∈ commV H₂ := G6.apply_mem_commV
      (fun x hx => H₂.mul_mem (H₂.mul_mem hb hx) (H₂.inv_mem hb)) hw
    rwa [h.act₁ a ha _ h2] at h1
  rw [hb1, mul_one]
  exact ha

theorem TwoBlk.centralizer₁ (h : TwoBlk X H₁ H₂ m) {y : MulAut V} (hy : y ∈ H₁ ⊔ H₂)
    (hfix : ∀ w ∈ commV H₁, y w = w) : y ∈ H₂ := by
  have h' := h.symm
  rw [sup_comm] at hy
  exact h'.centralizer₂ hy hfix

theorem core_inv_eq {H : Subgroup (MulAut V)} {U : Subgroup V} (hm : m = 3 ∨ m = 5)
    (hH : IsSymCore H U m) (W : Subgroup V) (hW : ∀ a ∈ H, ∀ w ∈ W, a w ∈ W) :
    W ⊓ U = ⊥ ∨ U ≤ W := by
  obtain ⟨θ, β, hβeq, hβr, hβk⟩ := hH
  let W' : Subgroup (coreMod m) := (W ⊓ U).comap β
  have hinv : ∀ σ : Equiv.Perm (Fin m), ∀ w ∈ W', coreAct m σ w ∈ W' := by
    intro σ w hw
    have h1 := hβeq (θ.symm σ) w
    rw [MulEquiv.apply_symm_apply] at h1
    refine ⟨?_, ?_⟩
    · show β (coreAct m σ w) ∈ W
      rw [h1]
      exact hW _ (θ.symm σ).2 _ hw.1
    · show β (coreAct m σ w) ∈ U
      rw [← hβr]
      exact ⟨_, rfl⟩
  rcases core_irred m hm W' hinv with h0 | h1
  · left
    rw [eq_bot_iff]
    rintro x ⟨hxW, hxU⟩
    have hxU' := hxU
    rw [← hβr] at hxU'
    obtain ⟨w, hw⟩ := hxU'
    have hw' : w ∈ W' := by
      show β w ∈ W ⊓ U
      rw [hw]
      exact ⟨hxW, hxU⟩
    rw [h0, Subgroup.mem_bot] at hw'
    rw [Subgroup.mem_bot, ← hw, hw', map_one]
  · right
    intro x hxU
    have hxU' := hxU
    rw [← hβr] at hxU'
    obtain ⟨w, hw⟩ := hxU'
    have hw' : w ∈ W' := by rw [h1]; trivial
    have : β w ∈ W ⊓ U := hw'
    rw [hw] at this
    exact this.1

theorem TwoBlk.sym_inj (h : TwoBlk X H₁ H₂ m) : ∃ (θ : ↥H₁ ≃* Equiv.Perm (Fin m))
    (β : ↥(coreMod m) →* V), (∀ (x : ↥H₁) (u : ↥(coreMod m)),
      β (coreAct m (θ x) u) = (x : MulAut V) (β u)) ∧ β.range = commV H₁ ∧ Function.Injective β := by
  obtain ⟨θ, β, hβeq, hβr, hβk⟩ := h.sym₁
  refine ⟨θ, β, hβeq, hβr, ?_⟩
  rw [injective_iff_map_eq_one]
  intro u hu
  have : u ∈ β.ker := hu
  rw [hβk] at this
  simpa using this

theorem TwoBlk.no_fixed₁ (h : TwoBlk X H₁ H₂ m) {e : V} (he : e ∈ commV H₁)
    (hfix : ∀ a ∈ H₁, a e = e) : e = 1 := by
  obtain ⟨θ, β, hβeq, hβr, hβi⟩ := h.sym_inj
  have he' : e ∈ β.range := hβr ▸ he
  obtain ⟨w, rfl⟩ := he'
  have hw : ∀ σ : Equiv.Perm (Fin m), coreAct m σ w = w := by
    intro σ
    have h1 := hβeq (θ.symm σ) w
    rw [MulEquiv.apply_symm_apply] at h1
    exact hβi (h1.trans (hfix _ (θ.symm σ).2))
  rw [core_fixed_all m h.m35 w hw, map_one]

theorem TwoBlk.card_comm (h : TwoBlk X H₁ H₂ m) : Nat.card (commV H₁) = Nat.card (commV H₂) := by
  obtain ⟨θ, β, hβeq, hβr, hβi⟩ := h.sym_inj
  obtain ⟨θ', β', hβeq', hβr', hβi'⟩ := h.symm.sym_inj
  rw [← hβr, ← hβr']
  exact (Nat.card_congr (MonoidHom.ofInjective hβi).toEquiv.symm).trans
    (Nat.card_congr (MonoidHom.ofInjective hβi').toEquiv)

theorem TwoBlk.exists_ne_one (h : TwoBlk X H₁ H₂ m) : ∃ e ∈ commV H₁, e ≠ 1 := by
  obtain ⟨θ, β, hβeq, hβr, hβi⟩ := h.sym_inj
  have hodd : Odd m := by rcases h.m35 with rfl | rfl <;> decide
  have h3 : 3 ≤ m := by rcases h.m35 with rfl | rfl <;> decide
  refine ⟨β (uCore m hodd ⟨0, by omega⟩), by rw [← hβr]; exact ⟨_, rfl⟩, fun h1 => ?_⟩
  have := hβi (h1.trans (map_one β).symm)
  exact uCore_ne_one m hodd h3 _ this

variable [Finite V]

theorem TwoBlk.map_comm (h : TwoBlk X H₁ H₂ m) {u : MulAut V} (hu : u ∈ X) :
    (commV H₁).map u.toMonoidHom = commV H₁ ∨ (commV H₁).map u.toMonoidHom = commV H₂ := by
  set W := (commV H₁).map u.toMonoidHom with hW
  have hWinv : ∀ y ∈ H₁ ⊔ H₂, ∀ w ∈ W, y w ∈ W := by
    intro y hy w hw
    obtain ⟨e, he, rfl⟩ := hw
    have hy' : u⁻¹ * y * u ∈ H₁ ⊔ H₂ := by
      have := h.Ynorm u⁻¹ (X.inv_mem hu) y hy
      simpa using this
    refine ⟨(u⁻¹ * y * u) e, h.preserve₁ hy' he, ?_⟩
    simp [MulAut.mul_apply]
  have hC₁ := core_inv_eq h.m35 h.sym₁ W (fun a ha w hw => hWinv a ((le_sup_left : H₁ ≤ H₁ ⊔ H₂) ha) w hw)
  have hC₂ := core_inv_eq h.m35 h.sym₂ W (fun a ha w hw => hWinv a ((le_sup_right : H₂ ≤ H₁ ⊔ H₂) ha) w hw)
  have hcard1 : Nat.card W = Nat.card (commV H₁) := Subgroup.card_map_of_injective u.injective
  have hcard12 := h.card_comm
  rcases hC₁ with h1 | h1
  · rcases hC₂ with h2 | h2
    · exfalso
      obtain ⟨e₀, he₀, he₀1⟩ := h.exists_ne_one
      have heW₀ : u e₀ ∈ W := ⟨e₀, he₀, rfl⟩
      have hu1 : u e₀ ≠ 1 := fun h1 => he₀1 (u.injective (h1.trans (map_one u).symm))
      obtain ⟨e₁, he₁, e₂, he₂, he⟩ := Subgroup.mem_sup.mp (h.supV ▸ (Subgroup.mem_top (u e₀)))
      have he₂1 : e₂ ≠ 1 := by
        intro h21
        rw [h21, mul_one] at he
        have : u e₀ ∈ W ⊓ commV H₁ := ⟨heW₀, he ▸ he₁⟩
        rw [h1, Subgroup.mem_bot] at this
        exact hu1 this
      have he₁1 : e₁ ≠ 1 := by
        intro h11
        rw [h11, one_mul] at he
        have : u e₀ ∈ W ⊓ commV H₂ := ⟨heW₀, he ▸ he₂⟩
        rw [h2, Subgroup.mem_bot] at this
        exact hu1 this
      have hmove : ∃ a ∈ H₁, a e₁ ≠ e₁ := by
        by_contra hcon
        push Not at hcon
        exact he₁1 (h.no_fixed₁ he₁ hcon)
      obtain ⟨a, ha, hae⟩ := hmove
      have haW : a (u e₀) ∈ W := hWinv a ((le_sup_left : H₁ ≤ H₁ ⊔ H₂) ha) _ heW₀
      have h3 : a (u e₀) * (u e₀)⁻¹ ∈ W := W.mul_mem haW (W.inv_mem heW₀)
      have h4 : a (u e₀) * (u e₀)⁻¹ = a e₁ * e₁⁻¹ := by
        rw [← he, map_mul, h.act₁ a ha e₂ he₂]
        simp
      have h5 : a e₁ * e₁⁻¹ ∈ commV H₁ := G6.mem_commV_of_mem ha e₁
      rw [h4] at h3
      have h6 : a e₁ * e₁⁻¹ ∈ W ⊓ commV H₁ := ⟨h3, h5⟩
      rw [h1, Subgroup.mem_bot, mul_inv_eq_one] at h6
      exact hae h6
    · right
      exact (Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard1, hcard12])).symm
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard1])).symm

omit [Finite V] in
theorem TwoBlk.mem_sup_of_normalizes (h : TwoBlk X H₁ H₂ m) {x : MulAut V} (hxX : x ∈ X)
    (hx : x ∈ Subgroup.normalizer (H₁ : Set (MulAut V))) : x ∈ H₁ ⊔ H₂ := by
  have hm : m = 3 ∨ m = 5 ∨ m = 7 := by
    rcases h.m35 with h3 | h5
    · exact Or.inl h3
    · exact Or.inr (Or.inl h5)
  have hnorm' : ∀ y ∈ H₁, x * y * x⁻¹ ∈ H₁ := fun y hy => (Subgroup.mem_normalizer_iff.mp hx y).mp hy
  have hnorm'' : ∀ y ∈ H₁, x⁻¹ * y * x⁻¹⁻¹ ∈ H₁ := fun y hy => by
    simpa using (Subgroup.mem_normalizer_iff''.mp hx y).mp hy
  have hxE : ∀ w ∈ commV H₁, x w ∈ commV H₁ := fun w hw => G6.apply_mem_commV hnorm' hw
  have hxE' : ∀ w ∈ commV H₁, x⁻¹ w ∈ commV H₁ := fun w hw => G6.apply_mem_commV hnorm'' hw
  obtain ⟨a, haH, hxa⟩ := exists_mem_eq_on_of_normalizes hm h.sym₁ x hxE hxE' hx
  set x' := a⁻¹ * x with hx'
  have hx'X : x' ∈ X := X.mul_mem (X.inv_mem (h.h1X haH)) hxX
  have hx'E : ∀ w ∈ commV H₁, x' w = w := fun w hw => by
    rw [hx', MulAut.mul_apply, hxa w hw]
    simp
  have hx'E' : ∀ w ∈ commV H₁, x'⁻¹ w = w := fun w hw => by
    have := congrArg (fun z => x'⁻¹ z) (hx'E w hw)
    exact (by simpa using this : w = x'⁻¹ w).symm
  have key : ∀ z : MulAut V, z ∈ X → (∀ w ∈ commV H₁, z w = w) → (∀ w ∈ commV H₁, z⁻¹ w = w) →
      ∀ y ∈ H₂, z * y * z⁻¹ ∈ H₂ := by
    intro z hzX hz hz' y hy
    have hY : z * y * z⁻¹ ∈ H₁ ⊔ H₂ := h.Ynorm z hzX y ((le_sup_right : H₂ ≤ H₁ ⊔ H₂) hy)
    refine h.centralizer₁ hY fun w hw => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, hz' w hw, h.act₂ y hy w hw, hz w hw]
  have hx'N : x' ∈ Subgroup.normalizer (H₂ : Set (MulAut V)) := by
    apply B6.mem_normalizer_of_forall_mem (key x' hx'X hx'E hx'E')
    intro y hy
    have := key x'⁻¹ (X.inv_mem hx'X) hx'E' (fun w hw => by simpa using hx'E w hw) y hy
    simpa using this
  have hn₂' : ∀ y ∈ H₂, x' * y * x'⁻¹ ∈ H₂ := key x' hx'X hx'E hx'E'
  have hn₂'' : ∀ y ∈ H₂, x'⁻¹ * y * x'⁻¹⁻¹ ∈ H₂ := fun y hy => by
    simpa using (Subgroup.mem_normalizer_iff''.mp hx'N y).mp hy
  have hx'E₂ : ∀ w ∈ commV H₂, x' w ∈ commV H₂ := fun w hw => G6.apply_mem_commV hn₂' hw
  have hx'E₂' : ∀ w ∈ commV H₂, x'⁻¹ w ∈ commV H₂ := fun w hw => G6.apply_mem_commV hn₂'' hw
  obtain ⟨b, hbH, hx'b⟩ := exists_mem_eq_on_of_normalizes hm h.sym₂ x' hx'E₂ hx'E₂' hx'N
  have hx'' : b⁻¹ * x' = 1 := by
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ commV H₁ ⊔ commV H₂ := h.supV ▸ Subgroup.mem_top v
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [MulAut.mul_apply, map_mul, map_mul, hx'E e₁ he₁, hx'b e₂ he₂]
    have h1 : b⁻¹ e₁ = e₁ := h.act₂ _ (H₂.inv_mem hbH) e₁ he₁
    have h2 : b⁻¹ (b e₂) = e₂ := by simp
    rw [h1, h2]
    rfl
  have hx'eq : x' = b := by
    have := congrArg (fun z => b * z) hx''
    simpa using this
  have hxe : x = a * b := by
    rw [← hx'eq, hx']
    simp
  rw [hxe]
  exact Subgroup.mul_mem_sup haH hbH

omit [Finite V] in
theorem TwoBlk.card_blocks (h : TwoBlk X H₁ H₂ m) : Nat.card H₁ = Nat.card H₂ := by
  obtain ⟨θ₁, -⟩ := h.sym₁
  obtain ⟨θ₂, -⟩ := h.sym₂
  exact Nat.card_congr (θ₁.toEquiv.trans θ₂.toEquiv.symm)

omit [Finite V] in
theorem card_conjSub (u : MulAut V) (H : Subgroup (MulAut V)) :
    Nat.card (B6.conjSub u H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj u).injective

theorem TwoBlk.conj_block (h : TwoBlk X H₁ H₂ m) {u : MulAut V} (hu : u ∈ X) :
    B6.conjSub u H₁ = H₁ ∨ B6.conjSub u H₁ = H₂ := by
  have hU₁ := h.map_comm hu
  have hU₂ := h.symm.map_comm hu
  have hne : (commV H₁).map u.toMonoidHom ≠ (commV H₂).map u.toMonoidHom := by
    intro heq
    have h12 : commV H₁ = commV H₂ := Subgroup.map_injective u.injective heq
    obtain ⟨e, he, he1⟩ := h.exists_ne_one
    have : e ∈ commV H₁ ⊓ commV H₂ := ⟨he, h12 ▸ he⟩
    rw [h.infV, Subgroup.mem_bot] at this
    exact he1 this
  have hcc := card_conjSub u H₁
  have hcb := h.card_blocks
  have hY : ∀ y ∈ B6.conjSub u H₁, y ∈ H₁ ⊔ H₂ ∧ u⁻¹ * y * u ∈ H₁ := by
    intro y hy
    have ha : u⁻¹ * y * u ∈ H₁ := B6.mem_conjSub.mp hy
    refine ⟨?_, ha⟩
    have := h.Ynorm u hu _ ((le_sup_left : H₁ ≤ H₁ ⊔ H₂) ha)
    simpa [mul_assoc] using this
  have hact : ∀ y ∈ B6.conjSub u H₁, ∀ e ∈ commV H₂, y (u e) = u e := by
    intro y hy e he
    have ha := (hY y hy).2
    have : y (u e) = u ((u⁻¹ * y * u) e) := by simp [MulAut.mul_apply]
    rw [this, h.act₁ _ ha e he]
  have hact' : ∀ y ∈ B6.conjSub u H₁, ∀ w ∈ commV H₂ , ∀ e ∈ commV H₂, u e = w → y w = w := by
    intro y hy w hw e he hew
    rw [← hew]
    exact hact y hy e he
  rcases hU₁ with h1 | h1 <;> rcases hU₂ with h2 | h2
  · left
    have hle : B6.conjSub u H₁ ≤ H₁ := by
      intro y hy
      refine h.centralizer₂ (hY y hy).1 fun w hw => ?_
      have hw' : w ∈ (commV H₂).map u.toMonoidHom := by rw [h2]; exact hw
      obtain ⟨e, he, hew⟩ := hw'
      exact hact' y hy w hw e he hew
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcc])
  · exact absurd (h1.trans h2.symm) hne
  · exact absurd (h1.trans h2.symm) hne
  · right
    have hle : B6.conjSub u H₁ ≤ H₂ := by
      intro y hy
      refine h.centralizer₁ (hY y hy).1 fun w hw => ?_
      have hw' : w ∈ (commV H₂).map u.toMonoidHom := by rw [h2]; exact hw
      obtain ⟨e, he, hew⟩ := hw'
      have hew' : u e = w := hew
      have := hact y hy e he
      rw [hew'] at this
      exact this
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcc, hcb])

omit [Finite V] in
theorem TwoBlk.one_lt_card (h : TwoBlk X H₁ H₂ m) : 1 < Nat.card H₁ := by
  obtain ⟨θ, -⟩ := h.sym₁
  rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases h.m35 with rfl | rfl <;> decide

omit [Finite V] in
theorem TwoBlk.ne_bot₁ (h : TwoBlk X H₁ H₂ m) : H₁ ≠ ⊥ := by
  intro hb
  have := h.one_lt_card
  rw [hb] at this
  simp at this

omit [Finite V] in
theorem conj_mem_of_conjSub {H K : Subgroup (MulAut V)} {t : MulAut V} (h : B6.conjSub t H = K)
    {y : MulAut V} (hy : y ∈ H) : t * y * t⁻¹ ∈ K := by
  rw [← h, B6.mem_conjSub]
  have : t⁻¹ * (t * y * t⁻¹) * t = y := by group
  rw [this]
  exact hy

omit [Finite V] in
theorem conj_inv_mem_of_conjSub {H K : Subgroup (MulAut V)} {t : MulAut V}
    (h : B6.conjSub t H = K) {y : MulAut V} (hy : y ∈ K) : t⁻¹ * y * t ∈ H := by
  rw [← h, B6.mem_conjSub] at hy
  exact hy

theorem TwoBlk.exists_swap (h : TwoBlk X H₁ H₂ m) {t₀ : MulAut V} (ht₀ : t₀ ∈ X)
    (hconj : B6.conjSub t₀ H₁ = H₂) :
    ∃ t : MulAut V, t ∈ X ∧ t * t = 1 ∧ (∀ a ∈ H₁, t * a * t⁻¹ ∈ H₂) ∧
      (∀ b ∈ H₂, t * b * t⁻¹ ∈ H₁) ∧ ∀ x ∈ X, x ∈ H₁ ⊔ H₂ ∨ t * x ∈ H₁ ⊔ H₂ := by
  have hc₂ : B6.conjSub t₀ H₂ = H₁ := by
    rcases h.symm.conj_block ht₀ with h2 | h2
    · exfalso
      have : H₁ = H₂ := (B6.conjSub t₀).injective (hconj.trans h2.symm)
      apply h.ne_bot₁
      have h3 := h.inf
      rwa [← this, inf_idem] at h3
    · exact h2
  have hc₁' := fun y (hy : y ∈ H₁) => conj_mem_of_conjSub hconj hy
  have hc₂' := fun y (hy : y ∈ H₂) => conj_mem_of_conjSub hc₂ hy
  have hn₁ : t₀ * t₀ ∈ Subgroup.normalizer (H₁ : Set (MulAut V)) := by
    apply B6.mem_normalizer_of_forall_mem
    · intro y hy
      have := hc₂' _ (hc₁' y hy)
      simpa [mul_assoc] using this
    · intro y hy
      have h1 := conj_inv_mem_of_conjSub hc₂ hy
      have h2 := conj_inv_mem_of_conjSub hconj h1
      simpa [mul_assoc] using h2
  obtain ⟨a₁, ha₁, a₂, ha₂, hsq⟩ := mem_sup_of_commute h.comm
    (h.mem_sup_of_normalizes (X.mul_mem ht₀ ht₀) hn₁)
  have hcomm : (t₀ * a₁ * t₀⁻¹) * (t₀ * a₂ * t₀⁻¹) = a₁ * a₂ := by
    have : (t₀ * a₁ * t₀⁻¹) * (t₀ * a₂ * t₀⁻¹) = t₀ * (t₀ * t₀) * t₀⁻¹ := by
      rw [hsq]; group
    rw [this]
    have : t₀ * (t₀ * t₀) * t₀⁻¹ = t₀ * t₀ := by group
    rw [this, hsq]
  have hp : t₀ * a₁ * t₀⁻¹ ∈ H₂ := hc₁' a₁ ha₁
  have hq : t₀ * a₂ * t₀⁻¹ ∈ H₁ := hc₂' a₂ ha₂
  have hqp : (t₀ * a₂ * t₀⁻¹) * (t₀ * a₁ * t₀⁻¹) = a₁ * a₂ := by
    rw [← hcomm]; exact (h.comm _ hq _ hp)
  have hq1 : t₀ * a₂ * t₀⁻¹ = a₁ := by
    have h1 : a₁⁻¹ * (t₀ * a₂ * t₀⁻¹) = a₂ * (t₀ * a₁ * t₀⁻¹)⁻¹ := by
      calc a₁⁻¹ * (t₀ * a₂ * t₀⁻¹) = a₁⁻¹ * ((t₀ * a₂ * t₀⁻¹) * (t₀ * a₁ * t₀⁻¹)) *
            (t₀ * a₁ * t₀⁻¹)⁻¹ := by group
        _ = a₁⁻¹ * (a₁ * a₂) * (t₀ * a₁ * t₀⁻¹)⁻¹ := by rw [hqp]
        _ = a₂ * (t₀ * a₁ * t₀⁻¹)⁻¹ := by group
    have h2 : a₁⁻¹ * (t₀ * a₂ * t₀⁻¹) ∈ H₁ ⊓ H₂ :=
      ⟨H₁.mul_mem (H₁.inv_mem ha₁) hq, h1 ▸ H₂.mul_mem ha₂ (H₂.inv_mem hp)⟩
    rw [h.inf, Subgroup.mem_bot] at h2
    exact (inv_mul_eq_one.mp h2).symm
  have ht2 : (t₀ * a₂⁻¹) * (t₀ * a₂⁻¹) = 1 := by
    calc (t₀ * a₂⁻¹) * (t₀ * a₂⁻¹) = (t₀ * a₂ * t₀⁻¹)⁻¹ * (t₀ * t₀) * a₂⁻¹ := by group
      _ = 1 := by rw [hq1, hsq]; group
  have ha₂X : a₂ ∈ X := h.h2X ha₂
  have htX : t₀ * a₂⁻¹ ∈ X := X.mul_mem ht₀ (X.inv_mem ha₂X)
  have hconj₁ : ∀ a ∈ H₁, (t₀ * a₂⁻¹) * a * (t₀ * a₂⁻¹)⁻¹ ∈ H₂ := by
    intro a ha
    have e : a₂ * a = a * a₂ := (h.comm a ha a₂ ha₂).symm
    have : (t₀ * a₂⁻¹) * a * (t₀ * a₂⁻¹)⁻¹ = t₀ * a * t₀⁻¹ := by
      calc (t₀ * a₂⁻¹) * a * (t₀ * a₂⁻¹)⁻¹ = t₀ * (a₂⁻¹ * a * a₂) * t₀⁻¹ := by group
        _ = t₀ * a * t₀⁻¹ := by rw [show a₂⁻¹ * a * a₂ = a by rw [mul_assoc, ← e]; group]
    rw [this]
    exact hc₁' a ha
  have hconj₂ : ∀ b ∈ H₂, (t₀ * a₂⁻¹) * b * (t₀ * a₂⁻¹)⁻¹ ∈ H₁ := by
    intro b hb
    have : (t₀ * a₂⁻¹) * b * (t₀ * a₂⁻¹)⁻¹ = t₀ * (a₂⁻¹ * b * a₂) * t₀⁻¹ := by group
    rw [this]
    exact hc₂' _ (H₂.mul_mem (H₂.mul_mem (H₂.inv_mem ha₂) hb) ha₂)
  refine ⟨t₀ * a₂⁻¹, htX, ht2, hconj₁, hconj₂, fun x hx => ?_⟩
  rcases h.conj_block hx with hxc | hxc
  · left
    refine h.mem_sup_of_normalizes hx ?_
    apply B6.mem_normalizer_of_forall_mem
    · intro y hy
      have := conj_mem_of_conjSub hxc hy
      exact this
    · intro y hy
      exact conj_inv_mem_of_conjSub hxc hy
  · right
    refine h.mem_sup_of_normalizes (X.mul_mem htX hx) ?_
    set t := t₀ * a₂⁻¹ with ht
    have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    apply B6.mem_normalizer_of_forall_mem
    · intro y hy
      have h1 : x * y * x⁻¹ ∈ H₂ := conj_mem_of_conjSub hxc hy
      have h2 := hconj₂ _ h1
      simpa [mul_assoc] using h2
    · intro y hy
      have h1 : t * y * t⁻¹ ∈ H₂ := hconj₁ y hy
      have h2 : x⁻¹ * (t * y * t⁻¹) * x ∈ H₁ := conj_inv_mem_of_conjSub hxc h1
      rw [ht1] at h2
      simpa [mul_assoc, ht1] using h2

end TwoBlocks

section Classification

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {𝓗 : Finset (Subgroup (MulAut V))}

structure WreathData (X T : Subgroup (MulAut V)) (m : ℕ) (H₁ H₂ : Subgroup (MulAut V))
    (θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m)) (θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)) (β₁ β₂ : ↥(coreMod m) →* V)
    (Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥X) : Prop where
  m35 : m = 3 ∨ m = 5
  tb : TwoBlk X H₁ H₂ m
  h1X : H₁ ≤ X
  h2X : H₂ ≤ X
  ffJ_eq : ffJ X = H₁ ⊔ H₂
  inf : H₁ ⊓ H₂ = ⊥
  comm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a
  Ψ₁ : ∀ σ, ((Ψ (wrI₁ σ) : ↥X) : MulAut V) = ((θ₁.symm σ : ↥H₁) : MulAut V)
  Ψ₂ : ∀ σ, ((Ψ (wrI₂ σ) : ↥X) : MulAut V) = ((θ₂.symm σ : ↥H₂) : MulAut V)
  Ψmem : ∀ w, ((Ψ w : ↥X) : MulAut V) ∈ H₁ ⊔ H₂ ↔ w.right = 1
  eq₁ : ∀ (x : ↥H₁) (u : ↥(coreMod m)), β₁ (coreAct m (θ₁ x) u) = (x : MulAut V) (β₁ u)
  range₁ : β₁.range = commV H₁
  ker₁ : β₁.ker = ⊥
  eq₂ : ∀ (x : ↥H₂) (u : ↥(coreMod m)), β₂ (coreAct m (θ₂ x) u) = (x : MulAut V) (β₂ u)
  range₂ : β₂.range = commV H₂
  ker₂ : β₂.ker = ⊥
  supV : commV H₁ ⊔ commV H₂ = ⊤
  infV : commV H₁ ⊓ commV H₂ = ⊥
  act₁ : ∀ a ∈ H₁, ∀ v ∈ commV H₂, a v = v
  act₂ : ∀ a ∈ H₂, ∀ v ∈ commV H₁, a v = v
  swap : ∃ t ∈ T, B6.conjSub t H₁ = H₂

@[expose] def WreathShape (X T : Subgroup (MulAut V)) (m : ℕ) : Prop :=
  ∃ (H₁ H₂ : Subgroup (MulAut V)) (θ₁ : ↥H₁ ≃* Equiv.Perm (Fin m))
      (θ₂ : ↥H₂ ≃* Equiv.Perm (Fin m)) (β₁ β₂ : ↥(coreMod m) →* V)
      (Ψ : (Equiv.Perm (Fin m) ≀ᵣ Q2) ≃* ↥X), WreathData X T m H₁ H₂ θ₁ θ₂ β₁ β₂ Ψ

theorem BlkCtx.shape_of_card_two (h : BlkCtx X T M 𝓗) (hX : IsRankTwoQuotient ↥X)
    (hcard : 𝓗.card = 2) (hsym : ∀ H ∈ 𝓗, ∃ m, SymBlk M H m) : ∃ m, WreathShape X T m := by
  classical
  obtain ⟨H₁, H₂, hne, h𝓗⟩ := Finset.card_eq_two.mp hcard
  have h₁ : H₁ ∈ 𝓗 := by rw [h𝓗]; simp
  have h₂ : H₂ ∈ 𝓗 := by rw [h𝓗]; simp
  obtain ⟨m₁, hm₁3, hm₁odd, θ₁, β₁, hβ₁eq, hβ₁r, hβ₁k, -⟩ := hsym H₁ h₁
  obtain ⟨m₂, hm₂3, hm₂odd, θ₂, β₂, hβ₂eq, hβ₂r, hβ₂k, -⟩ := hsym H₂ h₂
  obtain ⟨t₀, ht₀T, ht₀⟩ := h.trans h₁ h₂
  have hcardeq : Nat.card H₁ = Nat.card H₂ := by rw [← ht₀]; exact (card_conjSub t₀ H₁).symm
  have hcardperm : ∀ (m : ℕ) (H : Subgroup (MulAut V)) (θ : ↥H ≃* Equiv.Perm (Fin m)),
      Nat.card H = Nat.factorial m := fun m H θ => by
    rw [Nat.card_congr θ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hm : m₁ = m₂ := by
    have h1 := hcardperm m₁ H₁ θ₁
    have h2 := hcardperm m₂ H₂ θ₂
    rw [h1, h2] at hcardeq
    exact (Nat.factorial_inj (by omega)).mp hcardeq
  subst hm
  have hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a := fun a ha b hb => h.comm_of_ne h₁ h₂ hne ha hb
  have hinf : H₁ ⊓ H₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact (h.indep₂ h₁ h₂ hne hx.1 (H₂.inv_mem hx.2) (mul_inv_cancel x)).1
  have hm35 : m₁ = 3 ∨ m₁ = 5 := by
    by_contra hcon
    push Not at hcon
    have hge : 6 ≤ m₁ := by
      obtain ⟨k, hk⟩ := hm₁odd
      omega
    exact false_of_two_blocks hX (h.mem_le h₁) (h.mem_le h₂) θ₁ θ₂ hge hm₂3 hcomm
      (fun a ha b hb hab => h.indep₂ h₁ h₂ hne ha hb hab)
  have hJ : ffJ X = H₁ ⊔ H₂ := by
    rw [h.ffJ_eq, h𝓗, Finset.iSup_insert, Finset.iSup_singleton]
  have hsupV : commV H₁ ⊔ commV H₂ = ⊤ := by
    have := h.iSup_comm
    rwa [h𝓗, Finset.iSup_insert, Finset.iSup_singleton] at this
  have hinfV : commV H₁ ⊓ commV H₂ = ⊥ := by
    have := h.inf_iSup_comm h₁
    rw [h𝓗, Finset.iSup_insert, Finset.iSup_singleton, iSup_pos hne.symm] at this
    have e : (⨆ (_ : H₁ ≠ H₁), commV H₁) = ⊥ := by simp
    rwa [e, bot_sup_eq] at this
  have hact₁ : ∀ a ∈ H₁, ∀ v ∈ commV H₂, a v = v := fun a ha v hv =>
    h.act_commV_of_ne h₂ h₁ hne.symm ha hv
  have hact₂ : ∀ a ∈ H₂, ∀ v ∈ commV H₁, a v = v := fun a ha v hv =>
    h.act_commV_of_ne h₁ h₂ hne ha hv
  have htb : TwoBlk X H₁ H₂ m₁ :=
    { m35 := hm35
      h1X := h.mem_le h₁
      h2X := h.mem_le h₂
      Ynorm := fun x hx y hy => by
        rw [← hJ] at hy ⊢
        exact (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) y).mp hy
      comm := hcomm
      inf := hinf
      supV := hsupV
      infV := hinfV
      act₁ := hact₁
      act₂ := hact₂
      sym₁ := ⟨θ₁, β₁, hβ₁eq, hβ₁r, hβ₁k⟩
      sym₂ := ⟨θ₂, β₂, hβ₂eq, hβ₂r, hβ₂k⟩ }
  obtain ⟨t, htX, htt, hc₁, hc₂, hcover⟩ := htb.exists_swap (h.mp.isSylow.1 ht₀T) ht₀
  have hsetup : WreathSetup X H₁ H₂ t :=
    { h1X := h.mem_le h₁
      h2X := h.mem_le h₂
      htX := htX
      comm := hcomm
      inf := hinf
      tt := htt
      c₁ := hc₁
      c₂ := hc₂
      ne := htb.ne_bot₁
      cover := hcover }
  have ht1 : t⁻¹ = t := hsetup.t_inv
  have hcj : B6.conjSub t H₁ = H₂ := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have h1 : t⁻¹ * y * t ∈ H₁ := B6.mem_conjSub.mp hy
      have := hc₁ _ h1
      have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
      rwa [e] at this
    · rw [B6.mem_conjSub, ht1]
      have := hc₂ y hy
      rwa [ht1] at this
  let cjt : ↥H₂ ≃* ↥H₁ :=
    { toFun := fun b => ⟨t * b * t⁻¹, hc₂ b b.2⟩
      invFun := fun a => ⟨t * a * t⁻¹, hc₁ a a.2⟩
      left_inv := fun b => Subtype.ext (by
        show t * (t * (b : MulAut V) * t⁻¹) * t⁻¹ = b
        calc t * (t * (b : MulAut V) * t⁻¹) * t⁻¹ = (t * t) * (b : MulAut V) * (t⁻¹ * t⁻¹) := by
              group
          _ = b := by rw [htt, ht1, htt]; group)
      right_inv := fun a => Subtype.ext (by
        show t * (t * (a : MulAut V) * t⁻¹) * t⁻¹ = a
        calc t * (t * (a : MulAut V) * t⁻¹) * t⁻¹ = (t * t) * (a : MulAut V) * (t⁻¹ * t⁻¹) := by
              group
          _ = a := by rw [htt, ht1, htt]; group)
      map_mul' := fun a b => Subtype.ext (by
        show t * ((a : MulAut V) * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
        group) }
  let θ₂' : ↥H₂ ≃* Equiv.Perm (Fin m₁) := cjt.trans θ₁
  let β₂' : ↥(coreMod m₁) →* V := (t.toMonoidHom).comp β₁
  have hβ₂'inj : Function.Injective β₂' := by
    have : Function.Injective β₁ := by
      rw [injective_iff_map_eq_one]
      intro u hu
      have : u ∈ β₁.ker := hu
      rw [hβ₁k] at this
      simpa using this
    exact t.injective.comp this
  refine ⟨m₁, H₁, H₂, θ₁, θ₂', β₁, β₂', wrapEquiv hsetup θ₁, ?_⟩
  refine ⟨hm35, htb, h.mem_le h₁, h.mem_le h₂, hJ, hinf, hcomm, ?_, ?_, ?_, hβ₁eq, hβ₁r, hβ₁k, ?_, ?_,
    ?_, hsupV, hinfV, hact₁, hact₂, ⟨t₀, ht₀T, ht₀⟩⟩
  · intro σ
    rw [wrapEquiv_wrI₁]
    rfl
  · intro σ
    rw [wrapEquiv_wrI₂]
    rfl
  · exact wrapEquiv_mem_iff hsetup θ₁
  · intro x u
    have hy : θ₂' x = θ₁ ⟨t * (x : MulAut V) * t⁻¹, hc₂ x x.2⟩ := rfl
    rw [hy]
    show t (β₁ (coreAct m₁ (θ₁ ⟨t * (x : MulAut V) * t⁻¹, hc₂ x x.2⟩) u)) = (x : MulAut V) (t (β₁ u))
    rw [hβ₁eq]
    have e : t * (t * (x : MulAut V) * t⁻¹) = (x : MulAut V) * t := by
      calc t * (t * (x : MulAut V) * t⁻¹) = (t * t) * (x : MulAut V) * t⁻¹ := by group
        _ = (x : MulAut V) * t := by rw [htt, one_mul, ht1]
    have := congrArg (fun z : MulAut V => z (β₁ u)) e
    simpa [MulAut.mul_apply] using this
  · show (t.toMonoidHom.comp β₁).range = commV H₂
    rw [MonoidHom.range_comp, hβ₁r, ← hcj]
    exact (B19.commV_map_conj t H₁).symm
  · rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    apply hβ₂'inj
    rw [map_one]
    exact hu

end Classification

end Ch3z

end CFSG.Quasithin
