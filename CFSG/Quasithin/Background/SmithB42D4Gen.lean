module

public import CFSG.Quasithin.Background.SmithB42D4Pure

public section

namespace CFSG.Quasithin.B42D4

open scoped commutatorElement
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

theorem commutator_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

section Span

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "kk" => trialityFixedField K σ.toRingHom

omit [Finite K] in
theorem eq_zero_of_tr_mul {μ : K} (h : ∀ s, tr σ (μ * s) = 0) : μ = 0 := by
  by_contra hμ
  have h1 := h μ⁻¹
  rw [mul_inv_cancel₀ hμ, tr_of_fixed σ (map_one σ)] at h1
  exact one_ne_zero h1

omit [Finite K] [CharP K 2] in
theorem bF_smul_right {a : K} (ha : σ a = a) (s s' : K) : bF σ s (a * s') = a * bF σ s s' := by
  simp only [bF, map_mul, ha]; ring

omit [Finite K] in
include hσ3 in
theorem eq_zero_of_tr_bF {lam : K} (hσ1 : ∃ x : K, σ x ≠ x)
    (h : ∀ s s', tr σ (lam * bF σ s s') = 0) : lam = 0 := by
  have h3 := sigma_sigma_sigma σ hσ3
  have h1 : ∀ s, tr σ ((σ (σ lam) + σ lam) * s) = 0 := by
    intro s
    have e := h s 1
    simp only [tr, bF, map_mul, map_add, map_one, mul_one, h3] at e ⊢
    linear_combination e
  have hs : σ (σ lam) + σ lam = 0 := eq_zero_of_tr_mul σ h1
  have hlk : σ lam = lam := by
    have e1 : σ (σ lam) = σ lam := by linear_combination (norm := ring2) hs
    have e2 := congrArg σ e1
    rw [h3] at e2
    exact e1.symm.trans e2.symm
  by_contra hl
  obtain ⟨x, hx⟩ := hσ1
  have h2 : ∀ s, tr σ ((σ x + σ (σ x)) * s) = 0 := by
    intro s
    have e := h s x
    rw [tr_mul_fixed σ hlk] at e
    have e' : tr σ (bF σ s x) = 0 := (mul_eq_zero.1 e).resolve_left hl
    simp only [tr, bF, map_mul, map_add, h3] at e' ⊢
    linear_combination e'
  have hx2 : σ x + σ (σ x) = 0 := eq_zero_of_tr_mul σ h2
  apply hx
  have e1 : σ (σ x) = σ x := by linear_combination (norm := ring2) hx2
  have e2 := congrArg σ e1
  rw [h3] at e2
  exact e1.symm.trans e2.symm

omit [Finite K] [CharP K 2] in
theorem bF_expand {t₁ t₂ t₃ a₁ a₂ a₃ b₁ b₂ b₃ : K} (ha₁ : σ a₁ = a₁) (ha₂ : σ a₂ = a₂)
    (ha₃ : σ a₃ = a₃) (hb₁ : σ b₁ = b₁) (hb₂ : σ b₂ = b₂) (hb₃ : σ b₃ = b₃) :
    bF σ (a₁ * t₁ + a₂ * t₂ + a₃ * t₃) (b₁ * t₁ + b₂ * t₂ + b₃ * t₃) =
      a₁ * b₁ * bF σ t₁ t₁ + a₁ * b₂ * bF σ t₁ t₂ + a₁ * b₃ * bF σ t₁ t₃ +
      a₂ * b₁ * bF σ t₂ t₁ + a₂ * b₂ * bF σ t₂ t₂ + a₂ * b₃ * bF σ t₂ t₃ +
      a₃ * b₁ * bF σ t₃ t₁ + a₃ * b₂ * bF σ t₃ t₂ + a₃ * b₃ * bF σ t₃ t₃ := by
  simp only [bF, map_add, map_mul, ha₁, ha₂, ha₃, hb₁, hb₂, hb₃]
  ring

include hσ3 in
theorem bF_generate (hσ1 : ∃ x : K, σ x ≠ x) {t₁ t₂ t₃ : K}
    (hspan : ∀ x : K, ∃ a₁ a₂ a₃ : K, σ a₁ = a₁ ∧ σ a₂ = a₂ ∧ σ a₃ = a₃ ∧
      x = a₁ * t₁ + a₂ * t₂ + a₃ * t₃)
    (V : AddSubgroup K) (hV : ∀ β : K, σ β = β → ∀ s ∈ ({t₁, t₂, t₃} : Set K),
      ∀ s' ∈ ({t₁, t₂, t₃} : Set K), β * bF σ s s' ∈ V) (x : K) : x ∈ V := by
  classical
  set S : Set K := {y | ∃ s ∈ ({t₁, t₂, t₃} : Set K), ∃ s' ∈ ({t₁, t₂, t₃} : Set K),
    y = bF σ s s'} with hS
  set W := Submodule.span kk S with hW
  have hWV : ∀ y ∈ W, y ∈ V := by
    intro y hy
    have key : ∀ y ∈ W, ∀ c : kk, (c : K) * y ∈ V := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨s, hs, s', hs', rfl⟩ := hy
        exact fun c => hV c c.2 s hs s' hs'
      | zero => intro c; rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => intro c; rw [mul_add]; exact add_mem (hy c) (hz c)
      | smul a y _ hy =>
        intro c
        have : (c : K) * (a • y) = ((c * a : kk) : K) * y := by
          rw [Subfield.coe_mul, Algebra.smul_def, mul_assoc]; rfl
        rw [this]
        exact hy _
    simpa using key y hy 1
  have hWtop : W = ⊤ := by
    by_contra hW'
    obtain ⟨φ, hφ0, hφW⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.2 hW')
    have hB := trialityTraceForm_nondegenerate K τ₀ hσ3
    set lam := ((trialityTraceForm K τ₀ hσ3).toDual hB).symm φ with hlam
    have hφ : ∀ y, (φ y : K) = tr σ (lam * y) := by
      intro y
      have e : (trialityTraceForm K τ₀ hσ3).toDual hB lam = φ := LinearEquiv.apply_symm_apply _ _
      rw [← e, LinearMap.BilinForm.toDual_def, trialityTraceForm_apply, ← tr_eq_coe_trace σ hσ3]
    have hmemS : ∀ s ∈ ({t₁, t₂, t₃} : Set K), ∀ s' ∈ ({t₁, t₂, t₃} : Set K),
        bF σ s s' ∈ W := fun s hs s' hs' => Submodule.subset_span ⟨s, hs, s', hs', rfl⟩
    have hsm : ∀ a : K, σ a = a → ∀ y ∈ W, a * y ∈ W := by
      intro a ha y hy
      have : a * y = (⟨a, ha⟩ : kk) • y := by rw [Algebra.smul_def]; rfl
      rw [this]; exact W.smul_mem _ hy
    have hall : ∀ s s', bF σ s s' ∈ W := by
      intro s s'
      obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, rfl⟩ := hspan s
      obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, rfl⟩ := hspan s'
      rw [bF_expand σ ha₁ ha₂ ha₃ hb₁ hb₂ hb₃]
      have m : ∀ a b : K, σ a = a → σ b = b → ∀ s ∈ ({t₁, t₂, t₃} : Set K),
          ∀ s' ∈ ({t₁, t₂, t₃} : Set K), a * b * bF σ s s' ∈ W := fun a b ha hb s hs s' hs' =>
        hsm (a * b) (by rw [map_mul, ha, hb]) _ (hmemS s hs s' hs')
      have h1 : t₁ ∈ ({t₁, t₂, t₃} : Set K) := by simp
      have h2 : t₂ ∈ ({t₁, t₂, t₃} : Set K) := by simp
      have h3 : t₃ ∈ ({t₁, t₂, t₃} : Set K) := by simp
      refine add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem (add_mem ?_ ?_) ?_) ?_)
        ?_) ?_) ?_) ?_) ?_ <;> apply m <;> assumption
    have hzero : ∀ s s', tr σ (lam * bF σ s s') = 0 := fun s s' => by
      rw [← hφ]
      have := hφW (hall s s')
      rw [LinearMap.mem_ker] at this
      rw [this]; rfl
    have hl : lam = 0 := eq_zero_of_tr_bF σ hσ3 hσ1 hzero
    apply hφ0
    have : φ = (trialityTraceForm K τ₀ hσ3).toDual hB lam := (LinearEquiv.apply_symm_apply _ _).symm
    rw [this, hl, map_zero]
  exact hWV x (hWtop ▸ Submodule.mem_top)

end Span

section Orbit

variable {K : Type} [Field K] (σ : K ≃+* K)

local notation "Xr" => pinnedX TwistTag.D4.tag K

@[expose] noncomputable def nx₁ (c : K) : ModGL TwistTag.D4.tag K :=
  Xr (-d4E0) c * Xr (-d4E1) (σ c) * Xr (-d4E3) (σ (σ c))

theorem orbitX_zero_eq (c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      ox₁ σ c := by
  rw [coe_orbitX, coe_ox₁_eq]
  have h1 : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
  have h2 : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have p1 : (TwistTag.D4.perm ^ 1) ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p2 : (TwistTag.D4.perm ^ 2) ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
  have e0 : d4E0 = Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  have e1 : d4E1 = Pi.single (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  have e3 : d4E3 = Pi.single (⟨3, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  rw [h1, h2, e0, e1, e3, pinnedX_single, pinnedX_single, pinnedX_single]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, pow_zero, p1, p2]
  simp [mul_assoc, pow_succ]

theorem orbitY_zero_eq (c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :
    (orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      nx₁ σ c := by
  rw [coe_orbitY, nx₁]
  have h1 : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
  have h2 : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have p1 : (TwistTag.D4.perm ^ 1) ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have p2 : (TwistTag.D4.perm ^ 2) ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
  have e0 : d4E0 = Pi.single (⟨0, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  have e1 : d4E1 = Pi.single (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  have e3 : d4E3 = Pi.single (⟨3, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  rw [h1, h2, e0, e1, e3, pinnedX_neg_single, pinnedX_neg_single, pinnedX_neg_single]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, pow_zero, p1, p2]
  simp [mul_assoc, pow_succ]

theorem orbitX_one_eq (c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      Xr d4C c := by
  rw [coe_orbitX]
  have h1 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have h2 : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hC : d4C = Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  rw [h1, h2, hC, pinnedX_single]
  simp

theorem orbitY_one_eq (c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :
    (orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      Xr (-d4C) c := by
  rw [coe_orbitY]
  have h1 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have h2 : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hC : d4C = Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 := by decide
  rw [h1, h2, hC, pinnedX_neg_single]
  simp

end Orbit

section Relations

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "Xr" => pinnedX TwistTag.D4.tag K

omit [Finite K] in
theorem np_conj {ν μ : Fin TwistTag.D4.tag.rank → ℤ} (h1 : d4CommB d4P ν = true)
    (h2 : d4SumB (-d4P) ν μ = true) (h3 : d4SumB d4P μ ν = true) (h4 : d4CommB ν μ = true)
    (x : K) :
    (Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1) * Xr ν x * (Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1)⁻¹ =
      Xr μ x := by
  have e1 := conj_pinnedX_of_comm (K := K) h1 1 x
  have e2 := conj_pinnedX_of_sum (K := K) h2 1 x
  have e3 := conj_pinnedX_of_sum (K := K) h3 1 x
  rw [one_mul] at e2 e3
  have hc := (commute_of_d4CommB (K := K) h4 x x).eq
  calc (Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1) * Xr ν x * (Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1)⁻¹ =
      Xr d4P 1 * (Xr (-d4P) 1 * (Xr d4P 1 * Xr ν x * (Xr d4P 1)⁻¹) * (Xr (-d4P) 1)⁻¹) *
        (Xr d4P 1)⁻¹ := by group
    _ = Xr d4P 1 * (Xr μ x * Xr ν x) * (Xr d4P 1)⁻¹ := by rw [e1, e2]
    _ = (Xr d4P 1 * Xr μ x * (Xr d4P 1)⁻¹) * (Xr d4P 1 * Xr ν x * (Xr d4P 1)⁻¹) :=
        conj_mul2 _ _ _
    _ = Xr μ x := by
        rw [e3, e1, mul_assoc, ← hc, ← mul_assoc, Xr_mul_self, one_mul]

omit [Finite K] in
theorem np_ox₄ (d : K) :
    (Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1) * ox₄ σ d * (Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1)⁻¹ =
      nx₁ σ d := by
  rw [coe_ox₄_eq, conj_mul3, np_conj (μ := -d4E0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel), np_conj (μ := -d4E1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel), np_conj (μ := -d4E3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel), nx₁]

include hσ3 in
theorem comm_y_z (a c d d' : K) :
    ⁅qE σ 0 c d 0 0, ox₁ σ a * qE σ 0 0 d' 0 0⁆ =
      qE σ 0 0 (bF σ a c) (e5F σ a c + tr σ (a * d)) (tr σ (d' * c) + e6F σ a c) := by
  have e1 : ⁅qE σ 0 c d 0 0, ox₁ σ a * qE σ 0 0 d' 0 0⁆ =
      qE σ 0 c d 0 0 * (ox₁ σ a * (qE σ 0 0 d' 0 0 * (qE σ 0 c d 0 0)⁻¹ *
        (qE σ 0 0 d' 0 0)⁻¹) * (ox₁ σ a)⁻¹) := by
    rw [commutatorElement_def]; group
  rw [e1, qE_inv σ hσ3 0 c d 0 0, qE_conj_qE σ hσ3 0 0 d' 0 0, conj_ox₁_qE σ hσ3 (map_zero σ),
    qE_mul σ hσ3]
  refine qE_congr σ ?_ ?_ ?_ ?_ ?_
  · ring2
  · ring2
  · ring2
  · ring2
  · simp only [tr, mul_zero, map_zero, zero_mul, add_zero, zero_add, map_mul]
    ring2

omit
  [Finite K] in
@[expose] def rootAddSubgroup (x : K → ModGL TwistTag.D4.tag K) (hx : ∀ c d, x (c + d) = x c * x d)
    (hx0 : x 0 = 1) (H : Subgroup (ModGL TwistTag.D4.tag K)) : AddSubgroup K where
  carrier := {d | x d ∈ H}
  add_mem' {a b} ha hb := by
    change x (a + b) ∈ H
    rw [hx]; exact mul_mem ha hb
  zero_mem' := by
    change x 0 ∈ H
    rw [hx0]; exact one_mem _
  neg_mem' {a} ha := by
    change x (-a) ∈ H
    rwa [CharTwo.neg_eq]

include hσ3 in
theorem five_lines_generate (hσ1 : ∃ x : K, σ x ≠ x) {t₁ t₂ t₃ : K}
    (hspan : ∀ x : K, ∃ a₁ a₂ a₃ : K, σ a₁ = a₁ ∧ σ a₂ = a₂ ∧ σ a₃ = a₃ ∧
      x = a₁ * t₁ + a₂ * t₂ + a₃ * t₃)
    {H : Subgroup (ModGL TwistTag.D4.tag K)}
    (hΛ : ∀ e f : K, σ e = e → σ f = f → Xr d4P e * Xr d4H f ∈ H)
    (hΛ₀ : ∀ e f : K, σ e = e → σ f = f → nW0 K * (Xr d4P e * Xr d4H f) * (nW0 K)⁻¹ ∈ H)
    (hΛᵢ : ∀ t ∈ ({t₁, t₂, t₃} : Set K), ∀ e f : K, σ e = e → σ f = f →
      (ox₁ σ t * nA K) * (Xr d4P e * Xr d4H f) * (ox₁ σ t * nA K)⁻¹ ∈ H) :
    graphFixedRootGroup TwistTag.D4 K τ₀ ≤ H := by
  have h3 := sigma_sigma_sigma σ hσ3
  have hN : ∀ s, σ (nK σ s) = nK σ s := sigma_nK σ hσ3
  have hP : ∀ e : K, σ e = e → Xr d4P e ∈ H := fun e he => by
    simpa [pinnedX_zero] using hΛ e 0 he (map_zero σ)
  have hH : ∀ f : K, σ f = f → Xr d4H f ∈ H := fun f hf => by
    simpa [pinnedX_zero] using hΛ 0 f (map_zero σ) hf
  have hnP : ∀ e : K, σ e = e → Xr (-d4P) e ∈ H := fun e he => by
    have h := hΛ₀ e 0 he (map_zero σ)
    rwa [pinnedX_zero, mul_one, nW0_conj (by decide +kernel), w0_neg (by simp)] at h
  have hnH : ∀ f : K, σ f = f → Xr (-d4H) f ∈ H := fun f hf => by
    have h := hΛ₀ 0 f (map_zero σ) hf
    rwa [pinnedX_zero, one_mul, nW0_conj (by decide +kernel), w0_neg (by simp)] at h
  have hC : ∀ β : K, σ β = β → Xr d4C β ∈ H := fun β hβ => by
    have h := commutator_of_d4SumB (K := K) (α := d4H) (β := -d4P) (γ := d4C)
      (by decide +kernel) β 1
    rw [mul_one] at h
    rw [← h]
    exact commutator_mem (hH β hβ) (hnP 1 (map_one σ))
  have hnC : ∀ β : K, σ β = β → Xr (-d4C) β ∈ H := fun β hβ => by
    have h := commutator_of_d4SumB (K := K) (α := d4P) (β := -d4H) (γ := -d4C)
      (by decide +kernel) β 1
    rw [mul_one] at h
    rw [← h]
    exact commutator_mem (hP β hβ) (hnH 1 (map_one σ))
  have hMb : orbitRankOneGroup TwistTag.D4 K τ₀ ⟨1, by decide⟩ ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    have hfix : ∀ c : orbitField TwistTag.D4 K τ₀ ⟨1, by decide⟩, σ (c : K) = c := fun c => by
      have h := (mem_orbitField (t := TwistTag.D4) (σ := τ₀) (a := ⟨1, by decide⟩)).1 c.2
      have h1 : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
      rw [h1, pow_one] at h
      exact h
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · dsimp only; rw [SetLike.mem_coe, orbitX_one_eq]; exact hC c (hfix c)
    · dsimp only; rw [SetLike.mem_coe, orbitY_one_eq]; exact hnC c (hfix c)
  have hnB : nB K ∈ H := by
    rw [nB, rB, canonicalRep_orbitReflection_eq_orbitN TwistTag.D4 τ₀]
    exact hMb (orbitN_one_mem_orbitRankOneGroup _)
  have hy : ∀ t ∈ ({t₁, t₂, t₃} : Set K), ∀ β : K, σ β = β →
      qE σ 0 (β * t) (β * (σ t * σ (σ t))) 0 0 ∈ H := by
    intro t ht β hβ
    have h := hΛᵢ t ht β 0 hβ (map_zero σ)
    rw [pinnedX_zero, mul_one,
      show (ox₁ σ t * nA K) * Xr d4P β * (ox₁ σ t * nA K)⁻¹ =
        ox₁ σ t * (nA K * Xr d4P β * (nA K)⁻¹) * (ox₁ σ t)⁻¹ by group,
      nA_P, conj_ox₁_C σ hσ3 hβ] at h
    have e : qE σ 0 (β * t) (β * (σ t * σ (σ t))) 0 0 =
        (Xr d4C β)⁻¹ * qE σ β (β * t) (β * (σ t * σ (σ t))) (β * nK σ t) (β * β * nK σ t) *
          (Xr d4P (β * nK σ t) * Xr d4H (β * β * nK σ t))⁻¹ := by
      simp only [qE, pinnedX_zero, one_mul, mul_one]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hC β hβ)) h) (inv_mem (mul_mem
      (hP _ (by rw [map_mul, hβ, hN])) (hH _ (by rw [map_mul, map_mul, hβ, hN]))))
  have hz : ∀ t ∈ ({t₁, t₂, t₃} : Set K), ∀ β : K, σ β = β →
      ox₁ σ (β * t) * qE σ 0 0 (β * (σ t * σ (σ t))) 0 0 ∈ H := by
    intro t ht β hβ
    rw [← nB_qE σ]
    exact mul_mem (mul_mem hnB (hy t ht β hβ)) (inv_mem hnB)
  have hX4 : ∀ d : K, ox₄ σ d ∈ H := by
    intro d
    refine bF_generate σ hσ3 hσ1 hspan
      (rootAddSubgroup (ox₄ σ) (ox₄_add σ hσ3) (ox₄_zero' σ) H) ?_ d
    intro β hβ s hs s' hs'
    change ox₄ σ (β * bF σ s s') ∈ H
    have hz1 := hz s hs 1 (map_one σ)
    rw [one_mul, one_mul] at hz1
    have hcomm := comm_y_z σ hσ3 s (β * s') (β * (σ s' * σ (σ s'))) (σ s * σ (σ s))
    have hmem := commutator_mem (hy s' hs' β hβ) hz1
    rw [hcomm] at hmem
    set E := e5F σ s (β * s') + tr σ (s * (β * (σ s' * σ (σ s')))) with hEdef
    set F := tr σ (σ s * σ (σ s) * (β * s')) + e6F σ s (β * s') with hFdef
    have hE : σ E = E := by rw [hEdef, map_add, sigma_e5F σ hσ3, sigma_tr σ hσ3]
    have hF : σ F = F := by rw [hFdef, map_add, sigma_e6F σ hσ3, sigma_tr σ hσ3]
    have e : ox₄ σ (bF σ s (β * s')) =
        qE σ 0 0 (bF σ s (β * s')) E F * (Xr d4P E * Xr d4H F)⁻¹ := by
      simp only [qE, pinnedX_zero, ox₃_zero', one_mul]; group
    rw [← bF_smul_right σ hβ, e]
    exact mul_mem hmem (inv_mem (mul_mem (hP _ hE) (hH _ hF)))
  have hX1 : ∀ a : K, ox₁ σ a ∈ H := by
    have hV : ∀ t ∈ ({t₁, t₂, t₃} : Set K), ∀ β : K, σ β = β → ox₁ σ (β * t) ∈ H := by
      intro t ht β hβ
      have e : ox₁ σ (β * t) = ox₁ σ (β * t) * qE σ 0 0 (β * (σ t * σ (σ t))) 0 0 *
          (ox₄ σ (β * (σ t * σ (σ t))))⁻¹ := by
        simp only [qE, pinnedX_zero, ox₃_zero', one_mul, mul_one, mul_inv_cancel_right]
      rw [e]
      exact mul_mem (hz t ht β hβ) (inv_mem (hX4 _))
    intro a
    obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, rfl⟩ := hspan a
    rw [ox₁_add σ hσ3, ox₁_add σ hσ3]
    exact mul_mem (mul_mem (hV t₁ (by simp) a₁ ha₁) (hV t₂ (by simp) a₂ ha₂))
      (hV t₃ (by simp) a₃ ha₃)
  have hX3 : ∀ c : K, ox₃ σ c ∈ H := by
    have hV : ∀ t ∈ ({t₁, t₂, t₃} : Set K), ∀ β : K, σ β = β → ox₃ σ (β * t) ∈ H := by
      intro t ht β hβ
      have e : ox₃ σ (β * t) = qE σ 0 (β * t) (β * (σ t * σ (σ t))) 0 0 *
          (ox₄ σ (β * (σ t * σ (σ t))))⁻¹ := by
        simp only [qE, pinnedX_zero, one_mul, mul_one, mul_inv_cancel_right]
      rw [e]
      exact mul_mem (hy t ht β hβ) (inv_mem (hX4 _))
    intro c
    obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, rfl⟩ := hspan c
    rw [ox₃_add σ hσ3, ox₃_add σ hσ3]
    exact mul_mem (mul_mem (hV t₁ (by simp) a₁ ha₁) (hV t₂ (by simp) a₂ ha₂))
      (hV t₃ (by simp) a₃ ha₃)
  have hnp : Xr d4P 1 * Xr (-d4P) 1 * Xr d4P 1 ∈ H :=
    mul_mem (mul_mem (hP 1 (map_one σ)) (hnP 1 (map_one σ))) (hP 1 (map_one σ))
  have hnX1 : ∀ c : K, nx₁ σ c ∈ H := fun c => by
    rw [← np_ox₄ σ c]
    exact mul_mem (mul_mem hnp (hX4 c)) (inv_mem hnp)
  rw [graphFixedRootGroup_eq_iSup_orbitRankOneGroup σ.surjective]
  refine iSup_le fun a => ?_
  fin_cases a
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · dsimp only; rw [SetLike.mem_coe, orbitX_zero_eq]; exact hX1 c
    · dsimp only; rw [SetLike.mem_coe, orbitY_zero_eq]; exact hnX1 c
  · exact hMb

end Relations

end CFSG.Quasithin.B42D4
