module

public import CFSG.RankThree.PartTwo.Sec21.FF79KTypeLnLift

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.TLn

open Subgroup

variable {S : Type} [Group S]

@[expose] def QA (S : Type) [Group S] (R : Subgroup S) (n : ℕ) (a₀ : S) : Prop :=
  ∀ Y₀ : Subgroup (MulAut S), (∀ σ ∈ Y₀, σ a₀ = a₀) →
    (∀ σ ∈ Y₀, Nat.Coprime 3 (orderOf σ)) →
    (∀ c : S, c * a₀ = a₀ * c → ∀ σ ∈ Y₀, MulAut.conj c * σ * (MulAut.conj c)⁻¹ ∈ Y₀) →
    (∀ σ ∈ Y₀, ∀ x ∈ R, σ x = x) ∧ (n = 5 → ∀ σ ∈ Y₀, σ = 1)

theorem centAlphaS_iff {R : Subgroup S} {n : ℕ} :
    CentAlphaS S R n ↔ ∀ a₀ ∈ R, a₀ ≠ 1 → QA S R n a₀ := Iff.rfl

@[expose] def HBad (a₀ : S) : Prop :=
  ∀ s : S, s * a₀ = a₀ * s → s ≠ 1 → Nat.Coprime 3 (orderOf s) →
    ∃ w : S, w * a₀ = a₀ * w ∧ ¬ Nat.Coprime 3 (orderOf (s * (w * s * w⁻¹)))

@[expose] def HX (R : Subgroup S) (δ : MulAut S) (a₀ : S) : Prop :=
  ∀ s₀ : S, (∀ x ∈ R, s₀ * x⁻¹ * s₀⁻¹ = x) →
    ∃ c : S, c * a₀ = a₀ * c ∧ s₀ * δ c * s₀⁻¹ ≠ c

theorem center_triv {R : Subgroup S} (M : TModel S R) {s : S} (h : ∀ x : S, s * x = x * s) :
    s = 1 := by
  have hs : s ∈ R := M.cent s fun x _ => h x
  obtain ⟨τ, -, hτ⟩ := M.tau
  have h1 := hτ s hs
  have h2 : τ * s * τ⁻¹ = s := by rw [← h τ]; group
  have h3 : s * s = 1 := mul_eq_one_iff_eq_inv.mpr (h2.symm.trans h1)
  have h4 := M.cube s hs
  calc s = s * (s * s) := by rw [h3, mul_one]
    _ = s ^ 3 := (pow_three s).symm
    _ = 1 := h4

theorem conj_injective {R : Subgroup S} (M : TModel S R) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro x y hxy
  have hz : ∀ z : S, (x⁻¹ * y) * z = z * (x⁻¹ * y) := by
    intro z
    have e := DFunLike.congr_fun hxy z
    simp only [MulAut.conj_apply] at e
    calc x⁻¹ * y * z = x⁻¹ * (y * z * y⁻¹) * y := by group
      _ = x⁻¹ * (x * z * x⁻¹) * y := by rw [e]
      _ = z * (x⁻¹ * y) := by group
  exact inv_mul_eq_one.mp (center_triv M hz)

theorem aut_conj_conj (σ : MulAut S) (x : S) :
    σ * MulAut.conj x * σ⁻¹ = MulAut.conj (σ x) := by
  ext y
  simp [MulAut.conj_apply]

theorem hx_of_tau {R : Subgroup S} (M : TModel S R) (δ : MulAut S) {a₀ τ : S}
    (hτ : ∀ x ∈ R, τ * x * τ⁻¹ = x⁻¹)
    (h : ∀ p ∈ R, ∃ c : S, c * a₀ = a₀ * c ∧ (p * τ) * δ c * (p * τ)⁻¹ ≠ c) : HX R δ a₀ := by
  intro s₀ hs₀
  have hτ' : ∀ x ∈ R, τ⁻¹ * x * τ = x⁻¹ := by
    intro x hx
    have := hτ x⁻¹ (inv_mem hx)
    rw [inv_inv] at this
    calc τ⁻¹ * x * τ = τ⁻¹ * (τ * x⁻¹ * τ⁻¹) * τ := by rw [this]
      _ = x⁻¹ := by group
  have hp : s₀ * τ⁻¹ ∈ R := by
    refine M.cent _ fun x hx => ?_
    have h1 : s₀ * τ⁻¹ * x = (s₀ * τ⁻¹ * x * τ * s₀⁻¹) * (s₀ * τ⁻¹) := by group
    have h2 : s₀ * τ⁻¹ * x * τ * s₀⁻¹ = x := by
      calc s₀ * τ⁻¹ * x * τ * s₀⁻¹ = s₀ * (τ⁻¹ * x * τ) * s₀⁻¹ := by group
        _ = s₀ * x⁻¹ * s₀⁻¹ := by rw [hτ' x hx]
        _ = x := hs₀ x hx
    rw [h1, h2]
  obtain ⟨c, hc, hne⟩ := h _ hp
  refine ⟨c, hc, ?_⟩
  have : s₀ * τ⁻¹ * τ = s₀ := by group
  rwa [this] at hne

theorem qa_of_checks {R : Subgroup S} {n : ℕ} (M : TModel S R) (δ : MulAut S)
    (hδ : ∀ x ∈ R, δ x = x⁻¹)
    (hform : ∀ α : MulAut S, ∃ s₀ : S, ∃ ε : ℕ, ε ≤ 1 ∧ α = MulAut.conj s₀ * δ ^ ε)
    {a₀ : S} (ha₀ : a₀ ∈ R) (hb : HBad a₀) (hx : n = 5 → HX R δ a₀) : QA S R n a₀ := by
  intro Y₀ hfix hord hnorm
  have hinj := conj_injective M
  have hN : ∀ s : S, MulAut.conj s ∈ Y₀ → s = 1 := by
    intro s hs
    by_contra hs1
    have hca : s * a₀ = a₀ * s := by
      have := hfix _ hs
      simp only [MulAut.conj_apply] at this
      rwa [mul_inv_eq_iff_eq_mul] at this
    have hcop : Nat.Coprime 3 (orderOf s) := by
      rw [← orderOf_injective _ hinj s]; exact hord _ hs
    obtain ⟨w, hw, hnc⟩ := hb s hca hs1 hcop
    apply hnc
    have h1 : MulAut.conj (w * s * w⁻¹) ∈ Y₀ := by
      have := hnorm w hw _ hs
      simpa [map_mul, map_inv] using this
    have h2 : MulAut.conj (s * (w * s * w⁻¹)) ∈ Y₀ := by
      rw [map_mul]; exact Y₀.mul_mem hs h1
    rw [← orderOf_injective _ hinj]; exact hord _ h2
  have hB : ∀ σ ∈ Y₀, ∀ c : S, c * a₀ = a₀ * c → σ c = c := by
    intro σ hσ c hc
    have h1 := hnorm c hc σ hσ
    have h2 : MulAut.conj c * σ * (MulAut.conj c)⁻¹ * σ⁻¹ ∈ Y₀ :=
      Y₀.mul_mem h1 (Y₀.inv_mem hσ)
    have h3 : MulAut.conj (c * (σ c)⁻¹) =
        MulAut.conj c * σ * (MulAut.conj c)⁻¹ * σ⁻¹ := by
      rw [map_mul, map_inv, ← aut_conj_conj σ c]; group
    have := hN _ (h3 ▸ h2)
    exact (mul_inv_eq_one.mp this).symm
  refine ⟨fun σ hσ x hx => hB σ hσ x (M.comm x hx a₀ ha₀), fun h5 σ hσ => ?_⟩
  obtain ⟨s₀, ε, hε, hσe⟩ := hform σ
  interval_cases ε
  · have hσ' : σ = MulAut.conj s₀ := by simpa using hσe
    have : s₀ = 1 := hN s₀ (hσ' ▸ hσ)
    rw [hσ', this]; simp
  · have hσx : ∀ x, σ x = s₀ * δ x * s₀⁻¹ := fun x => by
      rw [hσe]; simp [MulAut.conj_apply]
    have hinv : ∀ x ∈ R, s₀ * x⁻¹ * s₀⁻¹ = x := fun x hx => by
      have := hB σ hσ x (M.comm x hx a₀ ha₀)
      rwa [hσx, hδ x hx] at this
    obtain ⟨c, hc, hne⟩ := hx h5 s₀ hinv
    exact absurd (by rw [← hσx]; exact hB σ hσ c hc) hne

theorem QA.inv {R : Subgroup S} {n : ℕ} {a₀ : S} (h : QA S R n a₀) : QA S R n a₀⁻¹ := by
  intro Y₀ hfix hord hnorm
  refine h Y₀ (fun σ hσ => ?_) hord (fun c hc => hnorm c ?_)
  · have := hfix σ hσ
    rw [map_inv] at this
    exact inv_injective this
  · exact (Commute.inv_right (show Commute c a₀ from hc)).eq

theorem QA.conj {R : Subgroup S} {n : ℕ} {a₀ : S} (h : QA S R n a₀) {t : S}
    (ht : t ∈ Subgroup.normalizer (R : Set S)) : QA S R n (t * a₀ * t⁻¹) := by
  intro Y₀ hfix hord hnorm
  let u : MulAut S := MulAut.conj t
  let φ : MulAut S →* MulAut S := (MulAut.conj u).toMonoidHom
  have hφ : ∀ σ : MulAut S, φ σ = u * σ * u⁻¹ := fun σ => by
    simp [φ, MulAut.conj_apply]
  let Y' : Subgroup (MulAut S) := Y₀.comap φ
  have hmem : ∀ σ, σ ∈ Y' ↔ u * σ * u⁻¹ ∈ Y₀ := fun σ => by
    rw [← hφ]; rfl
  have hci : u⁻¹ = MulAut.conj t⁻¹ := (map_inv (MulAut.conj : S →* MulAut S) t).symm
  have hres := h Y' (fun σ hσ => ?_) (fun σ hσ => ?_) (fun c hc σ hσ => ?_)
  · have hback : ∀ τ₀ ∈ Y₀, u⁻¹ * τ₀ * u ∈ Y' ∧ u * (u⁻¹ * τ₀ * u) * u⁻¹ = τ₀ := by
      intro τ₀ hτ₀
      have e : u * (u⁻¹ * τ₀ * u) * u⁻¹ = τ₀ := by group
      exact ⟨(hmem _).mpr (by rw [e]; exact hτ₀), e⟩
    refine ⟨fun τ₀ hτ₀ x hx => ?_, fun h5 τ₀ hτ₀ => ?_⟩
    · obtain ⟨hσ, e⟩ := hback τ₀ hτ₀
      have hx' : t⁻¹ * x * t ∈ R := by
        refine (Subgroup.mem_normalizer_iff.mp ht (t⁻¹ * x * t)).mpr ?_
        have : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
        rw [this]; exact hx
      have h1 := hres.1 _ hσ _ hx'
      have h2 : τ₀ x = (u * (u⁻¹ * τ₀ * u) * u⁻¹) x := by rw [e]
      rw [h2]
      simp only [MulAut.mul_apply, hci, MulAut.conj_apply, u] at h1 ⊢
      simp only [inv_inv] at h1 ⊢
      have e1 : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rw [e1] at h1 ⊢
      rw [h1]; group
    · obtain ⟨hσ, e⟩ := hback τ₀ hτ₀
      have h1 := hres.2 h5 _ hσ
      rw [h1] at e
      rw [← e]; group
  · have e := hfix _ ((hmem σ).mp hσ)
    rw [hci] at e
    simp only [MulAut.mul_apply, MulAut.conj_apply, u] at e
    have h1 : t⁻¹ * (t * a₀ * t⁻¹) * t⁻¹⁻¹ = a₀ := by group
    rw [h1] at e
    exact mul_left_cancel (mul_right_cancel e)
  · rw [← orderOf_injective φ (MulAut.conj u).injective σ]
    exact hord _ ((hmem σ).mp hσ)
  · rw [hmem]
    have hc' : t * c * t⁻¹ * (t * a₀ * t⁻¹) = t * a₀ * t⁻¹ * (t * c * t⁻¹) := by
      calc t * c * t⁻¹ * (t * a₀ * t⁻¹) = t * (c * a₀) * t⁻¹ := by group
        _ = t * (a₀ * c) * t⁻¹ := by rw [hc]
        _ = _ := by group
    have := hnorm _ hc' _ ((hmem σ).mp hσ)
    have e : u * (MulAut.conj c * σ * (MulAut.conj c)⁻¹) * u⁻¹ =
        MulAut.conj (t * c * t⁻¹) * (u * σ * u⁻¹) * (MulAut.conj (t * c * t⁻¹))⁻¹ := by
      simp only [map_mul, map_inv, u]; group
    rw [e]; exact this

theorem centAlphaS_of_reps [Finite S] {a b r₁ r₂ w : S} (D : NormData a b r₁ r₂ w) {n : ℕ}
    (ha : QA S (R a b) n a) (hab : QA S (R a b) n (a * b)) : CentAlphaS S (R a b) n := by
  have E := D.toE9Data
  have hr₂ : r₂ ∈ Subgroup.normalizer (R a b : Set S) := by simpa [jk] using D.jk_mem 2
  have hw : w ∈ Subgroup.normalizer (R a b : Set S) := by simpa [jk] using D.jk_mem 4
  have ha2 : a ^ 2 = a⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, E.a3]
  have hb2 : b ^ 2 = b⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← pow_succ, E.b3]
  have hcm : Commute a b := E.comm
  have hwa : w * a * w⁻¹ = b := by simpa [MulAut.conj_apply] using conj_eq_of D.wa
  have hra : r₂ * a * r₂⁻¹ = a := by simpa [MulAut.conj_apply] using conj_eq_of D.r₂a
  have hrb : r₂ * b * r₂⁻¹ = b ^ 2 := by simpa [MulAut.conj_apply] using conj_eq_of D.r₂b
  have hb : QA S (R a b) n b := hwa ▸ ha.conj hw
  have hab2 : QA S (R a b) n (a * b ^ 2) := by
    have := hab.conj hr₂
    have e : r₂ * (a * b) * r₂⁻¹ = a * b ^ 2 := by
      calc r₂ * (a * b) * r₂⁻¹ = (r₂ * a * r₂⁻¹) * (r₂ * b * r₂⁻¹) := by group
        _ = a * b ^ 2 := by rw [hra, hrb]
    rwa [e] at this
  have h22 : a ^ 2 * b ^ 2 = (a * b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc a ^ 2 * b ^ 2 * (a * b) = a ^ 2 * (b ^ 2 * a) * b := by group
      _ = a ^ 2 * (a * b ^ 2) * b := by rw [← (hcm.pow_right 2).eq]
      _ = a ^ 3 * b ^ 3 := by group
      _ = 1 := by rw [E.a3, E.b3, one_mul]
  have h21 : a ^ 2 * b = (a * b ^ 2)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc a ^ 2 * b * (a * b ^ 2) = a ^ 2 * (b * a) * b ^ 2 := by group
      _ = a ^ 2 * (a * b) * b ^ 2 := by rw [← hcm.eq]
      _ = a ^ 3 * b ^ 3 := by group
      _ = 1 := by rw [E.a3, E.b3, one_mul]
  have key : ∀ i j : ℕ, i < 3 → j < 3 → (i ≠ 0 ∨ j ≠ 0) → QA S (R a b) n (a ^ i * b ^ j) := by
    intro i j hi hj hne
    interval_cases i <;> interval_cases j
    · simp at hne
    · simpa using hb
    · simpa [hb2] using hb.inv
    · simpa using ha
    · simpa using hab
    · simpa using hab2
    · simpa [ha2] using ha.inv
    · rw [pow_one, h21]; exact hab2.inv
    · rw [h22]; exact hab.inv
  refine centAlphaS_iff.mpr fun x hx hx1 => ?_
  obtain ⟨i, j, rfl⟩ := E.mem_R_iff.mp hx
  refine key i j i.2 j.2 ?_
  by_contra hcon
  push Not at hcon
  rw [hcon.1, hcon.2] at hx1
  simp at hx1

end CFSG.RankThree.PartTwo.Sec21.FF79.TLn
