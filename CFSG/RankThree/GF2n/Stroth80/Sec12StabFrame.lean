module

public import CFSG.RankThree.GF2n.Stroth80.QuadIso

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {γ : G → K}

theorem card_le_two_mul_of_fixing_frame (M₀ : Tim79.QuadModel QF V K γ)
    (P : Subgroup (M₀.E ≃ₗ[K] M₀.E)) (w v a b' : M₀.E) (R Y : Submodule K M₀.E)
    (hY : Y = Submodule.span K {w, v, a, b'}) (hYR : Y ⊔ R = ⊤)
    (hwa : M₀.B w a = 1) (hvb : M₀.B v b' = 1) (hwv : M₀.B w v = 0) (hwb : M₀.B w b' = 0)
    (hav : M₀.B a v = 0) (hab : M₀.B a b' = 0) (hQv : M₀.Qf v = 0) (hQw : M₀.Qf w ≠ 0)
    (hiso : ∀ T ∈ P, ∀ e, M₀.Qf (T e) = M₀.Qf e) (hfw : ∀ T ∈ P, T w = w)
    (hfv : ∀ T ∈ P, T v = v) (hfR : ∀ T ∈ P, ∀ y ∈ R, T y = y)
    (hYst : ∀ T ∈ P, ∀ y ∈ Y, T y ∈ Y) :
    Nat.card P ≤ 2 * Nat.card K := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsymm : ∀ e f : M₀.E, M₀.B e f = M₀.B f e := fun e f => by
    rw [Tim79.QuadModel.B_comm e f, CharTwo.neg_eq]
  have gww : M₀.B w w = 0 := M₀.alt w
  have gaa : M₀.B a a = 0 := M₀.alt a
  have gvv : M₀.B v v = 0 := M₀.alt v
  have gbb : M₀.B b' b' = 0 := M₀.alt b'
  have gaw : M₀.B a w = 1 := (hsymm a w).trans hwa
  have gbv : M₀.B b' v = 1 := (hsymm b' v).trans hvb
  have gvw : M₀.B v w = 0 := (hsymm v w).trans hwv
  have gbw : M₀.B b' w = 0 := (hsymm b' w).trans hwb
  have gva : M₀.B v a = 0 := (hsymm v a).trans hav
  have gba : M₀.B b' a = 0 := (hsymm b' a).trans hab
  have hcoef : ∀ α β t δ : K,
      M₀.B (α • w + β • a + t • v + δ • b') w = β ∧
      M₀.B (α • w + β • a + t • v + δ • b') v = δ ∧
      M₀.B (α • w + β • a + t • v + δ • b') a = α ∧
      M₀.B (α • w + β • a + t • v + δ • b') b' = t := by
    intro α β t δ
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        gww, gaa, gvv, gbb, gaw, gbv, gvw, gbw, gva, gba, hwa, hvb, hwv, hwb, hav, hab,
        mul_zero, mul_one, zero_add, add_zero] <;> ring
  have hQcomb : ∀ α β t δ : K,
      M₀.Qf (α • w + β • a + t • v + δ • b') = α ^ 2 * M₀.Qf w + β ^ 2 * M₀.Qf a +
        t ^ 2 * M₀.Qf v + δ ^ 2 * M₀.Qf b' + α * β + t * δ := by
    intro α β t δ
    simp only [M₀.Qf_add, M₀.Qf_smul, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hwa, hwv, hwb, hav, hab, hvb, mul_zero, mul_one,
      zero_mul, add_zero, zero_add] <;> ring
  have hdecY : ∀ y ∈ Y, ∃ α β t δ : K, y = α • w + β • a + t • v + δ • b' := by
    intro y hy
    rw [hY] at hy
    obtain ⟨α, z₁, hz₁, rfl⟩ := Submodule.mem_span_insert.mp hy
    obtain ⟨t, z₂, hz₂, rfl⟩ := Submodule.mem_span_insert.mp hz₁
    obtain ⟨β, δ, rfl⟩ := Submodule.mem_span_pair.mp hz₂
    exact ⟨α, β, t, δ, by abel⟩
  have haY : a ∈ Y := by
    rw [hY]
    exact Submodule.subset_span (by simp)
  have hbY : b' ∈ Y := by
    rw [hY]
    exact Submodule.subset_span (by simp)
  have hBiso : ∀ T ∈ P, ∀ e f : M₀.E, M₀.B (T e) (T f) = M₀.B e f := fun T hT e f =>
    Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hiso T hT) e f
  have hdich_eq : ∀ x y : K, (x = 0 ∨ x = (M₀.Qf w)⁻¹) → (y = 0 ∨ y = (M₀.Qf w)⁻¹) →
      (x = 0 ↔ y = 0) → x = y := by
    have hinv : (M₀.Qf w)⁻¹ ≠ 0 := inv_ne_zero hQw
    rintro x y (rfl | rfl) (rfl | rfl) h
    · rfl
    · exact absurd (h.mp rfl) hinv
    · exact absurd (h.mpr rfl) hinv
    · rfl
  have hT_form : ∀ T ∈ P, ∃ α t : K, (α = 0 ∨ α = (M₀.Qf w)⁻¹) ∧
      T a = α • w + a + t • v ∧ T b' = t • w + b' + (t ^ 2 * M₀.Qf w) • v ∧
      M₀.B (T a) a = α ∧ M₀.B (T a) b' = t := by
    intro T hT
    obtain ⟨α, β, t, δ, hTa⟩ := hdecY (T a) (hYst T hT a haY)
    obtain ⟨p, q, r, s, hTb⟩ := hdecY (T b') (hYst T hT b' hbY)
    have e1 : M₀.B (T a) w = 1 := by
      have h := hBiso T hT a w
      rw [hfw T hT] at h
      rw [h]
      exact gaw
    have e2 : M₀.B (T a) v = 0 := by
      have h := hBiso T hT a v
      rw [hfv T hT] at h
      rw [h]
      exact hav
    have e3 : M₀.B (T b') w = 0 := by
      have h := hBiso T hT b' w
      rw [hfw T hT] at h
      rw [h]
      exact gbw
    have e4 : M₀.B (T b') v = 1 := by
      have h := hBiso T hT b' v
      rw [hfv T hT] at h
      rw [h]
      exact gbv
    have e5 : M₀.B (T a) (T b') = 0 := by
      rw [hBiso T hT]
      exact hab
    have e6 : M₀.Qf (T a) = M₀.Qf a := hiso T hT a
    have e7 : M₀.Qf (T b') = M₀.Qf b' := hiso T hT b'
    have hβ : β = 1 := by
      have h := (hcoef α β t δ).1
      rw [← hTa] at h
      exact h.symm.trans e1
    have hδ : δ = 0 := by
      have h := (hcoef α β t δ).2.1
      rw [← hTa] at h
      exact h.symm.trans e2
    have hq : q = 0 := by
      have h := (hcoef p q r s).1
      rw [← hTb] at h
      exact h.symm.trans e3
    have hs : s = 1 := by
      have h := (hcoef p q r s).2.1
      rw [← hTb] at h
      exact h.symm.trans e4
    have hBTa : M₀.B (T a) a = α := by
      rw [hTa]
      exact (hcoef α β t δ).2.2.1
    have hBTb : M₀.B (T a) b' = t := by
      rw [hTa]
      exact (hcoef α β t δ).2.2.2
    have hα0 : α * (α * M₀.Qf w + 1) = 0 := by
      have h := e6
      rw [hTa, hQcomb, hβ, hδ, hQv] at h
      linear_combination h
    have hαdich : α = 0 ∨ α = (M₀.Qf w)⁻¹ := by
      rcases mul_eq_zero.mp hα0 with h | h
      · exact Or.inl h
      · refine Or.inr (eq_inv_of_mul_eq_one_left ?_)
        linear_combination h - h2
    have e5' : α * q + β * p + t * s + δ * r = 0 := by
      have h := e5
      rw [hTa, hTb] at h
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        gww, gaa, gvv, gbb, gaw, gbv, gvw, gbw, gva, gba, hwa, hvb, hwv, hwb, hav, hab] at h
      linear_combination h
    have hpt : p = t := by
      rw [hβ, hδ, hq, hs] at e5'
      linear_combination e5' - t * h2
    have hr : r = p ^ 2 * M₀.Qf w := by
      have h := e7
      rw [hTb, hQcomb, hq, hs, hQv] at h
      linear_combination h - (p ^ 2 * M₀.Qf w) * h2
    refine ⟨α, t, hαdich, ?_, ?_, hBTa, hBTb⟩
    · simp only [hTa, hβ, hδ, one_smul, zero_smul, add_zero]
    · simp only [hTb, hq, hs, hr, hpt, zero_smul, one_smul, add_zero, zero_add]
      abel
  have hinj : Function.Injective
      (fun T : P => (decide (M₀.B (T.1 a) a = 0), M₀.B (T.1 a) b')) := by
    intro T₁ T₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hdec, hb⟩ := h
    have hdec' := decide_eq_decide.mp hdec
    obtain ⟨α₁, t₁, hα₁, hTa₁, hTb₁, hBa₁, hBb₁⟩ := hT_form T₁.1 T₁.2
    obtain ⟨α₂, t₂, hα₂, hTa₂, hTb₂, hBa₂, hBb₂⟩ := hT_form T₂.1 T₂.2
    rw [hBa₁, hBa₂] at hdec'
    rw [hBb₁, hBb₂] at hb
    have hαe : α₁ = α₂ := hdich_eq α₁ α₂ hα₁ hα₂ hdec'
    have hte : t₁ = t₂ := hb
    have hTa : T₁.1 a = T₂.1 a := by rw [hTa₁, hTa₂, hαe, hte]
    have hTb : T₁.1 b' = T₂.1 b' := by rw [hTb₁, hTb₂, hte]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    have hz : z ∈ Y ⊔ R := by
      rw [hYR]
      exact Submodule.mem_top
    obtain ⟨y, hy, r, hr, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, map_add, hfR T₁.1 T₁.2 r hr, hfR T₂.1 T₂.2 r hr]
    congr 1
    obtain ⟨σ, β, τ, δ, rfl⟩ := hdecY y hy
    simp only [map_add, map_smul, hTa, hTb, hfw T₁.1 T₁.2, hfw T₂.1 T₂.2, hfv T₁.1 T₁.2,
      hfv T₂.1 T₂.2]
  calc Nat.card P ≤ Nat.card (Bool × K) := Nat.card_le_card_of_injective _ hinj
    _ = 2 * Nat.card K := by
      have hB : Nat.card Bool = 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_bool]
      rw [Nat.card_prod, hB]

end CFSG.RankThree.GF2n.Stroth80
