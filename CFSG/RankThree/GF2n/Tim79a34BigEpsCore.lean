module

public import CFSG.RankThree.GF2n.Tim79a34BigEpsCentralizer
public import CFSG.RankThree.GF2n.Tim79a34SpSchurMod

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section BigEpsExtra

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}

structure BigEpsExtra (φ : (Fin n ⊕ Fin n → F) → G) (a : Fin n ⊕ Fin n → F)
    (M P Q B V : Subgroup G) : Prop where
  VP : V ≤ P
  Vcent : ∀ v ∈ V, ∀ p ∈ P, v * p = p * v
  AV : ∀ l : F, φ (l • a) ∈ V
  VW : ∀ β, φ β ∈ V → ∃ l : F, β = l • a
  normV : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V
  Vact : ∀ c : F, ∃ v ∈ V, BigEpsParam φ a v 0 c
  kerP : ∀ p ∈ P, (∀ β, p * φ β * p⁻¹ = φ β) → ∃ x, spForm a x = 0 ∧ p = φ x
  Pall : ∀ u, spForm a u = 0 → ∀ c : F, ∃ p ∈ P, BigEpsParam φ a p u c
  three : ∀ d : F, ∃ s : F, s ≠ 0 ∧ s ≠ d

end BigEpsExtra

section BigEpsPartm5

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F}

theorem bigEpsParam_mul {u u' : Fin n ⊕ Fin n → F} {c c' : F} {p p' : G}
    (hu : spForm a u = 0) (hu' : spForm a u' = 0)
    (hp : BigEpsParam φ a p u c) (hp' : BigEpsParam φ a p' u' c') :
    BigEpsParam φ a (p * p') (u + u') (c + c' + spForm u u') := by
  have hua : spForm u a = 0 := spForm_eq_zero_comm hu
  intro β
  have e : p * p' * φ β * (p * p')⁻¹ = p * (p' * φ β * p'⁻¹) * p⁻¹ := by group
  rw [e, hp' β, hp _]
  congr 1
  simp only [spForm_add_left, spForm_add_right, spForm_smul_left', spForm_smul_right',
    spForm_self, hu, hu', hua, mul_zero, zero_mul, add_zero, zero_add]
  module

theorem bigEpsParam_one : BigEpsParam φ a (1 : G) 0 0 := by
  intro β
  simp only [one_mul, inv_one, mul_one, smul_zero, spForm_zero_left, zero_smul, zero_mul,
    add_zero]

theorem bigEpsParam_inv [CharP F 2] {u : Fin n ⊕ Fin n → F} {c : F} {p : G}
    (hu : spForm a u = 0) (hp : BigEpsParam φ a p u c) : BigEpsParam φ a p⁻¹ u c := by
  have hk : ∀ k : F, k + k = 0 := fun k => CharTwo.add_self_eq_zero k
  have hX : ∀ (k : F) (v : Fin n ⊕ Fin n → F), k • v + k • v = 0 := fun k v => by
    rw [← add_smul, hk k, zero_smul]
  have hua : spForm u a = 0 := spForm_eq_zero_comm hu
  intro β
  have hρρ : (β + spForm a β • u + spForm u β • a + (c * spForm a β) • a) +
      spForm a (β + spForm a β • u + spForm u β • a + (c * spForm a β) • a) • u +
      spForm u (β + spForm a β • u + spForm u β • a + (c * spForm a β) • a) • a +
      (c * spForm a (β + spForm a β • u + spForm u β • a + (c * spForm a β) • a)) • a = β := by
    simp only [spForm_add_right, spForm_smul_right', spForm_self, hu, hua, mul_zero, zero_mul,
      add_zero, zero_add]
    linear_combination (norm := module) hX (spForm a β) u + hX (spForm u β) a +
      hX (c * spForm a β) a
  have h1 := hp (β + spForm a β • u + spForm u β • a + (c * spForm a β) • a)
  rw [hρρ] at h1
  rw [inv_inv, ← h1]
  group

theorem bigEpsParam_smul_a [CharP F 2] {l c : F} {p : G} {u : Fin n ⊕ Fin n → F}
    (hu : u = l • a) : BigEpsParam φ a p u c ↔ BigEpsParam φ a p 0 c := by
  have hk : ∀ k : F, k + k = 0 := fun k => CharTwo.add_self_eq_zero k
  subst hu
  have hz : ∀ β : Fin n ⊕ Fin n → F, spForm a β • (l • a) + (l * spForm a β) • a = 0 := by
    intro β
    rw [smul_smul, ← add_smul, mul_comm (spForm a β) l, hk, zero_smul]
  have key : ∀ β : Fin n ⊕ Fin n → F,
      β + spForm a β • (l • a) + spForm (l • a) β • a + (c * spForm a β) • a =
        β + spForm a β • (0 : Fin n ⊕ Fin n → F) + spForm 0 β • a + (c * spForm a β) • a := by
    intro β
    rw [spForm_smul_left', spForm_zero_left]
    linear_combination (norm := module) hz β
  unfold BigEpsParam
  simp only [key]

theorem spForm_perp_add_smul {c₁ u : Fin n ⊕ Fin n → F} (μ : F) (hc₁ : spForm a c₁ = 0)
    (hu : spForm a u = 0) : spForm a (u + (μ * spForm c₁ u) • c₁) = 0 := by
  rw [spForm_add_right, spForm_smul_right', hu, hc₁, mul_zero, add_zero]

theorem bigEpsParam_conj [CharP F 2] {c₁ u : Fin n ⊕ Fin n → F} {μ c : F} {r p : G}
    (hc₁ : spForm a c₁ = 0) (hu : spForm a u = 0)
    (hr : ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c₁ y) • c₁))
    (hp : BigEpsParam φ a p u c) :
    BigEpsParam φ a (r * p * r⁻¹) (u + (μ * spForm c₁ u) • c₁) c := by
  have hk : ∀ k : F, k + k = 0 := fun k => CharTwo.add_self_eq_zero k
  have hca : spForm c₁ a = 0 := spForm_eq_zero_comm hc₁
  have hcu : spForm u c₁ = spForm c₁ u := by
    rw [spForm_comm, CharTwo.neg_eq]
  have hgg : ∀ x : Fin n ⊕ Fin n → F,
      (x + (μ * spForm c₁ x) • c₁) + (μ * spForm c₁ (x + (μ * spForm c₁ x) • c₁)) • c₁ = x := by
    intro x
    rw [spForm_add_right, spForm_smul_right', spForm_self, mul_zero, add_zero, add_assoc,
      ← add_smul, hk (μ * spForm c₁ x), zero_smul, add_zero]
  have hconj : ∀ x : Fin n ⊕ Fin n → F,
      r⁻¹ * φ x * r = φ (x + (μ * spForm c₁ x) • c₁) := by
    intro x
    have h1 := hr (x + (μ * spForm c₁ x) • c₁)
    rw [hgg x] at h1
    calc r⁻¹ * φ x * r = r⁻¹ * (r * φ (x + (μ * spForm c₁ x) • c₁) * r⁻¹) * r := by rw [h1]
      _ = φ (x + (μ * spForm c₁ x) • c₁) := by group
  intro β
  have hcancel : (μ * spForm c₁ β) • c₁ + (μ * spForm c₁ β) • c₁ = 0 := by
    rw [← add_smul, hk, zero_smul]
  have e : r * p * r⁻¹ * φ β * (r * p * r⁻¹)⁻¹ = r * (p * (r⁻¹ * φ β * r) * p⁻¹) * r⁻¹ := by
    group
  rw [e, hconj β, hp _, hr _]
  congr 1
  simp only [spForm_add_left, spForm_add_right, spForm_smul_left', spForm_smul_right',
    spForm_self, hc₁, hca, hcu, mul_zero, zero_mul, add_zero, zero_add]
  linear_combination (norm := module) hcancel

theorem bigEpsParam_comm_root [CharP F 2] {c₁ u : Fin n ⊕ Fin n → F} {μ c : F} {r p : G}
    (hc₁ : spForm a c₁ = 0) (hu : spForm a u = 0)
    (hr : ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c₁ y) • c₁))
    (hp : BigEpsParam φ a p u c) :
    BigEpsParam φ a (r * p * r⁻¹ * p⁻¹) ((μ * spForm c₁ u) • c₁)
      (μ * (spForm c₁ u * spForm c₁ u)) := by
  have hk : ∀ k : F, k + k = 0 := fun k => CharTwo.add_self_eq_zero k
  have hvv : ∀ v : Fin n ⊕ Fin n → F, v + v = 0 := fun v => by
    rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]
  have h := bigEpsParam_mul (spForm_perp_add_smul μ hc₁ hu) hu
    (bigEpsParam_conj hc₁ hu hr hp) (bigEpsParam_inv hu hp)
  have e1 : u + (μ * spForm c₁ u) • c₁ + u = (μ * spForm c₁ u) • c₁ := by
    rw [add_right_comm, hvv u, zero_add]
  have e2 : c + c + spForm (u + (μ * spForm c₁ u) • c₁) u =
      μ * (spForm c₁ u * spForm c₁ u) := by
    rw [spForm_add_left, spForm_smul_left', spForm_self, hk c]
    ring
  rw [e1, e2] at h
  exact h

end BigEpsPartm5

section BigEpsTwoA

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B V : Subgroup G}

@[expose] def BigEpsInA (φ : (Fin n ⊕ Fin n → F) → G) (a : Fin n ⊕ Fin n → F) (x : G) : Prop :=
  ∃ l : F, x = φ (l • a)

theorem BigEpsInA.mul (h : BigEpsCfg φ a M P Q B) {x y : G} (hx : BigEpsInA φ a x)
    (hy : BigEpsInA φ a y) : BigEpsInA φ a (x * y) := by
  obtain ⟨l, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hy
  exact ⟨l + m, by rw [add_smul, h.add]⟩

theorem BigEpsInA.one (h : BigEpsCfg φ a M P Q B) : BigEpsInA φ a (1 : G) :=
  ⟨0, by rw [zero_smul, h.zero]⟩

theorem BigEpsInA.mem_V (hx : BigEpsExtra φ a M P Q B V) {x : G} (hA : BigEpsInA φ a x) :
    x ∈ V := by
  obtain ⟨l, rfl⟩ := hA
  exact hx.AV l

theorem bigEps_comm_mul (x y z : G) : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem BigEpsCfg.comm_root_inA (h : BigEpsCfg φ a M P Q B)
    (hx : BigEpsExtra φ a M P Q B V) {t r : G} (hrM : r ∈ M) (htr : ⁅t, r⁆ ∈ Q)
    (hrV : ∀ v ∈ V, r * v * r⁻¹ = v) (hV : ∀ p ∈ P, ⁅t, p⁆ ∈ V) {p : G} (hp : p ∈ P) :
    BigEpsInA φ a ⁅t, r * p * r⁻¹ * p⁻¹⁆ := by
  have hyP : r * p * r⁻¹ ∈ P := h.normP r hrM p hp
  have hvV : ⁅t, p⁆ ∈ V := hV p hp
  have hwV : ⁅t, p⁻¹⁆ ∈ V := hV p⁻¹ (P.inv_mem hp)
  obtain ⟨l₁, hl₁⟩ := h.comm_Q ⁅t, r⁆ htr ⁅t, p⁆ (hx.VP hvV)
  obtain ⟨l₂, hl₂⟩ := h.comm_Q ⁅t, r⁆ htr (r * p * r⁻¹) hyP
  have hs : t * r * t⁻¹ = ⁅t, r⁆ * r := by
    simp only [commutatorElement_def]
    group
  have hvp : t * p * t⁻¹ = ⁅t, p⁆ * p := by
    simp only [commutatorElement_def]
    group
  have hrv : r * ⁅t, p⁆ * r⁻¹ = ⁅t, p⁆ := hrV _ hvV
  have hty : ⁅t, r * p * r⁻¹⁆ = ⁅⁅t, r⁆, ⁅t, p⁆⁆ * ⁅t, p⁆ * ⁅⁅t, r⁆, r * p * r⁻¹⁆ := by
    have h1 : t * (r * p * r⁻¹) * t⁻¹ =
        ⁅t, r⁆ * (r * ⁅t, p⁆ * r⁻¹) * (r * p * r⁻¹) * ⁅t, r⁆⁻¹ := by
      have e : t * (r * p * r⁻¹) * t⁻¹ =
          (t * r * t⁻¹) * (t * p * t⁻¹) * (t * r * t⁻¹)⁻¹ := by group
      rw [e, hs, hvp]
      group
    rw [hrv] at h1
    simp only [commutatorElement_def] at h1 ⊢
    rw [h1]
    group
  have hinv : ⁅t, p⁻¹⁆ = (⁅t, p⁆)⁻¹ := by
    have e : ⁅t, p⁻¹⁆ = p⁻¹ * (⁅t, p⁆)⁻¹ * p := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hc := hx.Vcent _ (V.inv_mem hvV) p hp
    rw [mul_assoc, hc]
    group
  have hcen : (r * p * r⁻¹) * (⁅t, p⁆)⁻¹ * (r * p * r⁻¹)⁻¹ = (⁅t, p⁆)⁻¹ := by
    have hc := hx.Vcent _ (V.inv_mem hvV) _ hyP
    rw [← hc]
    group
  have hAv : BigEpsInA φ a ⁅⁅t, r⁆, ⁅t, p⁆⁆ := ⟨l₁, hl₁⟩
  have hAy : BigEpsInA φ a ⁅⁅t, r⁆, r * p * r⁻¹⁆ := ⟨l₂, hl₂⟩
  have hcomm : ⁅t, p⁆ * ⁅⁅t, r⁆, r * p * r⁻¹⁆ = ⁅⁅t, r⁆, r * p * r⁻¹⁆ * ⁅t, p⁆ :=
    hx.Vcent _ hvV _ (hx.VP (BigEpsInA.mem_V hx hAy))
  have hfinal : ⁅t, r * p * r⁻¹ * p⁻¹⁆ = ⁅⁅t, r⁆, ⁅t, p⁆⁆ * ⁅⁅t, r⁆, r * p * r⁻¹⁆ := by
    rw [bigEps_comm_mul t (r * p * r⁻¹) p⁻¹, hty, hinv, hcen]
    calc ⁅⁅t, r⁆, ⁅t, p⁆⁆ * ⁅t, p⁆ * ⁅⁅t, r⁆, r * p * r⁻¹⁆ * (⁅t, p⁆)⁻¹
        = ⁅⁅t, r⁆, ⁅t, p⁆⁆ * (⁅t, p⁆ * ⁅⁅t, r⁆, r * p * r⁻¹⁆) * (⁅t, p⁆)⁻¹ := by group
      _ = ⁅⁅t, r⁆, ⁅t, p⁆⁆ * (⁅⁅t, r⁆, r * p * r⁻¹⁆ * ⁅t, p⁆) * (⁅t, p⁆)⁻¹ := by rw [hcomm]
      _ = ⁅⁅t, r⁆, ⁅t, p⁆⁆ * ⁅⁅t, r⁆, r * p * r⁻¹⁆ := by group
  rw [hfinal]
  exact BigEpsInA.mul h hAv hAy

end BigEpsTwoA

section BigEpsTwoB

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B V : Subgroup G}

theorem BigEpsCfg.good_mul (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t s₁ s₂ : G} (hs₁ : s₁ ∈ P) (hA₁ : BigEpsInA φ a ⁅t, s₁⁆) (hA₂ : BigEpsInA φ a ⁅t, s₂⁆) :
    BigEpsInA φ a ⁅t, s₁ * s₂⁆ := by
  have hc : ⁅t, s₂⁆ * s₁ = s₁ * ⁅t, s₂⁆ := hx.Vcent _ (BigEpsInA.mem_V hx hA₂) s₁ hs₁
  rw [bigEps_comm_mul]
  have e : s₁ * ⁅t, s₂⁆ * s₁⁻¹ = ⁅t, s₂⁆ := by
    rw [← hc]
    group
  rw [e]
  exact BigEpsInA.mul h hA₁ hA₂

theorem BigEpsCfg.exists_good_param₁ (h : BigEpsCfg φ a M P Q B)
    (hx : BigEpsExtra φ a M P Q B V) {t : G}
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    (hV : ∀ p ∈ P, ⁅t, p⁆ ∈ V) {c₁ : Fin n ⊕ Fin n → F} (hc₁ : spForm a c₁ = 0)
    (hca : ∀ l : F, c₁ ≠ l • a) {β : F} (hβ : β ≠ 0) :
    ∃ s ∈ P, BigEpsInA φ a ⁅t, s⁆ ∧ BigEpsParam φ a s c₁ β := by
  obtain ⟨u₀, hu₀a, hu₀⟩ := exists_dual h.ha hc₁ hca
  have hu'a : spForm a (β • u₀) = 0 := by
    rw [spForm_smul_right', hu₀a, mul_zero]
  have hu' : spForm c₁ (β • u₀) = β := by
    rw [spForm_smul_right', hu₀, mul_one]
  obtain ⟨p', hp'P, hp'⟩ := hx.Pall (β • u₀) hu'a 0
  obtain ⟨r, hrM, hrQ, hrV, hr⟩ := hroot c₁ β⁻¹ hc₁ hca (inv_ne_zero hβ)
  refine ⟨r * p' * r⁻¹ * p'⁻¹, ?_, h.comm_root_inA hx hrM hrQ hrV hV hp'P, ?_⟩
  · exact P.mul_mem (h.normP r hrM p' hp'P) (P.inv_mem hp'P)
  · have := bigEpsParam_comm_root (a := a) hc₁ hu'a hr hp'
    rw [hu', inv_mul_cancel₀ hβ, one_smul, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul] at this
    exact this

theorem BigEpsCfg.exists_good_param₂ (h : BigEpsCfg φ a M P Q B)
    (hx : BigEpsExtra φ a M P Q B V) {t : G}
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    (hV : ∀ p ∈ P, ⁅t, p⁆ ∈ V) (d : F) :
    ∃ z ∈ P, BigEpsInA φ a ⁅t, z⁆ ∧ BigEpsParam φ a z 0 d := by
  by_cases hd : d = 0
  · subst hd
    exact ⟨1, P.one_mem, by rw [commutatorElement_one_right]; exact BigEpsInA.one h,
      bigEpsParam_one⟩
  obtain ⟨c₁, -, hc₁a, hc₁F⟩ := exists_perp_vec_not_smul h.hn h.ha
  obtain ⟨β, hβ0, hβd⟩ := hx.three d
  have hβ2 : β + d ≠ 0 := by
    intro h0
    apply hβd
    have h1 : β = -d := eq_neg_of_add_eq_zero_left h0
    rw [h1, CharTwo.neg_eq]
  obtain ⟨s₁, hs₁P, hs₁A, hs₁⟩ := h.exists_good_param₁ hx hroot hV hc₁a hc₁F hβ0
  obtain ⟨s₂, hs₂P, hs₂A, hs₂⟩ := h.exists_good_param₁ hx hroot hV hc₁a hc₁F hβ2
  refine ⟨s₁ * s₂, P.mul_mem hs₁P hs₂P, h.good_mul hx hs₁P hs₁A hs₂A, ?_⟩
  have hmul := bigEpsParam_mul (a := a) hc₁a hc₁a hs₁ hs₂
  have e1 : c₁ + c₁ = 0 := by
    rw [← two_smul F c₁, CharTwo.two_eq_zero, zero_smul]
  have e2 : β + (β + d) + spForm c₁ c₁ = d := by
    rw [spForm_self, add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [e1, e2] at hmul
  exact hmul

theorem BigEpsCfg.exists_good_param (h : BigEpsCfg φ a M P Q B)
    (hx : BigEpsExtra φ a M P Q B V) {t : G}
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    (hV : ∀ p ∈ P, ⁅t, p⁆ ∈ V) {u : Fin n ⊕ Fin n → F} (hu : spForm a u = 0) (c : F) :
    ∃ s ∈ P, BigEpsInA φ a ⁅t, s⁆ ∧ BigEpsParam φ a s u c := by
  by_cases hua : ∀ l : F, u ≠ l • a
  · obtain ⟨s₁, hs₁P, hs₁A, hs₁⟩ := h.exists_good_param₁ hx hroot hV hu hua one_ne_zero
    obtain ⟨z, hzP, hzA, hz⟩ := h.exists_good_param₂ hx hroot hV (c + 1)
    refine ⟨s₁ * z, P.mul_mem hs₁P hzP, h.good_mul hx hs₁P hs₁A hzA, ?_⟩
    have hmul := bigEpsParam_mul (a := a) hu (spForm_zero_right a) hs₁ hz
    have e1 : 1 + (c + 1) + spForm u 0 = c := by
      rw [spForm_zero_right, add_zero, add_comm c 1, ← add_assoc, CharTwo.add_self_eq_zero,
        zero_add]
    rw [add_zero, e1] at hmul
    exact hmul
  · push Not at hua
    obtain ⟨l, hl⟩ := hua
    obtain ⟨z, hzP, hzA, hz⟩ := h.exists_good_param₂ hx hroot hV c
    exact ⟨z, hzP, hzA, (bigEpsParam_smul_a hl).mpr hz⟩

theorem BigEpsCfg.comm_inA (h : BigEpsCfg φ a M P Q B)
    (hx : BigEpsExtra φ a M P Q B V) {t : G}
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    (hFA : ∀ x, spForm a x = 0 → BigEpsInA φ a ⁅t, φ x⁆)
    (hV : ∀ p ∈ P, ⁅t, p⁆ ∈ V) : ∀ p ∈ P, BigEpsInA φ a ⁅t, p⁆ := by
  intro p hp
  obtain ⟨u, c, hu, hpar⟩ := h.act p hp
  obtain ⟨s, hsP, hsA, hspar⟩ := h.exists_good_param hx hroot hV hu c
  have hinv := bigEpsParam_inv hu hspar
  have hmul := bigEpsParam_mul (a := a) hu hu hpar hinv
  have e1 : u + u = 0 := by
    rw [← two_smul F u, CharTwo.two_eq_zero, zero_smul]
  have e2 : c + c + spForm u u = 0 := by
    rw [spForm_self, add_zero, CharTwo.add_self_eq_zero]
  rw [e1, e2] at hmul
  have htriv : ∀ β, p * s⁻¹ * φ β * (p * s⁻¹)⁻¹ = φ β := by
    intro β
    rw [hmul β]
    congr 1
    simp [spForm_zero_left]
  obtain ⟨x, hxa, hx'⟩ := hx.kerP (p * s⁻¹) (P.mul_mem hp (P.inv_mem hsP)) htriv
  have hps : p = φ x * s := by
    rw [← hx']
    group
  have hφxP : φ x ∈ P := (h.mem_P x).mpr hxa
  rw [hps]
  exact h.good_mul hx hφxP (hFA x hxa) hsA

end BigEpsTwoB

section BigEpsTwoC

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B V : Subgroup G}

theorem BigEpsCfg.zero_param_decomp (h : BigEpsCfg φ a M P Q B)
    (hx : BigEpsExtra φ a M P Q B V) {z : G} (hz : z ∈ P) {d : F}
    (hzp : BigEpsParam φ a z 0 d) :
    ∃ x, spForm a x = 0 ∧ ∃ v ∈ V, z = φ x * v := by
  obtain ⟨v, hvV, hvp⟩ := hx.Vact d
  have h0 : spForm a (0 : Fin n ⊕ Fin n → F) = 0 := spForm_zero_right a
  have hinv := bigEpsParam_inv h0 hvp
  have hmul := bigEpsParam_mul h0 h0 hzp hinv
  have e1 : d + d + spForm (0 : Fin n ⊕ Fin n → F) 0 = 0 := by
    rw [spForm_zero_left, add_zero, CharTwo.add_self_eq_zero]
  rw [add_zero, e1] at hmul
  have htriv : ∀ β, z * v⁻¹ * φ β * (z * v⁻¹)⁻¹ = φ β := by
    intro β
    rw [hmul β]
    congr 1
    simp [spForm_zero_left]
  obtain ⟨x, hxa, hxz⟩ := hx.kerP (z * v⁻¹) (P.mul_mem hz (P.inv_mem (hx.VP hvV))) htriv
  exact ⟨x, hxa, v, hvV, by rw [← hxz]; group⟩

@[expose] def BigEpsRel (φ : (Fin n ⊕ Fin n → F) → G) (a : Fin n ⊕ Fin n → F) (V : Subgroup G)
    (t p : G) (y : Fin n ⊕ Fin n → F) : Prop :=
  spForm a y = 0 ∧ ∃ v ∈ V, ⁅t, p⁆ = φ y * v

theorem BigEpsCfg.rel_unique (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t p : G} {y y' : Fin n ⊕ Fin n → F} (hy : BigEpsRel φ a V t p y)
    (hy' : BigEpsRel φ a V t p y') : ∃ l : F, y' = y + l • a := by
  obtain ⟨-, v, hv, e⟩ := hy
  obtain ⟨-, v', hv', e'⟩ := hy'
  have h1 : (φ y')⁻¹ * φ y = v' * v⁻¹ := by
    have : φ y * v = φ y' * v' := e.symm.trans e'
    calc (φ y')⁻¹ * φ y = (φ y')⁻¹ * (φ y * v) * v⁻¹ := by group
      _ = (φ y')⁻¹ * (φ y' * v') * v⁻¹ := by rw [this]
      _ = v' * v⁻¹ := by group
  have h2 : φ (y - y') ∈ V := by
    have e2 : φ (y - y') = (φ y')⁻¹ * φ y := by
      rw [sub_eq_neg_add, h.add, h.neg]
    rw [e2, h1]
    exact V.mul_mem hv' (V.inv_mem hv)
  obtain ⟨l, hl⟩ := hx.VW (y - y') h2
  exact ⟨-l, by rw [neg_smul, ← hl]; abel⟩

theorem BigEpsExtra.comm_four (hx : BigEpsExtra φ a M P Q B V) {g₁ g₂ v₁ v₂ : G}
    (hg₁ : g₁ ∈ P) (hg₂ : g₂ ∈ P) (hv₁ : v₁ ∈ V) (hv₂ : v₂ ∈ V)
    (hg : g₁ * g₂ = g₂ * g₁) :
    (g₁ * v₁) * (g₂ * v₂) = (g₂ * v₂) * (g₁ * v₁) := by
  have h1 : v₁ * g₂ = g₂ * v₁ := hx.Vcent _ hv₁ _ hg₂
  have h2 : v₂ * g₁ = g₁ * v₂ := hx.Vcent _ hv₂ _ hg₁
  have h3 : v₁ * v₂ = v₂ * v₁ := hx.Vcent _ hv₁ _ (hx.VP hv₂)
  calc (g₁ * v₁) * (g₂ * v₂) = g₁ * (v₁ * g₂) * v₂ := by group
    _ = g₁ * (g₂ * v₁) * v₂ := by rw [h1]
    _ = (g₁ * g₂) * (v₁ * v₂) := by group
    _ = (g₂ * g₁) * (v₂ * v₁) := by rw [hg, h3]
    _ = g₂ * (g₁ * v₂) * v₁ := by group
    _ = g₂ * (v₂ * g₁) * v₁ := by rw [h2]
    _ = (g₂ * v₂) * (g₁ * v₁) := by group

theorem BigEpsCfg.param_trivial_u (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    {β₀ : Fin n ⊕ Fin n → F} (hβ₀B : φ β₀ ∈ B) (hβ₀ : spForm a β₀ = 1)
    (hB : ∀ b ∈ B, b⁻¹ * (t * b * t⁻¹) ∈ Q)
    (hc : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {p : G} (hp : p ∈ P) {u u₁ : Fin n ⊕ Fin n → F} {c c₁ : F} (hu : spForm a u = 0)
    (hpar : BigEpsParam φ a p u c) (hpar₁ : BigEpsParam φ a (t * p * t⁻¹) u₁ c₁) :
    ∃ m : F, u₁ = u + m • a := by
  have hk := hB (φ β₀) hβ₀B
  have hkk : t * φ β₀ * t⁻¹ = φ β₀ * ((φ β₀)⁻¹ * (t * φ β₀ * t⁻¹)) := by group
  obtain ⟨m, hm⟩ := h.param_conj_t ht hc hk hkk hp hu hpar hpar₁
  exact ⟨m, by rw [hβ₀, one_smul, one_smul] at hm; exact hm⟩

theorem BigEpsCfg.rel_exists (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V) {t : G}
    (ht : t ∈ M) {β₀ : Fin n ⊕ Fin n → F} (hβ₀B : φ β₀ ∈ B) (hβ₀ : spForm a β₀ = 1)
    (hB : ∀ b ∈ B, b⁻¹ * (t * b * t⁻¹) ∈ Q)
    (hc : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {p : G} (hp : p ∈ P) : ∃ y, BigEpsRel φ a V t p y := by
  obtain ⟨u, c, hu, hpar⟩ := h.act p hp
  have htp : t * p * t⁻¹ ∈ P := h.normP t ht p hp
  obtain ⟨u₁, c₁, hu₁, hpar₁⟩ := h.act _ htp
  obtain ⟨m, hm⟩ := h.param_trivial_u ht hβ₀B hβ₀ hB hc hp hu hpar hpar₁
  have hinv := bigEpsParam_inv hu hpar
  have hmul := bigEpsParam_mul hu₁ hu hpar₁ hinv
  have e1 : u₁ + u = m • a := by
    have h2 : u + u = 0 := by rw [← two_smul F u, CharTwo.two_eq_zero, zero_smul]
    rw [hm]
    calc u + m • a + u = (u + u) + m • a := by abel
      _ = m • a := by rw [h2, zero_add]
  have e2 : c₁ + c + spForm u₁ u = c₁ + c := by
    rw [hm, spForm_add_left, spForm_self, spForm_smul_left', hu]
    simp
  rw [e1, e2] at hmul
  have hz0 := (bigEpsParam_smul_a (a := a) (l := m) (c := c₁ + c) (p := t * p * t⁻¹ * p⁻¹)
    (u := m • a) rfl).mp hmul
  have hzP : t * p * t⁻¹ * p⁻¹ ∈ P := P.mul_mem htp (P.inv_mem hp)
  obtain ⟨x, hxa, v, hv, hzx⟩ := h.zero_param_decomp hx hzP hz0
  exact ⟨x, hxa, v, hv, by rw [commutatorElement_def]; exact hzx⟩

end BigEpsTwoC

section BigEpsTwoD

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B V : Subgroup G}

theorem BigEpsCfg.rel_left_mul (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t : G} (ht : t ∈ M) (hc : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {x : Fin n ⊕ Fin n → F} (hxa : spForm a x = 0) {v₃ : G} (hv₃ : v₃ ∈ V) {g : G}
    {y : Fin n ⊕ Fin n → F} (hg : BigEpsRel φ a V t g y) :
    ∃ l : F, BigEpsRel φ a V t (φ x * v₃ * g) (y + l • a) := by
  obtain ⟨hya, v, hv, e⟩ := hg
  obtain ⟨l₀, hl₀⟩ := hc x hxa
  have hφx : φ x ∈ P := (h.mem_P x).mpr hxa
  have hφy : φ y ∈ P := (h.mem_P y).mpr hya
  have hcxA : ⁅t, φ x⁆ = φ (l₀ • a) := by
    rw [commutatorElement_def, hl₀, h.add, h.commute x (l₀ • a)]
    group
  have hv₃t : ⁅t, v₃⁆ ∈ V := by
    have h1 : t * v₃ * t⁻¹ ∈ V := hx.normV t ht v₃ hv₃
    have e1 : ⁅t, v₃⁆ = (t * v₃ * t⁻¹) * v₃⁻¹ := by
      simp only [commutatorElement_def]
    rw [e1]
    exact V.mul_mem h1 (V.inv_mem hv₃)
  have hz : ⁅t, φ x * v₃⁆ = φ (l₀ • a) * ⁅t, v₃⁆ := by
    rw [bigEps_comm_mul, hcxA]
    congr 1
    have hc2 : ⁅t, v₃⁆ * φ x = φ x * ⁅t, v₃⁆ := hx.Vcent _ hv₃t _ hφx
    rw [← hc2]
    group
  have hconj : (φ x * v₃) * ⁅t, g⁆ * (φ x * v₃)⁻¹ = ⁅t, g⁆ := by
    rw [e]
    have h4 := hx.comm_four hφx hφy hv₃ hv (h.commute x y)
    calc (φ x * v₃) * (φ y * v) * (φ x * v₃)⁻¹
        = ((φ y * v) * (φ x * v₃)) * (φ x * v₃)⁻¹ := by rw [h4]
      _ = φ y * v := by group
  have hres : ⁅t, φ x * v₃ * g⁆ = φ (y + l₀ • a) * (⁅t, v₃⁆ * v) := by
    rw [bigEps_comm_mul, hz, hconj, e]
    have hc3 : ⁅t, v₃⁆ * φ y = φ y * ⁅t, v₃⁆ := hx.Vcent _ hv₃t _ hφy
    calc φ (l₀ • a) * ⁅t, v₃⁆ * (φ y * v) = φ (l₀ • a) * (⁅t, v₃⁆ * φ y) * v := by group
      _ = φ (l₀ • a) * (φ y * ⁅t, v₃⁆) * v := by rw [hc3]
      _ = (φ (l₀ • a) * φ y) * (⁅t, v₃⁆ * v) := by group
      _ = φ (y + l₀ • a) * (⁅t, v₃⁆ * v) := by rw [← h.add, add_comm]
  refine ⟨l₀, ?_, ⁅t, v₃⁆ * v, V.mul_mem hv₃t hv, hres⟩
  rw [spForm_add_right, spForm_smul_right', hya, spForm_self]
  ring

theorem BigEpsCfg.rel_mul (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t p p' : G} (hp : p ∈ P) {u : Fin n ⊕ Fin n → F} {c : F}
    (hpar : BigEpsParam φ a p u c) {y y' : Fin n ⊕ Fin n → F}
    (hy : BigEpsRel φ a V t p y) (hy' : BigEpsRel φ a V t p' y') :
    BigEpsRel φ a V t (p * p') (y + y' + spForm u y' • a) := by
  obtain ⟨hya, v, hv, e⟩ := hy
  obtain ⟨hya', v', hv', e'⟩ := hy'
  have hφy : φ y ∈ P := (h.mem_P y).mpr hya
  have hza : spForm a (y' + spForm u y' • a) = 0 := by
    rw [spForm_add_right, spForm_smul_right', hya', spForm_self]
    ring
  have hφz : φ (y' + spForm u y' • a) ∈ P := (h.mem_P _).mpr hza
  have hpφ : p * φ y' * p⁻¹ = φ (y' + spForm u y' • a) := by
    rw [hpar y', hya']
    congr 1
    simp
  have hpv : p * v' * p⁻¹ = v' := by
    have h5 : v' * p = p * v' := hx.Vcent _ hv' p hp
    rw [← h5]
    group
  have hb : ⁅t, p * p'⁆ = (φ y * v) * (φ (y' + spForm u y' • a) * v') := by
    rw [bigEps_comm_mul, e, e']
    congr 1
    calc p * (φ y' * v') * p⁻¹ = (p * φ y' * p⁻¹) * (p * v' * p⁻¹) := by group
      _ = φ (y' + spForm u y' • a) * v' := by rw [hpφ, hpv]
  refine ⟨?_, v * v', V.mul_mem hv hv', ?_⟩
  · rw [spForm_add_right, spForm_add_right, spForm_smul_right', hya, hya', spForm_self]
    ring
  · rw [hb]
    have hc := hx.Vcent v hv _ hφz
    calc (φ y * v) * (φ (y' + spForm u y' • a) * v')
        = φ y * (v * φ (y' + spForm u y' • a)) * v' := by group
      _ = φ y * (φ (y' + spForm u y' • a) * v) * v' := by rw [hc]
      _ = (φ y * φ (y' + spForm u y' • a)) * (v * v') := by group
      _ = φ (y + y' + spForm u y' • a) * (v * v') := by rw [← h.add, add_assoc]

theorem BigEpsCfg.rel_conj_root (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t r p : G} (hrM : r ∈ M) (htr : ⁅t, r⁆ ∈ Q) (hrV : ∀ v ∈ V, r * v * r⁻¹ = v)
    {c₁ : Fin n ⊕ Fin n → F} {μ : F}
    (hr : ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c₁ y) • c₁)) (hc₁ : spForm a c₁ = 0)
    (hp : p ∈ P) {y : Fin n ⊕ Fin n → F} (hy : BigEpsRel φ a V t p y) :
    ∃ l : F, BigEpsRel φ a V t (r * p * r⁻¹) (y + (μ * spForm c₁ y) • c₁ + l • a) := by
  obtain ⟨hya, v₀, hv₀, e⟩ := hy
  obtain ⟨q, hq⟩ : ∃ q : G, q = ⁅t, r⁆ := ⟨_, rfl⟩
  have hqQ : q ∈ Q := hq ▸ htr
  have hyP : r * p * r⁻¹ ∈ P := h.normP r hrM p hp
  have hgy : spForm a (y + (μ * spForm c₁ y) • c₁) = 0 := spForm_perp_add_smul μ hc₁ hya
  have hφgy : φ (y + (μ * spForm c₁ y) • c₁) ∈ P := (h.mem_P _).mpr hgy
  have hs : t * r * t⁻¹ = q * r := by
    rw [hq]
    simp only [commutatorElement_def]
    group
  have htp : t * p * t⁻¹ = (φ y * v₀) * p := by
    rw [← e]
    simp only [commutatorElement_def]
    group
  have hrv₀ : r * v₀ * r⁻¹ = v₀ := hrV v₀ hv₀
  have h1 : t * (r * p * r⁻¹) * t⁻¹ =
      q * (φ (y + (μ * spForm c₁ y) • c₁) * v₀ * (r * p * r⁻¹)) * q⁻¹ := by
    have e1 : t * (r * p * r⁻¹) * t⁻¹ = (t * r * t⁻¹) * (t * p * t⁻¹) * (t * r * t⁻¹)⁻¹ := by
      group
    rw [e1, hs, htp]
    have e2 : q * r * (φ y * v₀ * p) * (q * r)⁻¹ =
        q * ((r * φ y * r⁻¹) * (r * v₀ * r⁻¹) * (r * p * r⁻¹)) * q⁻¹ := by group
    rw [e2, hr y, hrv₀]
  have h2 : ⁅t, r * p * r⁻¹⁆ =
      (q * φ (y + (μ * spForm c₁ y) • c₁) * q⁻¹) * (q * v₀ * q⁻¹) *
        (q * (r * p * r⁻¹) * q⁻¹ * (r * p * r⁻¹)⁻¹) := by
    rw [commutatorElement_def, h1]
    group
  obtain ⟨l₁, hl₁⟩ := h.comm_Q q hqQ _ hφgy
  obtain ⟨l₂, hl₂⟩ := h.comm_Q q hqQ v₀ (hx.VP hv₀)
  obtain ⟨l₃, hl₃⟩ := h.comm_Q q hqQ _ hyP
  have k1 : q * φ (y + (μ * spForm c₁ y) • c₁) * q⁻¹ =
      φ (l₁ • a) * φ (y + (μ * spForm c₁ y) • c₁) := by
    rw [← hl₁]
    simp only [commutatorElement_def]
    group
  have k2 : q * v₀ * q⁻¹ = φ (l₂ • a) * v₀ := by
    rw [← hl₂]
    simp only [commutatorElement_def]
    group
  have k3 : q * (r * p * r⁻¹) * q⁻¹ * (r * p * r⁻¹)⁻¹ = φ (l₃ • a) := by
    rw [← hl₃]
    simp only [commutatorElement_def]
  rw [k1, k2, k3] at h2
  have hv₀c : v₀ * φ (l₃ • a) = φ (l₃ • a) * v₀ :=
    hx.Vcent _ hv₀ _ (hx.VP (hx.AV l₃))
  have hfin : ⁅t, r * p * r⁻¹⁆ =
      φ (y + (μ * spForm c₁ y) • c₁ + (l₁ + l₂ + l₃) • a) * v₀ := by
    rw [h2]
    have e3 : φ (y + (μ * spForm c₁ y) • c₁ + (l₁ + l₂ + l₃) • a) =
        φ (l₁ • a) * φ (y + (μ * spForm c₁ y) • c₁) * φ (l₂ • a) * φ (l₃ • a) := by
      have e4 : y + (μ * spForm c₁ y) • c₁ + (l₁ + l₂ + l₃) • a =
          (l₁ • a + (y + (μ * spForm c₁ y) • c₁)) + l₂ • a + l₃ • a := by module
      rw [e4, h.add, h.add, h.add]
    rw [e3]
    calc φ (l₁ • a) * φ (y + (μ * spForm c₁ y) • c₁) * (φ (l₂ • a) * v₀) * φ (l₃ • a)
        = φ (l₁ • a) * φ (y + (μ * spForm c₁ y) • c₁) * φ (l₂ • a) * (v₀ * φ (l₃ • a)) := by
          group
      _ = φ (l₁ • a) * φ (y + (μ * spForm c₁ y) • c₁) * φ (l₂ • a) * (φ (l₃ • a) * v₀) := by
          rw [hv₀c]
      _ = _ := by group
  refine ⟨l₁ + l₂ + l₃, ?_, v₀, hv₀, hfin⟩
  rw [spForm_add_right, spForm_smul_right', hgy, spForm_self]
  ring

theorem BigEpsCfg.rel_congr_u (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t : G} (ht : t ∈ M) (hc : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {p p' : G} (hp : p ∈ P) (hp' : p' ∈ P) {u : Fin n ⊕ Fin n → F} {c c' : F}
    (hu : spForm a u = 0) (hpar : BigEpsParam φ a p u c) (hpar' : BigEpsParam φ a p' u c')
    {y y' : Fin n ⊕ Fin n → F} (hy : BigEpsRel φ a V t p y) (hy' : BigEpsRel φ a V t p' y') :
    ∃ l : F, y' = y + l • a := by
  have hinv := bigEpsParam_inv hu hpar
  have hmul := bigEpsParam_mul hu hu hpar' hinv
  have e1 : u + u = 0 := by rw [← two_smul F u, CharTwo.two_eq_zero, zero_smul]
  have e2 : c' + c + spForm u u = c' + c := by rw [spForm_self, add_zero]
  rw [e1, e2] at hmul
  have hz : p' * p⁻¹ ∈ P := P.mul_mem hp' (P.inv_mem hp)
  obtain ⟨x, hxa, v₃, hv₃, hzx⟩ := h.zero_param_decomp hx hz hmul
  have hp'eq : p' = φ x * v₃ * p := by
    rw [← hzx]
    group
  obtain ⟨l, hl⟩ := h.rel_left_mul hx ht hc hxa hv₃ hy
  rw [← hp'eq] at hl
  obtain ⟨l', hl'⟩ := h.rel_unique hx hl hy'
  exact ⟨l + l', by rw [hl', add_assoc, ← add_smul]⟩

end BigEpsTwoD

section BigEpsTwoE

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B V : Subgroup G}

theorem BigEpsCfg.exists_scalar (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V)
    {t : G} (ht : t ∈ M) {β₀ : Fin n ⊕ Fin n → F} (hβ₀B : φ β₀ ∈ B) (hβ₀ : spForm a β₀ = 1)
    (hB : ∀ b ∈ B, b⁻¹ * (t * b * t⁻¹) ∈ Q)
    (hc : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c)) :
    ∃ μ₀ : F, ∀ p ∈ P, ∀ (u : Fin n ⊕ Fin n → F) (c : F) (y : Fin n ⊕ Fin n → F),
      spForm a u = 0 → BigEpsParam φ a p u c → BigEpsRel φ a V t p y →
        ∃ l : F, y = μ₀ • u + l • a := by
  have key : ∀ x : Fin n ⊕ Fin n → F, ∃ (p : G) (y : Fin n ⊕ Fin n → F), spForm a x = 0 →
      (p ∈ P ∧ BigEpsParam φ a p x 0 ∧ BigEpsRel φ a V t p y) := by
    intro x
    by_cases hx0 : spForm a x = 0
    · obtain ⟨p, hpP, hpar⟩ := hx.Pall x hx0 0
      obtain ⟨y, hy⟩ := h.rel_exists hx ht hβ₀B hβ₀ hB hc hpP
      exact ⟨p, y, fun _ => ⟨hpP, hpar, hy⟩⟩
    · exact ⟨1, 0, fun h0 => absurd h0 hx0⟩
  choose lift T hT using key
  have hperp : ∀ x, spForm a x = 0 → spForm a (T x) = 0 := fun x hx0 => (hT x hx0).2.2.1
  have hadd : ∀ x y, spForm a x = 0 → spForm a y = 0 →
      ∃ l : F, T (x + y) = T x + T y + l • a := by
    intro x x' hx0 hx0'
    obtain ⟨hpP, hpar, hrel⟩ := hT x hx0
    obtain ⟨hp'P, hpar', hrel'⟩ := hT x' hx0'
    have hxx' : spForm a (x + x') = 0 := by rw [spForm_add_right, hx0, hx0', add_zero]
    obtain ⟨hp''P, hpar'', hrel''⟩ := hT (x + x') hxx'
    have hrelmul := h.rel_mul hx hpP hpar hrel hrel'
    have hparmul := bigEpsParam_mul (a := a) hx0 hx0' hpar hpar'
    obtain ⟨l, hl⟩ := h.rel_congr_u hx ht hc (P.mul_mem hpP hp'P) hp''P hxx' hparmul hpar''
      hrelmul hrel''
    exact ⟨spForm x (T x') + l, by rw [hl]; module⟩
  have hcomm : ∀ (c y : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      spForm a y = 0 → ∃ l : F, T (y + (μ * spForm c y) • c) =
        T y + (μ * spForm c (T y)) • c + l • a := by
    intro c y μ hc0 hca hy0
    by_cases hμ : μ = 0
    · exact ⟨0, by simp [hμ]⟩
    obtain ⟨r, hrM, htr, hrV, hr⟩ := hroot c μ hc0 hca hμ
    obtain ⟨hpP, hpar, hrel⟩ := hT y hy0
    have hy'0 : spForm a (y + (μ * spForm c y) • c) = 0 := spForm_perp_add_smul μ hc0 hy0
    obtain ⟨hp''P, hpar'', hrel''⟩ := hT _ hy'0
    have hrpr : r * lift y * r⁻¹ ∈ P := h.normP r hrM _ hpP
    have hparc := bigEpsParam_conj (a := a) hc0 hy0 hr hpar
    obtain ⟨l₀, hl₀⟩ := h.rel_conj_root hx hrM htr hrV hr hc0 hpP hrel
    obtain ⟨l₁, hl₁⟩ := h.rel_congr_u hx ht hc hrpr hp''P hy'0 hparc hpar'' hl₀ hrel''
    exact ⟨l₀ + l₁, by rw [hl₁]; module⟩
  obtain ⟨κ, hκ⟩ := sp_perp_schur_mod h.hn h.ha T hadd hperp hcomm
  refine ⟨κ, fun p hp u c y hu hpar hrel => ?_⟩
  obtain ⟨hpP, hpar₀, hrel₀⟩ := hT u hu
  obtain ⟨l, hl⟩ := h.rel_congr_u hx ht hc hpP hp hu hpar₀ hpar hrel₀ hrel
  obtain ⟨l', hl'⟩ := hκ u hu
  exact ⟨l' + l, by rw [hl, hl']; module⟩

end BigEpsTwoE

section BigEpsTwoF

variable {G : Type} [Group G] {F : Type} [Field F] [CharP F 2] {n : ℕ}
  {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B V : Subgroup G}

theorem vec_neg_eq_self (z : Fin n ⊕ Fin n → F) : -z = z := by
  have h2 : z + z = 0 := by rw [← two_smul F z, CharTwo.two_eq_zero, zero_smul]
  exact neg_eq_of_add_eq_zero_right h2

theorem BigEpsCfg.core (h : BigEpsCfg φ a M P Q B) (hx : BigEpsExtra φ a M P Q B V) {t : G}
    (ht : t ∈ M)
    (hKQ : ∀ m ∈ M, (∀ p ∈ P, BigEpsInA φ a ⁅m, p⁆) → m ∈ Q)
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ b ∈ B, ⁅b, r⁆ ∈ Q) ∧
        (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    (hBM : ∀ b ∈ B, b ∈ M)
    (hFB : ∀ β : Fin n ⊕ Fin n → F, ∃ x, spForm a x = 0 ∧ ∃ b ∈ B, φ β = φ x * b)
    (hB : ∀ b ∈ B, b⁻¹ * (t * b * t⁻¹) ∈ Q)
    (hc : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a)) :
    ∃ b ∈ B, b⁻¹ * t ∈ Q := by
  have hBsurj : ∀ s : F, ∃ β : Fin n ⊕ Fin n → F, φ β ∈ B ∧ spForm a β = s := by
    intro s
    obtain ⟨b₁, hb₁⟩ := exists_spForm_eq_one h.ha
    obtain ⟨x, hxa, b, hbB, hxb⟩ := hFB (s • b₁)
    obtain ⟨β, hβ⟩ := h.BW b hbB
    refine ⟨β, by rw [hβ]; exact hbB, ?_⟩
    have h1 : s • b₁ = x + β := h.inj (by rw [hxb, ← hβ, h.add])
    have h2 := congrArg (spForm a) h1
    rw [spForm_smul_right', hb₁, spForm_add_right, hxa, zero_add, mul_one] at h2
    exact h2.symm
  obtain ⟨β₀, hβ₀B, hβ₀⟩ := hBsurj 1
  have hroot₀ : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hrM, htr, -, hrV, hr⟩ := hroot c μ hc0 hca hμ
    exact ⟨r, hrM, htr, hrV, hr⟩
  obtain ⟨μ₀, hμ₀⟩ := h.exists_scalar hx ht hβ₀B hβ₀ hB hc hroot₀
  obtain ⟨β₁, hβ₁B, hβ₁⟩ := hBsurj μ₀
  have hb₀M : φ β₁ ∈ M := hBM _ hβ₁B
  have hb₀sq : φ β₁ * φ β₁ = 1 := by
    rw [← h.add, ← two_smul F β₁, CharTwo.two_eq_zero, zero_smul, h.zero]
  have hb₀inv : (φ β₁)⁻¹ = φ β₁ := inv_eq_of_mul_eq_one_right hb₀sq
  have ht' : φ β₁ * t ∈ M := M.mul_mem hb₀M ht
  have hrootA : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, r ∈ M ∧ ⁅φ β₁ * t, r⁆ ∈ Q ∧ (∀ v ∈ V, r * v * r⁻¹ = v) ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hrM, htr, hBr, hrV, hr⟩ := hroot c μ hc0 hca hμ
    refine ⟨r, hrM, ?_, hrV, hr⟩
    have e : ⁅φ β₁ * t, r⁆ = φ β₁ * ⁅t, r⁆ * (φ β₁)⁻¹ * ⁅φ β₁, r⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem (h.normQ _ hb₀M _ htr) (hBr _ hβ₁B)
  have hFA : ∀ x, spForm a x = 0 → BigEpsInA φ a ⁅φ β₁ * t, φ x⁆ := by
    intro x hxa
    obtain ⟨l₀, hl₀⟩ := hc x hxa
    have hcxA : ⁅t, φ x⁆ = φ (l₀ • a) := by
      rw [commutatorElement_def, hl₀, h.add, h.commute x (l₀ • a)]
      group
    have e : ⁅φ β₁ * t, φ x⁆ = φ β₁ * ⁅t, φ x⁆ * (φ β₁)⁻¹ * ⁅φ β₁, φ x⁆ := by
      simp only [commutatorElement_def]
      group
    have hc1 : ⁅φ β₁, φ x⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h.commute β₁ x
    have hc2 : φ β₁ * φ (l₀ • a) * (φ β₁)⁻¹ = φ (l₀ • a) := by
      rw [h.commute β₁ (l₀ • a)]
      group
    refine ⟨l₀, ?_⟩
    rw [e, hcxA, hc1, hc2, mul_one]
  have hV : ∀ p ∈ P, ⁅φ β₁ * t, p⁆ ∈ V := by
    intro p hp
    obtain ⟨u, c, hu, hpar⟩ := h.act p hp
    obtain ⟨y, hy⟩ := h.rel_exists hx ht hβ₀B hβ₀ hB hc hp
    obtain ⟨l, hl⟩ := hμ₀ p hp u c y hu hpar hy
    obtain ⟨hya, v, hv, e⟩ := hy
    have hφy : φ y ∈ P := (h.mem_P y).mpr hya
    have e1 : ⁅φ β₁ * t, p⁆ = φ β₁ * ⁅t, p⁆ * (φ β₁)⁻¹ * ⁅φ β₁, p⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅φ β₁, p⁆ = φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a) := by
      have e3 := h.comm_param hpar β₁
      rw [hβ₁] at e3
      have e4 : ⁅φ β₁, p⁆ = (⁅p, φ β₁⁆)⁻¹ := by
        rw [commutatorElement_inv]
      rw [e4, e3, ← h.neg, vec_neg_eq_self]
    have hz₁a : spForm a (μ₀ • u + (spForm u β₁ + c * μ₀) • a) = 0 := by
      rw [spForm_add_right, spForm_smul_right', spForm_smul_right', hu, spForm_self]
      ring
    have hφz₁ : φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a) ∈ P := (h.mem_P _).mpr hz₁a
    have hv' : φ β₁ * v * (φ β₁)⁻¹ ∈ V := hx.normV _ hb₀M v hv
    have hc3 : (φ β₁ * v * (φ β₁)⁻¹) * φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a) =
        φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a) * (φ β₁ * v * (φ β₁)⁻¹) :=
      hx.Vcent _ hv' _ hφz₁
    have e5 : φ β₁ * (φ y * v) * (φ β₁)⁻¹ = φ y * (φ β₁ * v * (φ β₁)⁻¹) := by
      have hc4 : φ β₁ * φ y = φ y * φ β₁ := h.commute β₁ y
      calc φ β₁ * (φ y * v) * (φ β₁)⁻¹ = (φ β₁ * φ y) * v * (φ β₁)⁻¹ := by group
        _ = (φ y * φ β₁) * v * (φ β₁)⁻¹ := by rw [hc4]
        _ = φ y * (φ β₁ * v * (φ β₁)⁻¹) := by group
    have hsum : y + (μ₀ • u + (spForm u β₁ + c * μ₀) • a) =
        (l + (spForm u β₁ + c * μ₀)) • a := by
      rw [hl]
      have h2u : μ₀ • u + μ₀ • u = 0 := by
        rw [← two_smul F (μ₀ • u), CharTwo.two_eq_zero, zero_smul]
      calc μ₀ • u + l • a + (μ₀ • u + (spForm u β₁ + c * μ₀) • a)
          = (μ₀ • u + μ₀ • u) + (l • a + (spForm u β₁ + c * μ₀) • a) := by abel
        _ = (l + (spForm u β₁ + c * μ₀)) • a := by
          rw [h2u, zero_add]
          exact (add_smul _ _ _).symm
    rw [e1, e, e5, e2]
    have hfin : φ y * (φ β₁ * v * (φ β₁)⁻¹) * φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a) =
        φ ((l + (spForm u β₁ + c * μ₀)) • a) * (φ β₁ * v * (φ β₁)⁻¹) := by
      calc φ y * (φ β₁ * v * (φ β₁)⁻¹) * φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a)
          = φ y * ((φ β₁ * v * (φ β₁)⁻¹) * φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a)) := by
            group
        _ = φ y * (φ (μ₀ • u + (spForm u β₁ + c * μ₀) • a) * (φ β₁ * v * (φ β₁)⁻¹)) := by
            rw [hc3]
        _ = φ (y + (μ₀ • u + (spForm u β₁ + c * μ₀) • a)) * (φ β₁ * v * (φ β₁)⁻¹) := by
            rw [h.add y (μ₀ • u + (spForm u β₁ + c * μ₀) • a)]
            group
        _ = φ ((l + (spForm u β₁ + c * μ₀)) • a) * (φ β₁ * v * (φ β₁)⁻¹) := by rw [hsum]
    rw [hfin]
    exact V.mul_mem (hx.AV _) hv'
  have hAll := h.comm_inA hx hrootA hFA hV
  have hQt := hKQ (φ β₁ * t) ht' hAll
  exact ⟨φ β₁, hβ₁B, by rw [hb₀inv]; exact hQt⟩

end BigEpsTwoF

end CFSG.RankThree.GF2n.Tim79a
