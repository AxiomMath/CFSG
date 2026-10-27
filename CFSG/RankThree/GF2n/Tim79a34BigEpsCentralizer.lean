module

public import CFSG.RankThree.GF2n.Tim79a34BigEpsLe
public import CFSG.RankThree.GF2n.Tim79a34SpSchur
public import CFSG.RankThree.GF2n.Tim79a34BigAlpha
public import CFSG.RankThree.GF2n.Tim79a34BigDirectTrans
public import CFSG.RankThree.GF2n.Tim79a34BigRoot
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SchurZassenhaus

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank
  CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

section BigEpsCfg

variable {G : Type} [Group G] {F : Type} [Field F] {n : ℕ}

@[expose] def BigEpsParam (φ : (Fin n ⊕ Fin n → F) → G) (a : Fin n ⊕ Fin n → F) (p : G)
    (u : Fin n ⊕ Fin n → F) (c : F) : Prop :=
  ∀ β, p * φ β * p⁻¹ = φ (β + spForm a β • u + spForm u β • a + (c * spForm a β) • a)

structure BigEpsCfg (φ : (Fin n ⊕ Fin n → F) → G) (a : Fin n ⊕ Fin n → F)
    (M P Q B : Subgroup G) : Prop where
  hn : 2 ≤ n
  ha : a ≠ 0
  add : ∀ u v, φ (u + v) = φ u * φ v
  inj : Function.Injective φ
  mem_P : ∀ w, φ w ∈ P ↔ spForm a w = 0
  comm_Q : ∀ q ∈ Q, ∀ x ∈ P, ∃ l : F, ⁅q, x⁆ = φ (l • a)
  normP : ∀ m ∈ M, ∀ p ∈ P, m * p * m⁻¹ ∈ P
  normQ : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q
  act : ∀ p ∈ P, ∃ u c, spForm a u = 0 ∧ BigEpsParam φ a p u c
  cover : ∀ β, spForm a β ≠ 0 → ∀ z, spForm a z = 0 → ∃ p ∈ P, ⁅p, φ β⁆ = φ z
  QW : ∀ β, φ β ∈ Q → φ β ∈ P
  BW : ∀ b ∈ B, ∃ β, φ β = b
  BP : ∀ b ∈ B, b ∈ P → b = 1

variable {φ : (Fin n ⊕ Fin n → F) → G} {a : Fin n ⊕ Fin n → F} {M P Q B : Subgroup G}

theorem BigEpsCfg.zero (h : BigEpsCfg φ a M P Q B) : φ 0 = 1 := by
  simpa using h.add 0 0

theorem BigEpsCfg.neg (h : BigEpsCfg φ a M P Q B) (u : Fin n ⊕ Fin n → F) :
    φ (-u) = (φ u)⁻¹ := by
  have h1 := h.add u (-u)
  rw [add_neg_cancel, h.zero] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem BigEpsCfg.commute (h : BigEpsCfg φ a M P Q B) (u v : Fin n ⊕ Fin n → F) :
    φ u * φ v = φ v * φ u := by
  rw [← h.add, ← h.add, add_comm]

theorem BigEpsCfg.comm_param (h : BigEpsCfg φ a M P Q B) {p : G} {u : Fin n ⊕ Fin n → F} {c : F}
    (hp : BigEpsParam φ a p u c) (β : Fin n ⊕ Fin n → F) :
    ⁅p, φ β⁆ = φ (spForm a β • u + (spForm u β + c * spForm a β) • a) := by
  rw [commutatorElement_def, hp β, ← h.neg, ← h.add]
  congr 1
  module

theorem BigEpsCfg.exists_T (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    (hT3 : ∀ x, spForm a x = 0 → ∃ y, φ y = t * φ x * t⁻¹) :
    ∃ T : (Fin n ⊕ Fin n → F) → (Fin n ⊕ Fin n → F), ∀ x, spForm a x = 0 →
      spForm a (T x) = 0 ∧ φ (T x) = t * φ x * t⁻¹ := by
  have key : ∀ x : Fin n ⊕ Fin n → F, ∃ y, spForm a x = 0 →
      spForm a y = 0 ∧ φ y = t * φ x * t⁻¹ := by
    intro x
    by_cases hx : spForm a x = 0
    · obtain ⟨y, hy⟩ := hT3 x hx
      refine ⟨y, fun _ => ⟨?_, hy⟩⟩
      rw [← h.mem_P, hy]
      exact h.normP t ht _ ((h.mem_P x).mpr hx)
    · exact ⟨0, fun h0 => absurd h0 hx⟩
  choose T hT using key
  exact ⟨T, hT⟩

theorem BigEpsCfg.conj_eq (h : BigEpsCfg φ a M P Q B) {q x : G} (hq : q ∈ Q) (hx : x ∈ P) :
    ∃ l : F, q * x * q⁻¹ = φ (l • a) * x := by
  obtain ⟨l, hl⟩ := h.comm_Q q hq x hx
  exact ⟨l, by rw [← hl, commutatorElement_def]; group⟩

theorem BigEpsCfg.exists_kappa [CharP F 2] (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    (hT3 : ∀ x, spForm a x = 0 → ∃ y, φ y = t * φ x * t⁻¹)
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, ⁅t, r⁆ ∈ Q ∧
        ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c)) :
    ∃ κ : F, ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (κ • x + l • a) := by
  obtain ⟨T, hT⟩ := h.exists_T ht hT3
  have hadd : ∀ x y, spForm a x = 0 → spForm a y = 0 → T (x + y) = T x + T y := by
    intro x y hx hy
    apply h.inj
    have hxy : spForm a (x + y) = 0 := by rw [spForm_add_right, hx, hy, add_zero]
    rw [(hT _ hxy).2, h.add, h.add, (hT x hx).2, (hT y hy).2]
    group
  have hcomm : ∀ (c y : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      spForm a y = 0 → ∃ l : F, T (y + (μ * spForm c y) • c) =
        T y + (μ * spForm c (T y)) • c + l • a := by
    intro c y μ hc hca hy
    by_cases hμ : μ = 0
    · exact ⟨0, by simp [hμ]⟩
    obtain ⟨r, hrQ, hr⟩ := hroot c μ hc hca hμ
    have hy' : spForm a (y + (μ * spForm c y) • c) = 0 := by
      rw [spForm_add_right, spForm_smul_right', hy, hc]
      ring
    have hTy := hT y hy
    have hz0 : spForm a (T y + (μ * spForm c (T y)) • c) = 0 := by
      rw [spForm_add_right, spForm_smul_right', hTy.1, hc]
      ring
    obtain ⟨κ', hκ'⟩ : ∃ κ' : G, κ' = t * r * t⁻¹ * r⁻¹ := ⟨_, rfl⟩
    have hκ'Q : κ' ∈ Q := by
      rw [hκ']
      simpa [commutatorElement_def] using hrQ
    have hs : t * r * t⁻¹ = κ' * r := by
      rw [hκ']
      group
    obtain ⟨l, hl⟩ := h.conj_eq hκ'Q ((h.mem_P _).mpr hz0)
    refine ⟨l, ?_⟩
    apply h.inj
    calc φ (T (y + (μ * spForm c y) • c)) = t * φ (y + (μ * spForm c y) • c) * t⁻¹ :=
          (hT _ hy').2
      _ = (t * r * t⁻¹) * (t * φ y * t⁻¹) * (t * r * t⁻¹)⁻¹ := by
          rw [← hr y]
          group
      _ = κ' * (r * φ (T y) * r⁻¹) * κ'⁻¹ := by
          rw [hs, hTy.2]
          group
      _ = κ' * φ (T y + (μ * spForm c (T y)) • c) * κ'⁻¹ := by rw [hr (T y)]
      _ = φ (l • a) * φ (T y + (μ * spForm c (T y)) • c) := hl
      _ = φ (T y + (μ * spForm c (T y)) • c + l • a) := by rw [← h.add, add_comm]
  obtain ⟨κ, hκ⟩ := sp_perp_schur h.hn h.ha T hadd (fun x hx => (hT x hx).1) hcomm
  refine ⟨κ, fun x hx => ?_⟩
  obtain ⟨l, hl⟩ := hκ x hx
  exact ⟨l, by rw [← (hT x hx).2, hl]⟩

theorem BigEpsCfg.pow_conj (h : BigEpsCfg φ a M P Q B) {t : G} {κ : F}
    (hκ : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (κ • x + l • a)) (j : ℕ) :
    ∀ x, spForm a x = 0 → ∃ l : F, t ^ j * φ x * (t ^ j)⁻¹ = φ (κ ^ j • x + l • a) := by
  induction j with
  | zero => intro x _; exact ⟨0, by simp⟩
  | succ j ih =>
    intro x hx
    obtain ⟨l, hl⟩ := ih x hx
    have hx' : spForm a (κ ^ j • x + l • a) = 0 := by
      rw [spForm_add_right, spForm_smul_right', spForm_smul_right', hx, spForm_self]
      ring
    obtain ⟨l', hl'⟩ := hκ _ hx'
    refine ⟨κ * l + l', ?_⟩
    have e : t ^ (j + 1) * φ x * (t ^ (j + 1))⁻¹ = t * (t ^ j * φ x * (t ^ j)⁻¹) * t⁻¹ := by
      rw [pow_succ']
      group
    rw [e, hl, hl']
    congr 1
    module

theorem BigEpsCfg.kappa_eq_one [CharP F 2] (h : BigEpsCfg φ a M P Q B) {t : G} {κ : F}
    (hκ : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (κ • x + l • a)) {k : ℕ}
    (hk : t ^ (2 ^ k) ∈ Q) : κ = 1 := by
  obtain ⟨x, -, hxa, hxF⟩ := exists_perp_vec_not_smul h.hn h.ha
  obtain ⟨l, hl⟩ := h.pow_conj hκ (2 ^ k) x hxa
  obtain ⟨l', hl'⟩ := h.conj_eq hk ((h.mem_P x).mpr hxa)
  have h2 : κ ^ (2 ^ k) • x + l • a = l' • a + x := by
    apply h.inj
    rw [← hl, hl', h.add]
  by_contra hne
  have hne' : κ ^ (2 ^ k) ≠ 1 := fun h1 => hne (charTwo_pow_two_pow_eq_one h1)
  have hsub : κ ^ (2 ^ k) - 1 ≠ 0 := sub_ne_zero.mpr hne'
  have h3 : (κ ^ (2 ^ k) - 1) • x = (l' - l) • a := by
    linear_combination (norm := module) h2
  apply hxF ((κ ^ (2 ^ k) - 1)⁻¹ * (l' - l))
  calc x = (κ ^ (2 ^ k) - 1)⁻¹ • ((κ ^ (2 ^ k) - 1) • x) := by
        rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
    _ = ((κ ^ (2 ^ k) - 1)⁻¹ * (l' - l)) • a := by rw [h3, smul_smul]

theorem BigEpsCfg.param_unique (h : BigEpsCfg φ a M P Q B) {p : G} {u u' : Fin n ⊕ Fin n → F}
    {c c' : F} (hp : BigEpsParam φ a p u c) (hp' : BigEpsParam φ a p u' c') :
    ∃ m : F, u' = u + m • a := by
  obtain ⟨b₀, hb₀⟩ := exists_spForm_eq_one h.ha
  have h1 := h.inj ((hp b₀).symm.trans (hp' b₀))
  rw [hb₀] at h1
  exact ⟨spForm u b₀ + c - spForm u' b₀ - c',
    by linear_combination (norm := module) (-1 : F) • h1⟩

theorem BigEpsCfg.param_conj_Q (h : BigEpsCfg φ a M P Q B) {q p : G} (hq : q ∈ Q) (hp : p ∈ P)
    {u : Fin n ⊕ Fin n → F} {c : F} (hpar : BigEpsParam φ a p u c) :
    BigEpsParam φ a (q * p * q⁻¹) u c := by
  obtain ⟨l, hl⟩ := h.conj_eq hq hp
  intro β
  rw [hl]
  have e : φ (l • a) * p * φ β * (φ (l • a) * p)⁻¹ =
      φ (l • a) * (p * φ β * p⁻¹) * (φ (l • a))⁻¹ := by group
  rw [e, hpar β, h.commute (l • a), mul_inv_cancel_right]

theorem BigEpsCfg.param_conj_t (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    (h1 : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {β β'' : Fin n ⊕ Fin n → F} {k : G} (hk : k ∈ Q) (hkk : t * φ β * t⁻¹ = φ β'' * k)
    {p : G} (hp : p ∈ P) {u u₁ : Fin n ⊕ Fin n → F} {c c₁ : F} (hu : spForm a u = 0)
    (hpar : BigEpsParam φ a p u c) (hpar₁ : BigEpsParam φ a (t * p * t⁻¹) u₁ c₁) :
    ∃ m : F, spForm a β'' • u₁ = spForm a β • u + m • a := by
  have hp₁ : t * p * t⁻¹ ∈ P := h.normP t ht p hp
  have hL : ⁅t * p * t⁻¹, t * φ β * t⁻¹⁆ = t * ⁅p, φ β⁆ * t⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h.comm_param hpar β] at hL
  have hzL : spForm a (spForm a β • u + (spForm u β + c * spForm a β) • a) = 0 := by
    rw [spForm_add_right, spForm_smul_right', spForm_smul_right', hu, spForm_self]
    ring
  obtain ⟨l, hl⟩ := h1 _ hzL
  rw [hl] at hL
  obtain ⟨l₂, hl₂⟩ := h.comm_Q k hk (t * p * t⁻¹) hp₁
  have hR : ⁅t * p * t⁻¹, φ β'' * k⁆ =
      ⁅t * p * t⁻¹, φ β''⁆ * (φ β'' * ⁅t * p * t⁻¹, k⁆ * (φ β'')⁻¹) := by
    simp only [commutatorElement_def]
    group
  have hkp : ⁅t * p * t⁻¹, k⁆ = φ (-(l₂ • a)) := by
    rw [← commutatorElement_inv, hl₂, h.neg]
  rw [hkk, hR, h.comm_param hpar₁ β'', hkp] at hL
  have hc : φ β'' * φ (-(l₂ • a)) * (φ β'')⁻¹ = φ (-(l₂ • a)) := by
    rw [h.commute β'', mul_inv_cancel_right]
  rw [hc, ← h.add] at hL
  have h2 := h.inj hL
  exact ⟨(spForm u β + c * spForm a β) + l + l₂ - (spForm u₁ β'' + c₁ * spForm a β''),
    by linear_combination (norm := module) h2⟩

theorem BigEpsCfg.param_conj_pow (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    (h1 : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {β β'' : Fin n ⊕ Fin n → F} {k : G} (hk : k ∈ Q) (hkk : t * φ β * t⁻¹ = φ β'' * k)
    (hβ'' : spForm a β'' ≠ 0) (j : ℕ) :
    ∀ p ∈ P, ∀ (u u' : Fin n ⊕ Fin n → F) (c c' : F), spForm a u = 0 →
      BigEpsParam φ a p u c → BigEpsParam φ a (t ^ j * p * (t ^ j)⁻¹) u' c' →
      ∃ m : F, u' = ((spForm a β'')⁻¹ * spForm a β) ^ j • u + m • a := by
  induction j with
  | zero =>
    intro p _ u u' c c' _ hpar hpar'
    obtain ⟨m, hm⟩ := h.param_unique hpar (by simpa using hpar')
    exact ⟨m, by simpa using hm⟩
  | succ j ih =>
    intro p hp u u' c c' hu hpar hpar'
    have hpjP : t ^ j * p * (t ^ j)⁻¹ ∈ P := h.normP _ (pow_mem ht j) p hp
    obtain ⟨uj, cj, huj, hparj⟩ := h.act _ hpjP
    obtain ⟨m, hm⟩ := ih p hp u uj c cj hu hpar hparj
    have hpar'' : BigEpsParam φ a (t * (t ^ j * p * (t ^ j)⁻¹) * t⁻¹) u' c' := by
      have e : t * (t ^ j * p * (t ^ j)⁻¹) * t⁻¹ = t ^ (j + 1) * p * (t ^ (j + 1))⁻¹ := by
        rw [pow_succ']
        group
      rw [e]
      exact hpar'
    obtain ⟨m', hm'⟩ := h.param_conj_t ht h1 hk hkk hpjP huj hparj hpar''
    have hu' : u' = (spForm a β'')⁻¹ • (spForm a β'' • u') := by
      rw [smul_smul, inv_mul_cancel₀ hβ'', one_smul]
    refine ⟨(spForm a β'')⁻¹ * m' + (spForm a β'')⁻¹ * spForm a β * m, ?_⟩
    rw [hu', hm', hm]
    module

theorem BigEpsCfg.ratio_eq_one [CharP F 2] (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    (h1 : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a))
    {β β'' : Fin n ⊕ Fin n → F} {k₀ : G} (hk₀ : k₀ ∈ Q) (hkk : t * φ β * t⁻¹ = φ β'' * k₀)
    (hβ : spForm a β ≠ 0) (hβ'' : spForm a β'' ≠ 0) {k : ℕ} (hk : t ^ (2 ^ k) ∈ Q) :
    spForm a β'' = spForm a β := by
  obtain ⟨z, -, hz0, hza⟩ := exists_perp_vec_not_smul h.hn h.ha
  obtain ⟨p, hp, hpz⟩ := h.cover β hβ z hz0
  obtain ⟨u, c, hu, hpar⟩ := h.act p hp
  have hpar' := h.param_conj_Q hk hp hpar
  obtain ⟨m, hm⟩ := h.param_conj_pow ht h1 hk₀ hkk hβ'' (2 ^ k) p hp u u c c hu hpar hpar'
  have hu_notin : ∀ l : F, u ≠ l • a := by
    intro l hl
    have h3 := h.inj ((h.comm_param hpar β).symm.trans hpz)
    apply hza (spForm a β * l + (spForm u β + c * spForm a β))
    rw [← h3, hl]
    module
  set ρ : F := (spForm a β'')⁻¹ * spForm a β with hρ
  have hρ1 : ρ = 1 := by
    refine charTwo_pow_two_pow_eq_one (k := k) ?_
    by_contra hne
    have hsub : 1 - ρ ^ (2 ^ k) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    apply hu_notin ((1 - ρ ^ (2 ^ k))⁻¹ * m)
    have h4 : (1 - ρ ^ (2 ^ k)) • u = m • a := by
      linear_combination (norm := module) hm
    calc u = (1 - ρ ^ (2 ^ k))⁻¹ • ((1 - ρ ^ (2 ^ k)) • u) := by
          rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
      _ = ((1 - ρ ^ (2 ^ k))⁻¹ * m) • a := by rw [h4, smul_smul]
  exact (inv_mul_eq_one₀ hβ'').mp hρ1

theorem BigEpsCfg.main [CharP F 2] (h : BigEpsCfg φ a M P Q B) {t : G} (ht : t ∈ M)
    (hroot : ∀ (c : Fin n ⊕ Fin n → F) (μ : F), spForm a c = 0 → (∀ l : F, c ≠ l • a) →
      μ ≠ 0 → ∃ r : G, ⁅t, r⁆ ∈ Q ∧ ∀ y, r * φ y * r⁻¹ = φ (y + (μ * spForm c y) • c))
    (hT2 : ∀ b ∈ B, ∃ b'' ∈ B, b''⁻¹ * (t * b * t⁻¹) ∈ Q)
    (hT3 : ∀ x, spForm a x = 0 → ∃ y, φ y = t * φ x * t⁻¹)
    (hT4 : ∃ k : ℕ, t ^ (2 ^ k) ∈ Q) : ∀ b ∈ B, b⁻¹ * (t * b * t⁻¹) ∈ Q := by
  obtain ⟨k, hk⟩ := hT4
  obtain ⟨κ, hκ⟩ := h.exists_kappa ht hT3 hroot
  have hκ1 : κ = 1 := h.kappa_eq_one hκ hk
  have h1 : ∀ x, spForm a x = 0 → ∃ l : F, t * φ x * t⁻¹ = φ (x + l • a) := by
    intro x hx
    obtain ⟨l, hl⟩ := hκ x hx
    exact ⟨l, by rw [hl, hκ1, one_smul]⟩
  intro b hb
  by_cases hb1 : b = 1
  · subst hb1
    rw [inv_one, one_mul, mul_one, mul_inv_cancel]
    exact Q.one_mem
  obtain ⟨β, rfl⟩ := h.BW b hb
  obtain ⟨b'', hb''B, hb''Q⟩ := hT2 _ hb
  obtain ⟨β'', rfl⟩ := h.BW b'' hb''B
  have hkk : t * φ β * t⁻¹ = φ β'' * ((φ β'')⁻¹ * (t * φ β * t⁻¹)) := by group
  have hβ : spForm a β ≠ 0 := fun h0 => hb1 (h.BP _ hb ((h.mem_P β).mpr h0))
  have hβ'' : spForm a β'' ≠ 0 := by
    intro h0
    have h1' : φ β'' = 1 := h.BP _ hb''B ((h.mem_P β'').mpr h0)
    apply hβ
    have hq : t * φ β * t⁻¹ ∈ Q := by
      have h2 := hb''Q
      rw [h1', inv_one, one_mul] at h2
      exact h2
    have hq' : φ β ∈ Q := by
      have h2 := h.normQ t⁻¹ (Subgroup.inv_mem _ ht) _ hq
      have e : t⁻¹ * (t * φ β * t⁻¹) * (t⁻¹)⁻¹ = φ β := by group
      rwa [e] at h2
    exact (h.mem_P β).mp (h.QW β hq')
  have hlam : spForm a β'' = spForm a β := h.ratio_eq_one ht h1 hb''Q hkk hβ hβ'' hk
  have hmem : φ β'' * (φ β)⁻¹ ∈ P := by
    rw [← h.neg, ← h.add, h.mem_P, ← sub_eq_add_neg, spForm_sub_right, hlam, sub_self]
  have hBmem : φ β'' * (φ β)⁻¹ ∈ B := B.mul_mem hb''B (B.inv_mem hb)
  have heq : φ β'' = φ β := mul_inv_eq_one.mp (h.BP _ hBmem hmem)
  rw [heq] at hb''Q
  exact hb''Q

end BigEpsCfg

theorem exists_odd_complement_of_two_elements {Mb : Type} [Group Mb] [Finite Mb]
    (R W : Subgroup Mb) (hWC : W ≤ Subgroup.centralizer (R : Set Mb))
    (hN : Subgroup.normalizer (R : Set Mb) ≤ Subgroup.normalizer (W : Set Mb))
    (hsq : ∀ w ∈ W, w * w = 1) (hcard : ∃ f : ℕ, Nat.card W = 2 ^ f)
    (hclaim : ∀ x ∈ Subgroup.centralizer (R : Set Mb), (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ W) :
    ∃ K : Subgroup Mb, Odd (Nat.card K) ∧ Subgroup.centralizer (R : Set Mb) = W ⊔ K := by
  set C : Subgroup Mb := Subgroup.centralizer (R : Set Mb) with hC
  have hCN : C ≤ Subgroup.normalizer (W : Set Mb) :=
    (Subgroup.centralizer_le_normalizer _).trans hN
  haveI hnorm : (W.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWC).mpr hCN
  have hodd : Odd (W.subgroupOf C).index := by
    by_contra hnot
    have h2 : 2 ∣ (W.subgroupOf C).index :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥C ⧸ W.subgroupOf C) 2 h2
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
    have hc1 : (c : ↥C ⧸ W.subgroupOf C) ^ 2 = 1 := by
      rw [← hy]
      exact pow_orderOf_eq_one _
    have hc2 : (c : ↥C ⧸ W.subgroupOf C) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hy
      omega
    have hcW2 : (c : Mb) ^ 2 ∈ W := by
      have h3 : c ^ 2 ∈ W.subgroupOf C := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact hc1
      exact Subgroup.mem_subgroupOf.mp h3
    have hcW : (c : Mb) ∈ W := by
      refine hclaim c c.2 ⟨2, ?_⟩
      have h4 : (c : Mb) ^ 2 * (c : Mb) ^ 2 = 1 := hsq _ hcW2
      calc (c : Mb) ^ 2 ^ 2 = (c : Mb) ^ (2 + 2) := by norm_num
        _ = (c : Mb) ^ 2 * (c : Mb) ^ 2 := pow_add _ _ _
        _ = 1 := h4
    apply hc2
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hcW
  have hcop : Nat.Coprime (Nat.card (W.subgroupOf C)) (W.subgroupOf C).index := by
    obtain ⟨f, hf⟩ := hcard
    have h1 : Nat.card (W.subgroupOf C) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
    rw [h1, hf]
    exact Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr hodd)
  obtain ⟨K', hK'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨K'.map C.subtype, ?_, ?_⟩
  · rw [Subgroup.card_subtype, ← hK'.symm.index_eq_card]
    exact hodd
  · apply le_antisymm
    · intro x hx
      have htop : W.subgroupOf C ⊔ K' = ⊤ := hK'.sup_eq_top
      have hx' : (⟨x, hx⟩ : ↥C) ∈ W.subgroupOf C ⊔ K' := by
        rw [htop]
        trivial
      have h5 := Subgroup.mem_map_of_mem C.subtype hx'
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWC] at h5
      exact h5
    · exact sup_le hWC (Subgroup.map_subtype_le K')

theorem bigEpsCent_data (hZ : Sec34CentreTrivialStatement) (hN : BigNaturalStatement)
    (hIW : BigIWStatement) (hγ : BigGammaStatement) (G : Type) [Group G] [Finite G]
    (M V Q P H : Subgroup G) (hH : BigEndHyp M V Q P H) :
    ∃ (n f : ℕ) (ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H))
      (a : Fin n ⊕ Fin n → GaloisField 2 f) (B : Subgroup G),
      2 ^ f = qBar V H ∧ BigEpsCfg (psiElt ψ) a M P Q B ∧ B ≤ wOf V H ∧
      (P ⊓ wOf V H) ⊔ B = wOf V H ∧
      ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
        (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
        ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
          ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcentre : Subgroup.center (Xbar V H) = ⊥ :=
    hZ G M V Q P H ⟨hH.setup, hH.tilde, hH.concl⟩ hH.three hH.centre
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hcentre
  obtain ⟨n, f, Φ, ψ, hn2, hf, hequiv, ⟨a, T, ha, hTT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hcentre
  have hNat : BigNatCfg V H hH.setup.mc.toMinCex.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨B, hBW, hBP, hPB, -⟩ := bigBStatement_of_local hZ hN hIW G M V Q P H hH
  obtain ⟨hiff, hRbar, hxOf, -⟩ :=
    bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV
  have hCover := bigPCoverStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ hNat a T ha hTT hTV
  have hroot := bigRootElement_holds bigPLocalStatement_holds G M V Q P H hH hcentre hcP hf Φ ψ
    hNat a T ha hTT hTV
  have hPQ := (bigPQCommStatement_of_natural hZ hN hIW hγ G M V Q P H hH).1
  have hQW := bigQWStatement_of_natural hZ hN hIW hγ G M V Q P H hH
  have hiff' : ∀ w, psiElt ψ w ∈ P ↔ spForm a w = 0 := hiff
  refine ⟨n, f, ψ, a, B, hf, ⟨hn2, ha, psiElt_add ψ, psiElt_injective ψ, hiff', ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, hBW, hPB, fun c μ hc0 hca hμ => hroot c μ hc0 hca hμ⟩
  · intro q hq x hx
    obtain ⟨hV, hW⟩ := Subgroup.mem_inf.mp (hPQ q hq x hx)
    obtain ⟨u, hu⟩ := exists_psiElt ψ hW
    obtain ⟨l, hl⟩ := bigRW_eq_smul_of_psi_mem_V hH hf hNat ha hTT hTV (u := u)
      (by rw [show ((Additive.toMul (ψ u) : ↥(wOf V H)) : G) = ⁅q, x⁆ from hu]; exact hV)
    exact ⟨l, by rw [← hu, hl]⟩
  · intro m hm p hp
    exact (Subgroup.mem_normalizer_iff.mp (hc.M_le_normalizer_P hm) p).mp hp
  · intro m hm q hq
    rw [hc.hQ] at hq ⊢
    exact (Subgroup.mem_normalizer_iff.mp ((inSubgroup_pCore_two M).2.2 hm) q).mp hq
  · intro p hp
    obtain ⟨τ, hτ, -, -, hact⟩ := bigAlpha_act hc hNat hxOf hRbar hp
    obtain ⟨u, hu, c, hparam⟩ := exists_spRad_param ha hτ
    refine ⟨u, c, hu, fun β => ?_⟩
    exact (hact β).symm.trans (congrArg (psiElt ψ) (hparam β))
  · intro β hβ z hz
    exact hCover β hβ (psiElt ψ z) ⟨(hiff' z).mpr hz, psiElt_mem ψ z⟩
  · intro β hβ
    have h1 : psiElt ψ β ∈ Q ⊓ wOf V H := ⟨hβ, psiElt_mem ψ β⟩
    rw [hQW] at h1
    exact h1.1
  · intro b hb
    exact exists_psiElt ψ (hBW hb)
  · intro b hb hbP
    have h1 : b ∈ B ⊓ P := ⟨hb, hbP⟩
    rw [hBP, Subgroup.mem_bot] at h1
    exact h1

theorem bigEpsCent_two_elements {G : Type} [Group G] [Finite G] {M V Q P H B : Subgroup G}
    (hc : MinCex M V Q P H) {n f : ℕ}
    {ψ : (Fin n ⊕ Fin n → GaloisField 2 f) ≃+ Additive ↥(wOf V H)}
    {a : Fin n ⊕ Fin n → GaloisField 2 f} (hcfg : BigEpsCfg (psiElt ψ) a M P Q B)
    (hBW : B ≤ wOf V H) (hPB : (P ⊓ wOf V H) ⊔ B = wOf V H)
    (hroot : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f), spForm a c = 0 →
      (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r ∈ xOf V H ⊓ Subgroup.centralizer (V : Set G),
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c))
    (hFc : ∀ e : ↥M, (e : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) →
      conjSubgroup (e : G) (P ⊓ wOf V H) = P ⊓ wOf V H)
    (hLe : Subgroup.normalizer (RbarM M V H : Set (Mbar M)) ≤
      Subgroup.normalizer (WbarM M V H : Set (Mbar M)))
    (hF : ∀ x ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)) ⊓
        Subgroup.centralizer (WbarM M V H : Set (Mbar M)),
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ WbarM M V H) :
    ∀ x ∈ Subgroup.centralizer (RbarM M V H : Set (Mbar M)),
      (∃ k : ℕ, x ^ (2 ^ k) = 1) → x ∈ WbarM M V H := by
  intro x hx hxk
  obtain ⟨k, hk⟩ := hxk
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective x
  have hQM : Q = inSubgroup (pCore 2) M := hc.hQ
  have hWM : wOf V H ≤ M := wOf_le_M_of_minCex hc
  have hxN : (t : Mbar M) ∈ Subgroup.normalizer (RbarM M V H : Set (Mbar M)) :=
    Subgroup.centralizer_le_normalizer _ hx
  have hxW := hLe hxN
  have hcomm : ∀ b ∈ B, ∀ f' ∈ P ⊓ wOf V H, b * f' = f' * b := fun b hb f' hf' =>
    hc.wOf_isElemAbelian.comm (hBW hb) (Subgroup.mem_inf.mp hf').2
  have hroot' : ∀ (c : Fin n ⊕ Fin n → GaloisField 2 f) (μ : GaloisField 2 f),
      spForm a c = 0 → (∀ l : GaloisField 2 f, c ≠ l • a) → μ ≠ 0 →
      ∃ r : G, ⁅(t : G), r⁆ ∈ Q ∧
        ∀ y, r * psiElt ψ y * r⁻¹ = psiElt ψ (y + (μ * spForm c y) • c) := by
    intro c μ hc0 hca hμ
    obtain ⟨r, hr, hract⟩ := hroot c μ hc0 hca hμ
    refine ⟨r, ?_, hract⟩
    have hrM : r ∈ M := by
      have h1 : r ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hr).2
      rwa [hc.normalizer_eq] at h1
    have hrbar : ((⟨r, hrM⟩ : ↥M) : Mbar M) ∈ RbarM M V H :=
      Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
    have hcm := Subgroup.mem_centralizer_iff.mp hx _ hrbar
    have key : ((t * ⟨r, hrM⟩ : ↥M) : Mbar M) = ((⟨r, hrM⟩ * t : ↥M) : Mbar M) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hcm.symm
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf] at key
    have e : (((t * ⟨r, hrM⟩) / (⟨r, hrM⟩ * t) : ↥M) : G) = ⁅(t : G), r⁆ := by
      simp only [div_eq_mul_inv, _root_.mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv,
        commutatorElement_def]
      group
    rw [e] at key
    rwa [hQM]
  have hT2 : ∀ b ∈ B, ∃ b'' ∈ B, b''⁻¹ * ((t : G) * b * (t : G)⁻¹) ∈ Q := by
    intro b hb
    have hbM : b ∈ M := hWM (hBW hb)
    have hbbar : ((⟨b, hbM⟩ : ↥M) : Mbar M) ∈ WbarM M V H :=
      mem_WbarM_iff.mpr ⟨⟨b, hbM⟩, hBW hb, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hxW _).mp hbbar
    obtain ⟨w', hw'W, hw'⟩ := mem_WbarM_iff.mp h1
    have hw'BP : (w' : G) ∈ B ⊔ (P ⊓ wOf V H) := by
      rw [sup_comm, hPB]
      exact hw'W
    obtain ⟨b'', hb'', f', hf', hw'eq⟩ := exists_mul_of_mem_sup (S := B) (T := P ⊓ wOf V H)
      hcomm hw'BP
    refine ⟨b'', hb'', ?_⟩
    have hq : (((w' : ↥M)⁻¹ * (t * ⟨b, hbM⟩ * t⁻¹) : ↥M) : G) ∈ inSubgroup (pCore 2) M := by
      have h2 : (w' : Mbar M) = ((t * ⟨b, hbM⟩ * t⁻¹ : ↥M) : Mbar M) := by
        rw [hw', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h2)
    have hq' : (w' : G)⁻¹ * ((t : G) * b * (t : G)⁻¹) ∈ Q := by
      rw [hQM]
      exact hq
    have e : b''⁻¹ * ((t : G) * b * (t : G)⁻¹) =
        f' * ((w' : G)⁻¹ * ((t : G) * b * (t : G)⁻¹)) := by
      rw [hw'eq]
      group
    rw [e]
    exact Q.mul_mem (hc.P_le_Q (Subgroup.mem_inf.mp hf').1) hq'
  have hconj := hFc t hxN
  have hT3 : ∀ y, spForm a y = 0 → ∃ z, psiElt ψ z = (t : G) * psiElt ψ y * (t : G)⁻¹ := by
    intro y hy
    have hmem : (t : G) * psiElt ψ y * (t : G)⁻¹ ∈ conjSubgroup (t : G) (P ⊓ wOf V H) := by
      rw [mem_conjSubgroup]
      have e : (t : G)⁻¹ * ((t : G) * psiElt ψ y * (t : G)⁻¹) * (t : G) = psiElt ψ y := by group
      rw [e]
      exact ⟨(hcfg.mem_P y).mpr hy, psiElt_mem ψ y⟩
    rw [hconj] at hmem
    exact exists_psiElt ψ hmem.2
  have hT4 : ∃ k : ℕ, (t : G) ^ (2 ^ k) ∈ Q := by
    refine ⟨k, ?_⟩
    have h1 : t ^ (2 ^ k) ∈ (inSubgroup (pCore 2) M).subgroupOf M := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hk
    have h2 := Subgroup.mem_subgroupOf.mp h1
    rw [hQM]
    exact h2
  have hmain := hcfg.main t.2 hroot' hT2 hT3 hT4
  have hWbar : ∀ y ∈ WbarM M V H, ∃ (b : G) (_ : b ∈ B) (hbM : b ∈ M),
      y = ((⟨b, hbM⟩ : ↥M) : Mbar M) := by
    intro y hy
    obtain ⟨w, hwW, rfl⟩ := mem_WbarM_iff.mp hy
    have hw' : (w : G) ∈ B ⊔ (P ⊓ wOf V H) := by
      rw [sup_comm, hPB]
      exact hwW
    obtain ⟨b, hb, f', hf', hweq⟩ := exists_mul_of_mem_sup (S := B) (T := P ⊓ wOf V H) hcomm hw'
    have hbM : b ∈ M := hWM (hBW hb)
    have hf'M : f' ∈ M := hWM (Subgroup.mem_inf.mp hf').2
    have hf'Q : f' ∈ inSubgroup (pCore 2) M := by
      rw [← hQM]
      exact hc.P_le_Q (Subgroup.mem_inf.mp hf').1
    refine ⟨b, hb, hbM, ?_⟩
    have hwprod : w = ⟨b, hbM⟩ * ⟨f', hf'M⟩ := Subtype.ext hweq
    have hone : ((⟨f', hf'M⟩ : ↥M) : Mbar M) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hf'Q)
    rw [hwprod, QuotientGroup.mk_mul, hone, mul_one]
  have hxcW : (t : Mbar M) ∈ Subgroup.centralizer (WbarM M V H : Set (Mbar M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, hbM, rfl⟩ := hWbar y hy
    have hbt : ((⟨b, hbM⟩ : ↥M) : Mbar M) = ((t * ⟨b, hbM⟩ * t⁻¹ : ↥M) : Mbar M) := by
      apply QuotientGroup.eq.mpr
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [← hQM]
      exact hmain b hb
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hbt
    calc ((⟨b, hbM⟩ : ↥M) : Mbar M) * (t : Mbar M)
        = ((t : Mbar M) * ((⟨b, hbM⟩ : ↥M) : Mbar M) * (t : Mbar M)⁻¹) * (t : Mbar M) := by
          rw [← hbt]
      _ = (t : Mbar M) * ((⟨b, hbM⟩ : ↥M) : Mbar M) := by group
  exact hF _ (Subgroup.mem_inf.mpr ⟨hx, hxcW⟩) ⟨k, hk⟩

theorem bigEpsilonCentralizerStatement_of_faithfulTwo (hZ : Sec34CentreTrivialStatement)
    (hN : BigNaturalStatement) (hIW : BigIWStatement) (hγ : BigGammaStatement)
    (hFc : BigEpsFConjStatement) (hLe : BigEpsilonNormalizerLeStatement)
    (hF : BigEpsilonFaithfulTwoStatement) : BigEpsilonCentralizerStatement := by
  intro G _ _ M V Q P H hH
  obtain ⟨n, f, ψ, a, B, hf, hcfg, hBW, hPB, hroot⟩ := bigEpsCent_data hZ hN hIW hγ G M V Q P H hH
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hclaim := bigEpsCent_two_elements hc hcfg hBW hPB hroot (hFc G M V Q P H hH)
    (hLe G M V Q P H hH) (hF G M V Q P H hH)
  refine exists_odd_complement_of_two_elements (RbarM M V H) (WbarM M V H)
    (bigWbarCentralizesStatement_holds G M V Q P H hH) (hLe G M V Q P H hH) ?_ ?_ hclaim
  · intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_WbarM_iff.mp hy
    have hw2 : (w : G) * (w : G) = 1 := hc.wOf_isElemAbelian.mul_self_eq_one hw
    have hw2' : w * w = 1 := Subtype.ext hw2
    rw [← QuotientGroup.mk_mul, hw2']
    rfl
  · refine ⟨f, ?_⟩
    rw [bigWbarCardStatement_of_natural hZ hN hIW hγ G M V Q P H hH]
    exact hf.symm

end CFSG.RankThree.GF2n.Tim79a
