module

public import CFSG.RankThree.GF2n.Tim79aSpBraidModel

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic

variable {n : ℕ} {F : Type} [Field F]

theorem tor_spForm_swap [CharP F 2] (u v : Fin n ⊕ Fin n → F) : spForm v u = spForm u v := by
  rw [spForm_comm u v, CharTwo.neg_eq]

theorem tor_spTrans_ne_one {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {s : F} (hs : s ≠ 0) :
    spTrans a s ≠ 1 := by
  intro h
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
  have h1 : spTrans a s *ᵥ y = y := by rw [h, one_mulVec]
  rw [spTrans_mulVec] at h1
  have h2 : (s * spForm a y) • a = 0 := add_left_cancel (h1.trans (add_zero y).symm)
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact mul_ne_zero hs hy h3
  · exact ha h3

theorem tor_spTrans_inj {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {s t : F}
    (h : spTrans a s = spTrans a t) : s = t := by
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
  have h1 : spTrans a s *ᵥ y = spTrans a t *ᵥ y := by rw [h]
  rw [spTrans_mulVec, spTrans_mulVec] at h1
  have h2 : (s * spForm a y) • a = (t * spForm a y) • a := add_left_cancel h1
  have h3 : s * spForm a y = t * spForm a y := smul_left_injective F ha h2
  exact mul_right_cancel₀ hy h3

theorem tor_triple_mulVec [CharP F 2] (a a' x : Fin n ⊕ Fin n → F) (r s : F) :
    (spTrans a s * spTrans a' r * spTrans a s) *ᵥ x =
      x + (s * r * spForm a a' * spForm a' x +
          s * s * r * (spForm a a' * spForm a a') * spForm a x) • a +
        (r * spForm a' x + r * s * spForm a a' * spForm a x) • a' := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  simp only [spTrans_mulVec, spForm_add_left, spForm_add_right, spForm_smul_left',
    spForm_smul_right', spForm_self, tor_spForm_swap a a']
  linear_combination (norm := module) h2 • ((s * spForm a x) • a)

@[expose] def torDmap (a a' : Fin n ⊕ Fin n → F) (μ : F) (x : Fin n ⊕ Fin n → F) :
    Fin n ⊕ Fin n → F :=
  x + ((μ - 1) * (spForm a' x / spForm a a')) • a +
    ((μ⁻¹ - 1) * (spForm a x / spForm a a')) • a'

theorem tor_torDmap_apply (a a' : Fin n ⊕ Fin n → F) (μ : F) (y : Fin n ⊕ Fin n → F) :
    torDmap a a' μ y = y + ((μ - 1) * (spForm a' y / spForm a a')) • a +
      ((μ⁻¹ - 1) * (spForm a y / spForm a a')) • a' := rfl

theorem tor_torDmap_one (a a' x : Fin n ⊕ Fin n → F) : torDmap a a' 1 x = x := by
  simp [torDmap]

theorem tor_torDmap_self [CharP F 2] {a a' : Fin n ⊕ Fin n → F} (hβ : spForm a a' ≠ 0)
    (μ : F) : torDmap a a' μ a = μ • a := by
  rw [tor_torDmap_apply]
  simp only [tor_spForm_swap a a', spForm_self, zero_div, mul_zero, zero_smul, add_zero,
    div_self hβ, mul_one]
  module

theorem tor_torDmap_comp [CharP F 2] {a a' : Fin n ⊕ Fin n → F} (hβ : spForm a a' ≠ 0)
    (μ ν : F) (x : Fin n ⊕ Fin n → F) :
    torDmap a a' μ (torDmap a a' ν x) = torDmap a a' (μ * ν) x := by
  have hdb : spForm a x / spForm a a' * spForm a a' = spForm a x := div_mul_cancel₀ _ hβ
  have hdq : spForm a' x / spForm a a' * spForm a a' = spForm a' x := div_mul_cancel₀ _ hβ
  have hpa : spForm a (torDmap a a' ν x) = ν⁻¹ * spForm a x := by
    rw [tor_torDmap_apply]
    simp only [spForm_add_right, spForm_smul_right', spForm_self, mul_zero, zero_add, add_zero]
    linear_combination (ν⁻¹ - 1) * hdb
  have hqa : spForm a' (torDmap a a' ν x) = ν * spForm a' x := by
    rw [tor_torDmap_apply]
    simp only [spForm_add_right, spForm_smul_right', spForm_self, tor_spForm_swap a a',
      mul_zero, zero_add, add_zero]
    linear_combination (ν - 1) * hdq
  rw [tor_torDmap_apply a a' μ, hqa, hpa]
  simp only [tor_torDmap_apply]
  module

theorem tor_orderOf_three [CharP F 2] {a a' : Fin n ⊕ Fin n → F} {x y : StatedSp n F}
    {s r : F} (ha : a ≠ 0) (hB : spForm a a' ≠ 0) (hs : s ≠ 0)
    (hr : r * (s * spForm a a' * spForm a a') = 1)
    (hx : SpExtras.mat n F x = spTrans a s) (hy : SpExtras.mat n F y = spTrans a' r) :
    orderOf (x * y) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcube, hne⟩ := tim79a_braid_key ha hB hs hr
  apply orderOf_eq_prime
  · apply SpExtras.mat_injective
    rw [map_pow, map_mul, map_one, hx, hy]
    exact hcube
  · intro h
    apply hne
    rw [← hx, ← hy, ← map_mul, h, map_one]

theorem tor_torus_mulVec [CharP F 2] {a a' : Fin n ⊕ Fin n → F} (hβ : spForm a a' ≠ 0)
    {s r₁ rₛ : F} (hs : s ≠ 0) (hr₁ : r₁ * (spForm a a' * spForm a a') = 1)
    (hrₛ : rₛ = s⁻¹ * r₁) (x : Fin n ⊕ Fin n → F) :
    ((spTrans a s * spTrans a' rₛ * spTrans a s) * (spTrans a 1 * spTrans a' r₁ * spTrans a 1))
      *ᵥ x = torDmap a a' s x := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e1 := hr₁
  have e2 : spForm a a' * (spForm a a')⁻¹ = 1 := mul_inv_cancel₀ hβ
  have hS : s * s⁻¹ = 1 := mul_inv_cancel₀ hs
  subst hrₛ
  obtain ⟨y, hyy⟩ : ∃ y, (spTrans a 1 * spTrans a' r₁ * spTrans a 1) *ᵥ x = y := ⟨_, rfl⟩
  have hy : y = x + (r₁ * spForm a a' * spForm a' x +
      r₁ * (spForm a a' * spForm a a') * spForm a x) • a +
      (r₁ * spForm a' x + r₁ * spForm a a' * spForm a x) • a' := by
    rw [← hyy, tor_triple_mulVec]
    module
  have hpy : spForm a y = r₁ * spForm a a' * spForm a' x := by
    rw [hy]
    simp only [spForm_add_right, spForm_smul_right', spForm_self, mul_zero, zero_add, add_zero]
    linear_combination (spForm a x) * e1 + (spForm a x) * h2
  have hqy : spForm a' y = spForm a a' * spForm a x := by
    rw [hy]
    simp only [spForm_add_right, spForm_smul_right', spForm_self, tor_spForm_swap a a',
      mul_zero, zero_add, add_zero]
    linear_combination (spForm a' x + spForm a a' * spForm a x) * e1 + (spForm a' x) * h2
  have hA : (r₁ * spForm a a' * spForm a' x + r₁ * (spForm a a' * spForm a a') * spForm a x) +
      (s * (s⁻¹ * r₁) * spForm a a' * (spForm a a' * spForm a x) +
        s * s * (s⁻¹ * r₁) * (spForm a a' * spForm a a') *
          (r₁ * spForm a a' * spForm a' x)) = (s - 1) * (spForm a' x / spForm a a') := by
    linear_combination (-(1 + s) * spForm a' x * r₁ * spForm a a') * e2 +
      ((1 + s) * spForm a' x * (spForm a a')⁻¹ + 2 * spForm a x +
        s * r₁ * spForm a a' * spForm a' x) * e1 +
      (r₁ * (spForm a a') ^ 2 * spForm a x + s * r₁ ^ 2 * (spForm a a') ^ 3 * spForm a' x) * hS +
      (spForm a' x * (spForm a a')⁻¹ + spForm a x) * h2
  have hB : (r₁ * spForm a' x + r₁ * spForm a a' * spForm a x) +
      (s⁻¹ * r₁ * (spForm a a' * spForm a x) +
        s⁻¹ * r₁ * s * spForm a a' * (r₁ * spForm a a' * spForm a' x)) =
      (s⁻¹ - 1) * (spForm a x / spForm a a') := by
    linear_combination (spForm a' x * r₁ ^ 2 * (spForm a a') ^ 2) * hS +
      (spForm a' x * r₁) * e1 +
      (-(spForm a x * (1 + s⁻¹) * r₁ * spForm a a')) * e2 +
      (spForm a x * (1 + s⁻¹) * (spForm a a')⁻¹) * e1 +
      (r₁ * spForm a' x + spForm a x * (spForm a a')⁻¹) * h2
  rw [← mulVec_mulVec, hyy, tor_triple_mulVec, hpy, hqy, hy]
  simp only [torDmap]
  linear_combination (norm := module) hA • a + hB • a'

theorem spTorusModel_holds :
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2] (a a' : Fin n ⊕ Fin n → F)
      (T T' : Subgroup (StatedSp n F)), IsTransGroup a T → IsTransGroup a' T' →
      spForm a a' ≠ 0 →
      ∃ h ∈ Subgroup.normalizer (T : Set (StatedSp n F)),
        (∀ m ∈ Subgroup.normalizer (T : Set (StatedSp n F)), ∃ i : ℕ,
          ∃ c ∈ Subgroup.centralizer (T : Set (StatedSp n F)), m = c * h ^ i) ∧
        h ^ (Nat.card F - 1) = 1 ∧
        ∀ i : ℕ, 0 < i → i < Nat.card F - 1 →
          ∃ a₁ ∈ T, ∃ a₂ ∈ T, ∃ b₁ ∈ T', ∃ b₂ ∈ T', a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ b₁ ≠ b₂ ∧
            orderOf (a₁ * b₁) = 3 ∧ orderOf (a₂ * b₂) = 3 ∧
            (a₁ * b₁ * a₁) * (a₂ * b₂ * a₂) = h ^ i := by
  intro n F _ _ _ a a' T T' hT hT' hβ
  have ha : a ≠ 0 := by
    rintro rfl
    exact hβ (by simp [spForm])
  have ha' : a' ≠ 0 := by
    rintro rfl
    exact hβ (by simp [spForm])
  obtain ⟨tA, htA⟩ : ∃ f : F → StatedSp n F, ∀ c, SpExtras.mat n F (f c) = spTrans a c :=
    ⟨fun c => (hT.2 c).choose, fun c => (hT.2 c).choose_spec⟩
  obtain ⟨tB, htB⟩ : ∃ f : F → StatedSp n F, ∀ c, SpExtras.mat n F (f c) = spTrans a' c :=
    ⟨fun c => (hT'.2 c).choose, fun c => (hT'.2 c).choose_spec⟩
  have hTA : ∀ c, tA c ∈ T := fun c => (hT.1 (tA c)).2 ⟨c, htA c⟩
  have hTB : ∀ c, tB c ∈ T' := fun c => (hT'.1 (tB c)).2 ⟨c, htB c⟩
  obtain ⟨r, hr⟩ : ∃ r : F → F, ∀ s, r s = (s * spForm a a' * spForm a a')⁻¹ :=
    ⟨fun s => (s * spForm a a' * spForm a a')⁻¹, fun s => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : F → StatedSp n F, ∀ s, W s = tA s * tB (r s) * tA s :=
    ⟨fun s => tA s * tB (r s) * tA s, fun s => rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : F → StatedSp n F, ∀ μ, D μ = W μ * W 1 :=
    ⟨fun μ => W μ * W 1, fun μ => rfl⟩
  have hmW : ∀ s, SpExtras.mat n F (W s) = spTrans a s * spTrans a' (r s) * spTrans a s := by
    intro s
    rw [hW, map_mul, map_mul, htA, htB]
  have hmD : ∀ μ, SpExtras.mat n F (D μ) =
      (spTrans a μ * spTrans a' (r μ) * spTrans a μ) *
        (spTrans a 1 * spTrans a' (r 1) * spTrans a 1) := by
    intro μ
    rw [hD, map_mul, hmW, hmW]
  have hr1 : r 1 * (spForm a a' * spForm a a') = 1 := by
    rw [hr 1, one_mul]
    exact inv_mul_cancel₀ (mul_ne_zero hβ hβ)
  have hrμ : ∀ μ : F, r μ = μ⁻¹ * r 1 := by
    intro μ
    rw [hr μ, hr 1, one_mul, mul_assoc, mul_inv]
  have hG1 : ∀ μ : F, μ ≠ 0 → ∀ x, SpExtras.mat n F (D μ) *ᵥ x = torDmap a a' μ x := by
    intro μ hμ x
    rw [hmD]
    exact tor_torus_mulVec hβ hμ hr1 (hrμ μ) x
  have hG2 : ∀ μ ν : F, μ ≠ 0 → ν ≠ 0 → D μ * D ν = D (μ * ν) := by
    intro μ ν hμ hν
    apply SpExtras.mat_injective
    apply Matrix.ext_iff_mulVec.2
    intro x
    rw [map_mul, ← mulVec_mulVec, hG1 μ hμ, hG1 ν hν, hG1 (μ * ν) (mul_ne_zero hμ hν),
      tor_torDmap_comp hβ]
  have hG3 : D 1 = 1 := by
    apply SpExtras.mat_injective
    apply Matrix.ext_iff_mulVec.2
    intro x
    rw [hG1 1 one_ne_zero, tor_torDmap_one, map_one, one_mulVec]
  have hG4 : ∀ μ : F, μ ≠ 0 → SpExtras.mat n F (D μ) *ᵥ a = μ • a := by
    intro μ hμ
    rw [hG1 μ hμ]
    exact tor_torDmap_self hβ μ
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  have hgz : ∀ y : Fˣ, y ∈ Subgroup.zpowers g := fun y => mem_powers_iff_mem_zpowers.1 (hg y)
  have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hgz
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hgne : (g : F) ≠ 0 := g.ne_zero
  have hpow : ∀ μ : F, μ ≠ 0 → ∃ i : ℕ, (g : F) ^ i = μ := by
    intro μ hμ
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (hg (Units.mk0 μ hμ))
    exact ⟨i, by rw [← Units.val_pow_eq_pow_val, hi, Units.val_mk0]⟩
  have hDpow : ∀ i : ℕ, D (g : F) ^ i = D ((g : F) ^ i) := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, hG3]
    | succ k ih =>
      rw [pow_succ (D (g : F)) k, ih, hG2 _ _ (pow_ne_zero k hgne) hgne, pow_succ (g : F) k]
  have hζq : (g : F) ^ (Nat.card F - 1) = 1 := by
    rw [← hcard, ← hord, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  refine ⟨D (g : F), ?_, ?_, ?_, ?_⟩
  · rw [normalizer_eq_spLine ha hT]
    exact ⟨(g : F), hgne, hG4 _ hgne⟩
  · intro m hm
    rw [normalizer_eq_spLine ha hT] at hm
    obtain ⟨μ, hμ0, hμ⟩ := hm
    obtain ⟨i, hi⟩ := hpow μ hμ0
    have hmi : SpExtras.mat n F (D (g : F) ^ i) *ᵥ a = μ • a := by
      rw [hDpow, hG4 _ (pow_ne_zero i hgne), hi]
    have hcprop : ∃ c : StatedSp n F, m = c * D (g : F) ^ i ∧ SpExtras.mat n F c *ᵥ a = a := by
      refine ⟨m * (D (g : F) ^ i)⁻¹, (inv_mul_cancel_right m _).symm, ?_⟩
      have hcm : SpExtras.mat n F (m * (D (g : F) ^ i)⁻¹) * SpExtras.mat n F (D (g : F) ^ i) =
          SpExtras.mat n F m := by
        rw [← map_mul, inv_mul_cancel_right]
      have key : μ • (SpExtras.mat n F (m * (D (g : F) ^ i)⁻¹) *ᵥ a) = μ • a := by
        calc μ • (SpExtras.mat n F (m * (D (g : F) ^ i)⁻¹) *ᵥ a)
            = SpExtras.mat n F (m * (D (g : F) ^ i)⁻¹) *ᵥ (μ • a) := by rw [mulVec_smul]
          _ = SpExtras.mat n F (m * (D (g : F) ^ i)⁻¹) *ᵥ
                (SpExtras.mat n F (D (g : F) ^ i) *ᵥ a) := by rw [hmi]
          _ = (SpExtras.mat n F (m * (D (g : F) ^ i)⁻¹) * SpExtras.mat n F (D (g : F) ^ i)) *ᵥ a :=
                by rw [mulVec_mulVec]
          _ = SpExtras.mat n F m *ᵥ a := by rw [hcm]
          _ = μ • a := hμ
      exact smul_right_injective _ hμ0 key
    obtain ⟨c, hcm', hca⟩ := hcprop
    refine ⟨i, c, ?_, hcm'⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨s, hs⟩ := (hT.1 t).1 ht
    have hconj : SpExtras.mat n F (c * t * c⁻¹) = spTrans a s := by
      rw [mat_conj_of_mat_eq hs c, hca]
    have hct : c * t * c⁻¹ = t := SpExtras.mat_injective (hconj.trans hs.symm)
    exact (mul_inv_eq_iff_eq_mul.1 hct).symm
  · rw [hDpow, hζq, hG3]
  · intro i hi0 hiq
    have hne1 : (g : F) ^ i ≠ 1 := by
      intro h
      have h' : g ^ i = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
      have hdvd : orderOf g ∣ i := orderOf_dvd_of_pow_eq_one h'
      rw [hord, hcard] at hdvd
      exact absurd (Nat.le_of_dvd hi0 hdvd) (by omega)
    have hsi : (g : F) ^ i ≠ 0 := pow_ne_zero i hgne
    have hr_i : r ((g : F) ^ i) * ((g : F) ^ i * spForm a a' * spForm a a') = 1 := by
      rw [hr]
      exact inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero hsi hβ) hβ)
    have hr_one : r 1 * (1 * spForm a a' * spForm a a') = 1 := by
      rw [hr]
      exact inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero one_ne_zero hβ) hβ)
    refine ⟨tA ((g : F) ^ i), hTA _, tA 1, hTA 1, tB (r ((g : F) ^ i)), hTB _, tB (r 1),
      hTB (r 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact tor_spTrans_ne_one ha hsi (by rw [← htA, h, map_one])
    · intro h
      exact tor_spTrans_ne_one ha one_ne_zero (by rw [← htA, h, map_one])
    · intro h
      have h1 : r ((g : F) ^ i) = r 1 := tor_spTrans_inj ha' (by rw [← htB, ← htB, h])
      rw [hr, hr] at h1
      apply hne1
      have h2 := inv_inj.1 h1
      exact mul_right_cancel₀ hβ (mul_right_cancel₀ hβ h2)
    · exact tor_orderOf_three ha hβ hsi hr_i (htA _) (htB _)
    · exact tor_orderOf_three ha hβ one_ne_zero hr_one (htA _) (htB _)
    · rw [hDpow, hD, hW, hW]

end CFSG.RankThree.GF2n.Tim79a
