module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H13.L42

open Matrix

abbrev V4 : Type := Fin 4 → ZMod 2

abbrev GL4 : Type := GL (Fin 4) (ZMod 2)

@[expose] def pm : Fin 9 → Matrix (Fin 4) (Fin 4) (ZMod 2) := ![
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0],
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1],
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0],
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1],
  !![1, 1, 0, 0; 1, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 0]]

@[expose] def InV1 (v : V4) : Prop := v 2 = 0 ∧ v 3 = 0

@[expose] def InV2 (v : V4) : Prop := v 0 = 0 ∧ v 1 = 0

instance : DecidablePred InV1 := fun v => by unfold InV1; infer_instance

instance : DecidablePred InV2 := fun v => by unfold InV2; infer_instance

@[expose] def Mixed (v : V4) : Prop := ¬ InV1 v ∧ ¬ InV2 v

instance : DecidablePred Mixed := fun v => by unfold Mixed; infer_instance

theorem pm_mul : ∀ i j : Fin 9, ∃ k : Fin 9, pm i * pm j = pm k := by decide +kernel

theorem pm_facts : (∀ i : Fin 9, pm i * pm i * pm i = 1) ∧ pm 0 = 1 ∧ pm 2 = pm 1 * pm 1 ∧
    pm 1 ≠ 1 := by
  decide +kernel

theorem A1_mul : ∀ i j : Fin 9, i.val < 3 → j.val < 3 →
    ∃ k : Fin 9, k.val < 3 ∧ pm i * pm j = pm k := by
  decide +kernel

theorem fixed_gens : ∀ v : V4, (pm 1 *ᵥ v = v ↔ InV1 v) ∧ (pm 2 *ᵥ v = v ↔ InV1 v) ∧
    (pm 3 *ᵥ v = v ↔ InV2 v) ∧ (pm 6 *ᵥ v = v ↔ InV2 v) := by
  decide +kernel

theorem fixed_cases : ∀ k : Fin 9, ∀ v : V4, (v ≠ 0 ∧ pm k *ᵥ v = v) →
    k.val < 3 ∨ k = 3 ∨ k = 6 := by
  decide +kernel

theorem P0_mixed : ∀ k : Fin 9, ∀ v : V4, Mixed v → Mixed (pm k *ᵥ v) := by decide +kernel

theorem trans_mixed : ∀ w m : V4, (Mixed w ∧ Mixed m) → ∃ k : Fin 9, pm k *ᵥ w = m := by
  decide +kernel

theorem pair_N : ∀ x y : V4,
    (x ≠ 0 ∧ ¬ Mixed x ∧ y ≠ 0 ∧ ¬ Mixed y ∧ x ≠ y ∧ ¬ Mixed (x + y)) →
    (InV1 x ∧ InV1 y) ∨ (InV2 x ∧ InV2 y) := by
  decide +kernel

theorem basic_V : (∀ v : V4, InV1 v → InV2 v → v = 0) ∧ (∀ v : V4, InV1 v → ¬ Mixed v) ∧
    (∀ v : V4, InV2 v → ¬ Mixed v) ∧ (∀ x y : V4, InV1 x → InV1 y → InV1 (x + y)) ∧
    (∀ x y : V4, InV2 x → InV2 y → InV2 (x + y)) := by
  decide +kernel

@[expose] def proj1 (w : V4) : V4 := ![w 0, w 1, 0, 0]

@[expose] def proj2 (w : V4) : V4 := ![0, 0, w 2, w 3]

@[expose] def u1 (w : V4) : V4 := if w 0 = 1 ∧ w 1 = 0 then ![0, 1, 0, 0] else ![1, 0, 0, 0]

@[expose] def u2 (w : V4) : V4 := if w 2 = 1 ∧ w 3 = 0 then ![0, 0, 0, 1] else ![0, 0, 1, 0]

theorem basis_facts : ∀ w : V4, Mixed w →
    w = proj1 w + proj2 w ∧ InV1 (proj1 w) ∧ InV1 (u1 w) ∧ InV2 (proj2 w) ∧ InV2 (u2 w) ∧
    proj1 w ≠ 0 ∧ u1 w ≠ 0 ∧ proj1 w + u1 w ≠ 0 ∧ u1 w ≠ proj1 w ∧
    proj2 w ≠ 0 ∧ u2 w ≠ 0 ∧ proj2 w + u2 w ≠ 0 ∧ u2 w ≠ proj2 w ∧
    ∀ v : V4, ∃ c : Fin 4 → ZMod 2,
      v = c 0 • proj1 w + c 1 • u1 w + c 2 • proj2 w + c 3 • u2 w := by
  decide +kernel

theorem card_NN : (Finset.univ.filter fun p : V4 × V4 =>
    (p.1 ≠ 0 ∧ ¬ Mixed p.1) ∧ (p.2 ≠ 0 ∧ ¬ Mixed p.2)).card = 36 := by
  decide +kernel

theorem decomp_unique {x x' y y' : V4} (hx : InV1 x) (hx' : InV1 x') (hy : InV2 y)
    (hy' : InV2 y') (h : x + y = x' + y') : x = x' ∧ y = y' := by
  obtain ⟨hx2, hx3⟩ := hx
  obtain ⟨hx'2, hx'3⟩ := hx'
  obtain ⟨hy0, hy1⟩ := hy
  obtain ⟨hy'0, hy'1⟩ := hy'
  have key : ∀ i, x i + y i = x' i + y' i := fun i => congrFun h i
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  rw [hy0, hy'0, add_zero, add_zero] at k0
  rw [hy1, hy'1, add_zero, add_zero] at k1
  rw [hx2, hx'2, zero_add, zero_add] at k2
  rw [hx3, hx'3, zero_add, zero_add] at k3
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · fin_cases i
    · exact k0
    · exact k1
    · exact hx2.trans hx'2.symm
    · exact hx3.trans hx'3.symm
  · fin_cases i
    · exact hy0.trans hy'0.symm
    · exact hy1.trans hy'1.symm
    · exact k2
    · exact k3

@[expose] def pu (k : Fin 9) : GL4 :=
  ⟨pm k, pm k * pm k, by rw [← mul_assoc]; exact pm_facts.1 k, pm_facts.1 k⟩

@[expose] def P0 : Subgroup GL4 where
  carrier := {x | ∃ k : Fin 9, (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) = pm k}
  one_mem' := ⟨0, pm_facts.2.1.symm⟩
  mul_mem' := by
    rintro a b ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hk⟩ := pm_mul i j
    exact ⟨k, by rw [Units.val_mul, hi, hj, hk]⟩
  inv_mem' := by
    rintro a ⟨i, hi⟩
    obtain ⟨k, hk⟩ := pm_mul i i
    refine ⟨k, ?_⟩
    have h3 : a * a * a = 1 := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hi, pm_facts.1 i, Units.val_one])
    have h2 : a * a = a⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [← h2, Units.val_mul, hi, hk]

@[expose] def A1 : Subgroup GL4 where
  carrier := {x | ∃ k : Fin 9, k.val < 3 ∧ (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) = pm k}
  one_mem' := ⟨0, by decide, pm_facts.2.1.symm⟩
  mul_mem' := by
    rintro a b ⟨i, hi3, hi⟩ ⟨j, hj3, hj⟩
    obtain ⟨k, hk3, hk⟩ := A1_mul i j hi3 hj3
    exact ⟨k, hk3, by rw [Units.val_mul, hi, hj, hk]⟩
  inv_mem' := by
    rintro a ⟨i, hi3, hi⟩
    obtain ⟨k, hk3, hk⟩ := A1_mul i i hi3 hi3
    refine ⟨k, hk3, ?_⟩
    have h3 : a * a * a = 1 := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hi, pm_facts.1 i, Units.val_one])
    have h2 : a * a = a⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [← h2, Units.val_mul, hi, hk]

theorem A1_le_P0 : A1 ≤ P0 := fun _ ⟨k, _, hk⟩ => ⟨k, hk⟩

theorem pu_mem_P0 (k : Fin 9) : pu k ∈ P0 := ⟨k, rfl⟩

theorem conj_A1_le {g : GL4} (hg : g * pu 1 * g⁻¹ ∈ A1) {h : GL4} (hh : h ∈ A1) :
    g * h * g⁻¹ ∈ A1 := by
  obtain ⟨i, hi3, hi⟩ := hh
  have hcases : h = 1 ∨ h = pu 1 ∨ h = pu 1 * pu 1 := by
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl | rfl
    · exact Or.inl (Units.ext (hi.trans pm_facts.2.1))
    · exact Or.inr (Or.inl (Units.ext hi))
    · exact Or.inr (Or.inr (Units.ext (by rw [Units.val_mul, hi, pm_facts.2.2.1]; rfl)))
  rcases hcases with rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact A1.one_mem
  · exact hg
  · have : g * (pu 1 * pu 1) * g⁻¹ = (g * pu 1 * g⁻¹) * (g * pu 1 * g⁻¹) := by group
    rw [this]
    exact A1.mul_mem hg hg

theorem mem_normalizer_A1 {g : GL4} (hg : g * pu 1 * g⁻¹ ∈ A1)
    (hg' : g⁻¹ * pu 1 * g⁻¹⁻¹ ∈ A1) : g ∈ Subgroup.normalizer (A1 : Set GL4) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_A1_le hg hh, fun hh => ?_⟩
  have := conj_A1_le hg' hh
  rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this

theorem smul_def (x : GL4) (v : V4) : x • v = (x : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v := rfl

theorem ext_of_smul {x y : GL4} (h : ∀ v : V4, x • v = y • v) : x = y := by
  apply Units.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [smul_def, Matrix.mulVec_single] using this

theorem exists_fixed {S : Subgroup GL4} (hS : IsPGroup 2 S) :
    ∃ w : V4, w ≠ 0 ∧ ∀ s ∈ S, s • w = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hS.card_modEq_card_fixedPoints V4
  by_contra hno
  push Not at hno
  have hfix : MulAction.fixedPoints ↥S V4 = {0} := by
    ext v
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hv
      by_contra hv0
      obtain ⟨s, hs, hsv⟩ := hno v hv0
      exact hsv (hv ⟨s, hs⟩)
    · rintro rfl s
      exact smul_zero _
  have h1 : Nat.card ↥({0} : Set V4) = 1 := Nat.card_unique
  have h16 : Nat.card V4 = 16 := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card]
  rw [hfix, h1, h16] at hmod
  exact absurd hmod (by decide)

theorem fc1_core {S : Subgroup GL4} (hS : IsPGroup 2 S) (hS36 : 36 < Nat.card S)
    (hPS : ∀ s ∈ S, ∀ x ∈ P0, ∃ y ∈ P0, ∃ s' ∈ S, s * x = y * s')
    (hirr : ∀ U : Subgroup GL4, U ≤ P0 →
      S ⊓ Subgroup.normalizer (P0 : Set GL4) ≤ Subgroup.normalizer (U : Set GL4) →
      U = ⊥ ∨ U = P0) : False := by
  obtain ⟨hcube, hpm0, hpm2, hpm1⟩ := pm_facts
  obtain ⟨hV12, hV1M, hV2M, hV1add, hV2add⟩ := basic_V
  obtain ⟨r, ⟨hrS, hrN⟩, hrA⟩ : ∃ r ∈ S ⊓ Subgroup.normalizer (P0 : Set GL4),
      r * pu 1 * r⁻¹ ∉ A1 := by
    by_contra hno
    push Not at hno
    have hnorm : S ⊓ Subgroup.normalizer (P0 : Set GL4) ≤
        Subgroup.normalizer (A1 : Set GL4) := fun r hr =>
      mem_normalizer_A1 (hno r hr) (hno r⁻¹ (inv_mem hr))
    rcases hirr A1 A1_le_P0 hnorm with h | h
    · have h1 : pu 1 ∈ A1 := ⟨1, by decide, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact hpm1 (by have := congrArg Units.val h1; simpa [pu] using this)
    · have h3 : pu 3 ∈ A1 := h ▸ pu_mem_P0 3
      obtain ⟨k, hk3, hk⟩ := h3
      have : pm 3 = pm k := hk
      have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
      rcases hk' with rfl | rfl | rfl <;> revert this <;> decide +kernel
  have hc2 : ∀ v : V4, (r * pu 1 * r⁻¹) • v = v ↔ InV2 v := by
    have hmem : r * pu 1 * r⁻¹ ∈ P0 := (Subgroup.mem_normalizer_iff.mp hrN _).mp (pu_mem_P0 1)
    obtain ⟨k, hk⟩ := hmem
    have he0 : (pu 1) • (![1, 0, 0, 0] : V4) = ![1, 0, 0, 0] := by
      rw [smul_def]
      exact ((fixed_gens _).1).mpr (by decide)
    have hfix : (r * pu 1 * r⁻¹) • (r • (![1, 0, 0, 0] : V4)) = r • ![1, 0, 0, 0] := by
      rw [mul_smul, mul_smul, inv_smul_smul, he0]
    have hne : r • (![1, 0, 0, 0] : V4) ≠ 0 := by
      intro h0
      have : (![1, 0, 0, 0] : V4) = 0 := by
        rw [← inv_smul_smul r (![1, 0, 0, 0] : V4), h0, smul_zero]
      exact absurd this (by decide)
    rw [smul_def, hk] at hfix
    rcases fixed_cases k _ ⟨hne, hfix⟩ with h | rfl | rfl
    · exact absurd ⟨k, h, hk⟩ hrA
    · intro v
      rw [smul_def, hk]
      exact (fixed_gens v).2.2.1
    · intro v
      rw [smul_def, hk]
      exact (fixed_gens v).2.2.2
  obtain ⟨w, hw0, hwS⟩ := exists_fixed hS
  have hrw : r • w = w := hwS r hrS
  have hriw : r⁻¹ • w = w := by rw [← hrw, inv_smul_smul, hrw]
  have hwM : Mixed w := by
    refine ⟨fun h1 => hw0 (hV12 w h1 ?_), fun h2 => hw0 (hV12 w ?_ h2)⟩
    · rw [← hc2, mul_smul, mul_smul, hriw]
      have : (pu 1) • w = w := by rw [smul_def]; exact ((fixed_gens w).1).mpr h1
      rw [this, hrw]
    · have h := (hc2 w).mpr h2
      rw [mul_smul, mul_smul, hriw] at h
      have h' : (pu 1) • w = w := by
        have := congrArg (fun v => r⁻¹ • v) h
        simpa only [inv_smul_smul, hriw] using this
      rw [smul_def] at h'
      exact ((fixed_gens w).1).mp h'
  have hSM : ∀ s ∈ S, ∀ m : V4, Mixed m → Mixed (s • m) := by
    intro s hs m hm
    obtain ⟨k, hk⟩ := trans_mixed w m ⟨hwM, hm⟩
    obtain ⟨y, ⟨k', hk'⟩, s', hs', hsy⟩ := hPS s hs (pu k) (pu_mem_P0 k)
    have : s • m = y • w := by
      rw [← hk, show pm k *ᵥ w = pu k • w from rfl, ← mul_smul, hsy, mul_smul, hwS s' hs']
    rw [this, smul_def, hk']
    exact P0_mixed k' w hwM
  have hSN : ∀ s ∈ S, ∀ n : V4, n ≠ 0 → ¬ Mixed n → s • n ≠ 0 ∧ ¬ Mixed (s • n) := by
    intro s hs n hn hnM
    refine ⟨fun h0 => hn ?_, fun hM => hnM ?_⟩
    · rw [← inv_smul_smul s n, h0, smul_zero]
    · have := hSM s⁻¹ (inv_mem hs) _ hM
      rwa [inv_smul_smul] at this
  obtain ⟨hwdec, hw1, hu1, hw2, hu2, hw10, hu10, hwu10, hu1w, hw20, hu20, hwu20, hu2w, hspan⟩ :=
    basis_facts w hwM
  set w₁ := proj1 w
  set w₂ := proj2 w
  have hside : ∀ s ∈ S, ((InV1 (s • w₁) ∧ InV1 (s • u1 w)) ∨ (InV2 (s • w₁) ∧ InV2 (s • u1 w))) ∧
      ((InV1 (s • w₂) ∧ InV1 (s • u2 w)) ∨ (InV2 (s • w₂) ∧ InV2 (s • u2 w))) ∧
      s • w₁ + s • w₂ = w := by
    intro s hs
    refine ⟨pair_N _ _ ⟨(hSN s hs _ hw10 (hV1M _ hw1)).1, (hSN s hs _ hw10 (hV1M _ hw1)).2,
        (hSN s hs _ hu10 (hV1M _ hu1)).1, (hSN s hs _ hu10 (hV1M _ hu1)).2,
        fun h => hu1w (smul_left_cancel s h).symm, ?_⟩,
      pair_N _ _ ⟨(hSN s hs _ hw20 (hV2M _ hw2)).1, (hSN s hs _ hw20 (hV2M _ hw2)).2,
        (hSN s hs _ hu20 (hV2M _ hu2)).1, (hSN s hs _ hu20 (hV2M _ hu2)).2,
        fun h => hu2w (smul_left_cancel s h).symm, ?_⟩, ?_⟩
    · rw [← smul_add]
      exact (hSN s hs _ hwu10 (hV1M _ (hV1add _ _ hw1 hu1))).2
    · rw [← smul_add]
      exact (hSN s hs _ hwu20 (hV2M _ (hV2add _ _ hw2 hu2))).2
    · rw [← smul_add, ← hwdec, hwS s hs]
  have hdet : ∀ s ∈ S, ∀ s' ∈ S, s • u1 w = s' • u1 w → s • w₁ = s' • w₁ ∧ s • w₂ = s' • w₂ := by
    intro s hs s' hs' hu
    obtain ⟨hs1, hs2, hsw⟩ := hside s hs
    obtain ⟨hs'1, hs'2, hs'w⟩ := hside s' hs'
    have hsum : s • w₁ + s • w₂ = s' • w₁ + s' • w₂ := hsw.trans hs'w.symm
    have hdiff : ∀ t ∈ S, ¬ (InV1 (t • w₁) ∧ InV1 (t • w₂)) ∧
        ¬ (InV2 (t • w₁) ∧ InV2 (t • w₂)) := by
      intro t ht
      obtain ⟨-, -, htw⟩ := hside t ht
      refine ⟨fun ⟨h1, h2⟩ => hwM.1 (htw ▸ hV1add _ _ h1 h2),
        fun ⟨h1, h2⟩ => hwM.2 (htw ▸ hV2add _ _ h1 h2)⟩
    rcases hs1 with ⟨hsw1, hsu1⟩ | ⟨hsw1, hsu1⟩
    ·
      have hs'w1 : InV1 (s' • w₁) := by
        rcases hs'1 with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exact absurd (hV12 _ (hu ▸ hsu1) h) (hSN s' hs' _ hu10 (hV1M _ hu1)).1
      have hsw2 : InV2 (s • w₂) := by
        rcases hs2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd ⟨hsw1, h⟩ (hdiff s hs).1
        · exact h
      have hs'w2 : InV2 (s' • w₂) := by
        rcases hs'2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd ⟨hs'w1, h⟩ (hdiff s' hs').1
        · exact h
      exact decomp_unique hsw1 hs'w1 hsw2 hs'w2 hsum
    ·
      have hs'w1 : InV2 (s' • w₁) := by
        rcases hs'1 with ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd (hV12 _ h (hu ▸ hsu1)) (hSN s' hs' _ hu10 (hV1M _ hu1)).1
        · exact h
      have hsw2 : InV1 (s • w₂) := by
        rcases hs2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd ⟨hsw1, h⟩ (hdiff s hs).2
      have hs'w2 : InV1 (s' • w₂) := by
        rcases hs'2 with ⟨h, -⟩ | ⟨h, -⟩
        · exact h
        · exact absurd ⟨hs'w1, h⟩ (hdiff s' hs').2
      have := decomp_unique hsw2 hs'w2 hsw1 hs'w1 (by rw [add_comm, hsum, add_comm])
      exact ⟨this.2, this.1⟩
  have hinj : ∀ s ∈ S, ∀ s' ∈ S, s • u1 w = s' • u1 w → s • u2 w = s' • u2 w → s = s' := by
    intro s hs s' hs' h1 h2
    obtain ⟨hw1', hw2'⟩ := hdet s hs s' hs' h1
    apply ext_of_smul
    intro v
    obtain ⟨c, hc⟩ := hspan v
    rw [hc, smul_add, smul_add, smul_add, smul_add, smul_add, smul_add, smul_comm s (c 0),
      smul_comm s (c 1), smul_comm s (c 2), smul_comm s (c 3), smul_comm s' (c 0),
      smul_comm s' (c 1), smul_comm s' (c 2), smul_comm s' (c 3), hw1', hw2', h1, h2]
  set NN := Finset.univ.filter fun p : V4 × V4 =>
    (p.1 ≠ 0 ∧ ¬ Mixed p.1) ∧ (p.2 ≠ 0 ∧ ¬ Mixed p.2) with hNN
  let f : ↥S → ↥NN := fun s => ⟨((s : GL4) • u1 w, (s : GL4) • u2 w), by
    rw [hNN, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hSN s s.2 _ hu10 (hV1M _ hu1), hSN s s.2 _ hu20 (hV2M _ hu2)⟩⟩
  have hf : Function.Injective f := by
    intro s s' h
    have h' := congrArg Subtype.val h
    simp only [f, Prod.mk.injEq] at h'
    exact Subtype.ext (hinj s s.2 s' s'.2 h'.1 h'.2)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_finsetCard, hNN, card_NN] at hle
  omega

@[expose] def FC1Hyp {A : Type} [Group A] (P S : Subgroup A) : Prop :=
  Nat.card P = 9 ∧ IsPGroup 2 S ∧ 36 < Nat.card S ∧
    (∀ s ∈ S, ∀ x ∈ P, ∃ y ∈ P, ∃ s' ∈ S, s * x = y * s') ∧
    ∀ U : Subgroup A, U ≤ P → S ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (U : Set A) → U = ⊥ ∨ U = P

theorem FC1Hyp.map {A B : Type} [Group A] [Group B] (φ : A ≃* B) {P S : Subgroup A}
    (h : FC1Hyp P S) : FC1Hyp (P.map φ.toMonoidHom) (S.map φ.toMonoidHom) := by
  obtain ⟨hP9, hS, hS36, hPS, hirr⟩ := h
  refine ⟨by rw [Subgroup.card_map_of_injective φ.injective, hP9], hS.map _,
    by rw [Subgroup.card_map_of_injective φ.injective]; exact hS36, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, s', hs', h⟩ := hPS s hs x hx
    refine ⟨φ y, ⟨y, hy, rfl⟩, φ s', ⟨s', hs', rfl⟩, ?_⟩
    change φ s * φ x = φ y * φ s'
    rw [← map_mul, ← map_mul, h]
  · intro U' hU' hN
    have hUP : U'.comap φ.toMonoidHom ≤ P := fun x hx => by
      obtain ⟨y, hy, hyx⟩ := hU' hx
      rwa [φ.injective hyx] at hy
    have hN' : S ⊓ Subgroup.normalizer (P : Set A) ≤
        Subgroup.normalizer ((U'.comap φ.toMonoidHom : Subgroup A) : Set A) := by
      rintro t ⟨htS, htN⟩
      have h1 : φ t ∈ S.map φ.toMonoidHom ⊓
          Subgroup.normalizer ((P.map φ.toMonoidHom : Subgroup B) : Set B) := by
        refine ⟨⟨t, htS, rfl⟩, ?_⟩
        rw [← Subgroup.map_equiv_normalizer_eq]
        exact ⟨t, htN, rfl⟩
      have h2 := Subgroup.mem_normalizer_iff.mp (hN h1)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_comap, Subgroup.mem_comap, h2 (φ.toMonoidHom x)]
      simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    have hsurj : (U'.comap φ.toMonoidHom).map φ.toMonoidHom = U' :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective U'
    rcases hirr _ hUP hN' with h | h
    · left
      rw [← hsurj, h, Subgroup.map_bot]
    · right
      rw [← hsurj, h]

theorem card_P0 : Nat.card P0 = 9 := by
  have hinj : ∀ i j : Fin 9, pm i = pm j → i = j := by decide +kernel
  have hbij : Function.Bijective (fun k : Fin 9 => (⟨pu k, pu_mem_P0 k⟩ : P0)) := by
    refine ⟨fun i j h => hinj i j
      (congrArg (fun x : ↥P0 => ((x : GL4) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h), ?_⟩
    rintro ⟨x, k, hk⟩
    exact ⟨k, Subtype.ext (Units.ext hk.symm)⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_GL4 : Nat.card GL4 = 20160 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show Nat.card (GL (Fin 4) (ZMod 2)) = 20160
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 4, ZMod.card]
  simp [Fin.prod_univ_four]

theorem exists_conj_P0 {P : Subgroup GL4} (hP9 : Nat.card P = 9) :
    ∃ g : GL4, P.map (MulAut.conj g).toMonoidHom = P0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : ∀ H : Subgroup GL4, Nat.card H = 9 → ¬ 3 ∣ H.index := by
    intro H hH h3
    have h := H.card_mul_index
    rw [hH, card_GL4] at h
    omega
  have hp : ∀ H : Subgroup GL4, Nat.card H = 9 → IsPGroup 3 H := fun H hH =>
    IsPGroup.of_card (n := 2) (by rw [hH]; norm_num)
  let R : Sylow 3 GL4 := (hp P hP9).toSylow (hidx P hP9)
  let Q : Sylow 3 GL4 := (hp P0 card_P0).toSylow (hidx P0 card_P0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GL4 R Q
  refine ⟨g, ?_⟩
  have hQ : ((g • R : Sylow 3 GL4) : Subgroup GL4) = P0 := by rw [hg]; rfl
  rw [Sylow.coe_subgroup_smul] at hQ
  ext x
  rw [← hQ]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ hy
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (Subgroup.mem_smul_pointwise_iff_exists x (MulAut.conj g) _).mp hx
    exact ⟨y, hy, hyx⟩

theorem fc1 {A : Type} [Group A] (e : A ≃* GL4) {P S : Subgroup A} (h : FC1Hyp P S) : False := by
  have h' := h.map e
  obtain ⟨g, hg⟩ := exists_conj_P0 h'.1
  have h'' := h'.map (MulAut.conj g)
  rw [hg] at h''
  obtain ⟨-, hS, hS36, hPS, hirr⟩ := h''
  exact fc1_core hS hS36 hPS hirr

end CFSG.Quasithin.H13.L42
