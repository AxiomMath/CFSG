module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Quasithin.SBd11

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem mem_sylow_of_mem_normalizer {Q : Sylow 3 X} {x : X}
    (hx : IsPGroup 3 (Subgroup.zpowers x))
    (hN : x ∈ Subgroup.normalizer (Q : Set X)) : x ∈ (Q : Subgroup X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : IsPGroup 3 ((Subgroup.zpowers x) ⊔ (Q : Subgroup X) : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hx Q.isPGroup' (by rwa [Subgroup.zpowers_le])
  have h2 : (Subgroup.zpowers x) ⊔ (Q : Subgroup X) ≤ Q := (Q.is_maximal' h1 le_sup_right).le
  exact h2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem pow_dvd_card_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p X) {k : ℕ}
    (h : p ^ k ∣ Nat.card X) : p ^ k ∣ Nat.card P := by
  have h1 := Subgroup.card_mul_index (P : Subgroup X)
  have hnd : ¬ p ∣ (P : Subgroup X).index := P.not_dvd_index
  have hcop : Nat.Coprime (p ^ k) (P : Subgroup X).index :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd)
  rw [← h1] at h
  exact hcop.dvd_of_dvd_mul_right h

theorem exists_normal_three_of_index (P : Sylow 3 X) (h9 : 9 ∣ Nat.card P)
    {W : Subgroup X} (hW : W ≤ Subgroup.normalizer (P : Set X)) (hidx : W.index ∣ 8) :
    ∃ R : Subgroup X, R ≠ ⊥ ∧ R.Normal ∧ IsPGroup 3 R := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : Nat.card (Sylow 3 X) ∣ 8 := by
    rw [Sylow.card_eq_index_normalizer P]
    exact (Subgroup.index_dvd_of_le hW).trans hidx
  have hmod := card_sylow_modEq_one 3 X
  have hn14 : Nat.card (Sylow 3 X) = 1 ∨ Nat.card (Sylow 3 X) = 4 := by
    obtain ⟨i, hi, hni⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card (Sylow 3 X) ∣ 2 ^ 3 by simpa using hn)
    rw [hni] at hmod ⊢
    interval_cases i <;> simp_all [Nat.ModEq]
  have hperm : Nat.card (Equiv.Perm (Sylow 3 X)) ∣ 24 := by
    rw [Nat.card_perm]
    rcases hn14 with h | h <;> rw [h] <;> decide
  let φ : ↥(P : Subgroup X) →* Equiv.Perm (Sylow 3 X) := MulAction.toPermHom _ _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 P.isPGroup'
  have hr1 : Nat.card φ.range ∣ 3 ^ k := hk ▸ Subgroup.card_range_dvd φ
  have hr2 : Nat.card φ.range ∣ 3 * 8 :=
    (Subgroup.card_subgroup_dvd_card φ.range).trans hperm
  have hr3 : Nat.card φ.range ∣ 3 := by
    have hcop : Nat.Coprime (Nat.card φ.range) 8 :=
      Nat.Coprime.coprime_dvd_left hr1 (Nat.Coprime.pow_left k (by norm_num))
    exact hcop.dvd_of_dvd_mul_right hr2
  have hker : 1 < Nat.card φ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : 9 ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos h9
    have h4 : Nat.card φ.range ≤ 3 := Nat.le_of_dvd (by norm_num) hr3
    have h5 : 0 < Nat.card φ.range := Nat.card_pos
    by_contra hc
    push Not at hc
    have h6 : Nat.card φ.ker ≤ 1 := hc
    have : Nat.card φ.ker * Nat.card φ.range ≤ 1 * 3 := Nat.mul_le_mul h6 h4
    omega
  have hker' : φ.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hker
    omega
  obtain ⟨⟨y, hyK⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker'
  have hy1' : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  have hfix : ∀ Q : Sylow 3 X, (y : X) • Q = Q := by
    intro Q
    have h1 : φ y = 1 := hyK
    have h2 := congrArg (fun f => f Q) h1
    simpa [φ, Subgroup.smul_def] using h2
  have hyp : IsPGroup 3 (Subgroup.zpowers (y : X)) :=
    P.isPGroup'.to_le (Subgroup.zpowers_le.2 y.2)
  have hyQ : ∀ Q : Sylow 3 X, (y : X) ∈ (Q : Subgroup X) := fun Q =>
    mem_sylow_of_mem_normalizer hyp (Sylow.smul_eq_iff_mem_normalizer.1 (hfix Q))
  have hconj : ∀ g : X, g * (y : X) * g⁻¹ ∈ (P : Subgroup X) := by
    intro g
    have h := hyQ (g⁻¹ • P)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h
    obtain ⟨p, hp, hpy⟩ := h
    have : g * (y : X) * g⁻¹ = p := by
      have h2 : g⁻¹ * p * g = y := by simpa [MulAut.conj_apply] using hpy
      rw [← h2]
      group
    rw [this]
    exact hp
  refine ⟨Subgroup.normalClosure {(y : X)}, ?_, inferInstance, ?_⟩
  · intro h
    have : (y : X) ∈ Subgroup.normalClosure {(y : X)} := Subgroup.subset_normalClosure rfl
    rw [h, Subgroup.mem_bot] at this
    exact hy1' this
  · refine P.isPGroup'.to_le ?_
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    rw [← hg]
    exact hconj g

theorem exists_normal_three_of_card_dvd (P : Sylow 3 X) (h9 : 9 ∣ Nat.card P)
    {Z : Subgroup X} (hZ : IsPGroup 2 Z)
    (hZP : ∀ z ∈ Z, ∀ x ∈ (P : Subgroup X), z * x = x * z)
    (hcard : Nat.card X ∣ 8 * Nat.card Z * Nat.card P) :
    ∃ R : Subgroup X, R ≠ ⊥ ∧ R.Normal ∧ IsPGroup 3 R := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hconj : ∀ z ∈ Z, ∀ x ∈ (P : Subgroup X), z * x * z⁻¹ = x := fun z hz x hx => by
    rw [hZP z hz x hx]
    group
  have hWN : (P : Subgroup X) ⊔ Z ≤ Subgroup.normalizer (P : Set X) := by
    refine sup_le Subgroup.le_normalizer (fun z hz => ?_)
    change z ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hconj z hz n hn]
      exact hn
    · intro hn
      have h2 := hconj z⁻¹ (Z.inv_mem hz) _ hn
      have h3 : z⁻¹ * (z * n * z⁻¹) * z⁻¹⁻¹ = n := by group
      rw [h3] at h2
      rw [h2]
      exact hn
  have hcop : Nat.Coprime (Nat.card P) (Nat.card Z) :=
    IsPGroup.coprime_card_of_ne 3 2 (by norm_num) (P : Subgroup X) Z P.isPGroup' hZ
  have hdvdW : Nat.card P * Nat.card Z ∣ Nat.card ((P : Subgroup X) ⊔ Z : Subgroup X) :=
    hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le le_sup_left)
      (Subgroup.card_dvd_of_le le_sup_right)
  have hidx : ((P : Subgroup X) ⊔ Z).index ∣ 8 := by
    have h1 := Subgroup.card_mul_index ((P : Subgroup X) ⊔ Z)
    have hpos : 0 < Nat.card P * Nat.card Z := Nat.mul_pos Nat.card_pos Nat.card_pos
    have h2 : (Nat.card P * Nat.card Z) * ((P : Subgroup X) ⊔ Z).index ∣
        (Nat.card P * Nat.card Z) * 8 := by
      calc (Nat.card P * Nat.card Z) * ((P : Subgroup X) ⊔ Z).index
          ∣ Nat.card ((P : Subgroup X) ⊔ Z : Subgroup X) * ((P : Subgroup X) ⊔ Z).index :=
            Nat.mul_dvd_mul_right hdvdW _
        _ = Nat.card X := h1
        _ ∣ 8 * Nat.card Z * Nat.card P := hcard
        _ = (Nat.card P * Nat.card Z) * 8 := by ring
    exact Nat.dvd_of_mul_dvd_mul_left hpos h2
  exact exists_normal_three_of_index P h9 hWN hidx

end CFSG.Quasithin.SBd11
