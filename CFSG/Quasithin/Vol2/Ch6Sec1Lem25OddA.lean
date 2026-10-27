module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec3KGSylow
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.H13.OddSyl

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal)

@[expose] def OddSylowJ1 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsSporadic .J1 S → ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → ∀ (d : MulAut S) (r : ℕ), r.Prime →
      r ≠ 2 → orderOf d = r → P.map d.toMonoidHom = P → (∃ x ∈ P, d x ≠ x) →
      (∀ y ∈ Subgroup.normalizer (P : Set S), d y * y⁻¹ ∈ P) → False

@[expose] def OddSylowTits : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsTits S → ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → ∀ (d : MulAut S) (r : ℕ), r.Prime →
      r ≠ 2 → orderOf d = r → P.map d.toMonoidHom = P → (∃ x ∈ P, d x ≠ x) →
      (∀ y ∈ Subgroup.normalizer (P : Set S), d y * y⁻¹ ∈ P) → False

@[expose] def OddSylowJ2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    IsSporadic .J2 S → ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → ∀ (d : MulAut S) (r : ℕ), r.Prime →
      r ≠ 2 → orderOf d = r → P.map d.toMonoidHom = P → (∃ x ∈ P, d x ≠ x) →
      (∀ y ∈ Subgroup.normalizer (P : Set S), d y * y⁻¹ ∈ P) → r = 3 ∧ d ∈ innAut S

@[expose] def OddSylowD42 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Is3D4 2 1 S → ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → ∀ (d : MulAut S) (r : ℕ), r.Prime →
      r ≠ 2 → orderOf d = r → P.map d.toMonoidHom = P → (∃ x ∈ P, d x ≠ x) →
      (∀ y ∈ Subgroup.normalizer (P : Set S), d y * y⁻¹ ∈ P) → r = 7 ∧ d ∈ innAut S

variable {S : Type} [Group S]

theorem conj_injective (hS : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  have := hS
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
      exact absurd (Subgroup.mem_center_iff.1 ha b).symm hab
  intro g h hgh
  have hc : h⁻¹ * g ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : g * y * g⁻¹ = h * y * h⁻¹ := by
      simpa only [MulAut.conj_apply] using DFunLike.congr_fun hgh y
    calc y * (h⁻¹ * g) = h⁻¹ * (h * y * h⁻¹) * g := by group
      _ = h⁻¹ * (g * y * g⁻¹) * g := by rw [hy]
      _ = h⁻¹ * g * y := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem mul_conj_mul_inv (d : MulAut S) (x : S) :
    d * MulAut.conj x * d⁻¹ = MulAut.conj (d x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem relIndex_conj_range_sup_dvd (d : MulAut S) :
    (MulAut.conj : S →* MulAut S).range.relIndex
      ((MulAut.conj : S →* MulAut S).range ⊔ Subgroup.zpowers d) ∣ orderOf d := by
  have : (MulAut.conj : S →* MulAut S).range.Normal := inner_normal S
  rw [Subgroup.relIndex_sup_left, ← Nat.card_zpowers]
  exact Subgroup.relIndex_dvd_card _ _

theorem isSylowTwoOf_map_conj (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    {P : Subgroup S} (hP : IsSylowTwoOf P ⊤) {d : MulAut S} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : orderOf d = r) :
    IsSylowTwoOf (P.map (MulAut.conj : S →* MulAut S))
      ((MulAut.conj : S →* MulAut S).range ⊔ Subgroup.zpowers d) := by
  have hSI : P.map (MulAut.conj : S →* MulAut S) ≤ (MulAut.conj : S →* MulAut S).range :=
    Subgroup.map_le_range _ _
  refine ⟨hSI.trans le_sup_left, hP.2.1.map _, ?_⟩
  have h1 : (P.map (MulAut.conj : S →* MulAut S)).relIndex (MulAut.conj : S →* MulAut S).range =
      P.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
      Subgroup.relIndex_top_right]
  have h2 := relIndex_conj_range_sup_dvd d
  rw [hd] at h2
  have hP2 : ¬ 2 ∣ P.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hP.2.2
  change ¬ 2 ∣ (P.map (MulAut.conj : S →* MulAut S)).relIndex
    ((MulAut.conj : S →* MulAut S).range ⊔ Subgroup.zpowers d)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ hSI le_sup_left, h1]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
  · exact hP2 h
  · exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).1 (h.trans h2)).symm

theorem mem_normalizer_map_conj {P : Subgroup S} {d : MulAut S}
    (hdP : P.map d.toMonoidHom = P) :
    d ∈ Subgroup.normalizer
      ((P.map (MulAut.conj : S →* MulAut S) : Subgroup (MulAut S)) : Set (MulAut S)) := by
  have hmem : ∀ y, y ∈ P → d y ∈ P := fun y hy => by
    rw [← hdP]
    exact ⟨y, hy, rfl⟩
  have hmem' : ∀ y, y ∈ P → d⁻¹ y ∈ P := fun y hy => by
    rw [← hdP] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    change d⁻¹ (d z) ∈ P
    rw [MulAut.inv_apply_self]
    exact hz
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨d x, hmem x hx, (mul_conj_mul_inv d x).symm⟩
  · rintro ⟨y, hy, hyh⟩
    refine ⟨d⁻¹ y, hmem' y hy, ?_⟩
    rw [← mul_conj_mul_inv, hyh]
    group

theorem false_of_autOddNormCent [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hN : AutOddNormCent S) {P : Subgroup S}
    (hP : IsSylowTwoOf P ⊤) {d : MulAut S} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : orderOf d = r) (hdP : P.map d.toMonoidHom = P) (hx : ∃ x ∈ P, d x ≠ x) : False := by
  have hinj := conj_injective hS hna
  obtain ⟨x, hxP, hdx⟩ := hx
  have hodd : Odd (orderOf d) := by
    rw [hd]
    exact hr.odd_of_ne_two hr2
  have hc := hN ((MulAut.conj : S →* MulAut S).range ⊔ Subgroup.zpowers d)
    (P.map (MulAut.conj : S →* MulAut S)) le_sup_left (isSylowTwoOf_map_conj hinj hP hr hr2 hd) d
    ⟨mem_normalizer_map_conj hdP, Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩ hodd
    (MulAut.conj x) ⟨x, hxP, rfl⟩
  apply hdx
  apply hinj
  rw [← mul_conj_mul_inv, hc, mul_inv_cancel_right]

theorem mem_innAut_of_not_dvd {d : MulAut S} {r : ℕ} (hr : r.Prime) (hd : orderOf d = r)
    (hout : ¬ r ∣ Nat.card (Outer S)) : d ∈ innAut S := by
  set o : Outer S := QuotientGroup.mk d with ho
  have hop : o ^ r = 1 := by
    rw [ho, ← QuotientGroup.mk_pow, ← hd, pow_orderOf_eq_one, QuotientGroup.mk_one]
  rcases (Nat.dvd_prime hr).1 (orderOf_dvd_of_pow_eq_one hop) with h1 | h1
  · have hmem : d ∈ inner S :=
      (QuotientGroup.eq_one_iff (N := inner S) d).1 (orderOf_eq_one_iff.1 h1)
    exact hmem
  · exact absurd (h1 ▸ orderOf_dvd_natCard o) hout

theorem exists_conj_of_mem_innAut (hinj : Function.Injective (MulAut.conj : S →* MulAut S))
    {P : Subgroup S} {d : MulAut S} {r : ℕ} (hd : orderOf d = r) (hdP : P.map d.toMonoidHom = P)
    (hinn : d ∈ innAut S) :
    ∃ g ∈ Subgroup.normalizer (P : Set S), MulAut.conj g = d ∧ orderOf g = r := by
  obtain ⟨g, rfl⟩ := hinn
  refine ⟨g, ?_, rfl, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hdP]
      exact ⟨h, hh, MulAut.conj_apply g h⟩
    · intro hh
      rw [← hdP] at hh
      obtain ⟨z, hz, hzh⟩ := hh
      have hzh' : g * z * g⁻¹ = g * h * g⁻¹ := (MulAut.conj_apply g z).symm.trans hzh
      have hzeq : z = h := mul_left_cancel (mul_right_cancel hzh')
      exact hzeq ▸ hz
  · rw [← hd]
    exact (orderOf_injective _ hinj g).symm

theorem eq_three_of_card_four [Finite S] {P : Subgroup S} (hP4 : Nat.card P = 4) {d : MulAut S}
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hd : orderOf d = r) (hdP : P.map d.toMonoidHom = P)
    (hx : ∃ x ∈ P, d x ≠ x) : r = 3 := by
  have : Fact r.Prime := ⟨hr⟩
  have hmem : ∀ y, y ∈ P → d y ∈ P := fun y hy => by
    rw [← hdP]
    exact ⟨y, hy, rfl⟩
  have hmem' : ∀ y, y ∈ P → d⁻¹ y ∈ P := fun y hy => by
    rw [← hdP] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    change d⁻¹ (d z) ∈ P
    rw [MulAut.inv_apply_self]
    exact hz
  let σ : Equiv.Perm ↥P :=
    { toFun := fun y => ⟨d y, hmem y y.2⟩
      invFun := fun y => ⟨d⁻¹ y, hmem' y y.2⟩
      left_inv := fun y => Subtype.ext (MulAut.inv_apply_self S d y)
      right_inv := fun y => Subtype.ext (MulAut.apply_inv_self S d y) }
  have hσ : ∀ y : ↥P, ((σ y : ↥P) : S) = d y := fun y => rfl
  have hpow : ∀ (k : ℕ) (y : ↥P), (((σ ^ k) y : ↥P) : S) = (d ^ k) y := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [pow_zero, pow_zero]
      rfl
    | succ k ih =>
      intro y
      rw [pow_succ σ k, Equiv.Perm.mul_apply, ih, hσ, pow_succ d k, MulAut.mul_apply]
  have hσr : σ ^ r = 1 := by
    refine Equiv.ext fun y => Subtype.ext ?_
    rw [hpow, ← hd, pow_orderOf_eq_one]
    rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨x, hxP, hdx⟩ := hx
    intro h
    apply hdx
    exact congrArg (fun τ : Equiv.Perm ↥P => ((τ ⟨x, hxP⟩ : ↥P) : S)) h
  have hord : orderOf σ = r := orderOf_eq_prime hσr hσ1
  have h24 : r ∣ 2 ^ 3 * 3 := by
    have h := orderOf_dvd_natCard σ
    have h4 : Nat.factorial 4 = 2 ^ 3 * 3 := rfl
    rw [hord, Nat.card_perm, hP4, h4] at h
    exact h
  rcases (Nat.Prime.dvd_mul hr).1 h24 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)) hr2
  · exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h

end CFSG.Quasithin.H13.OddSyl
