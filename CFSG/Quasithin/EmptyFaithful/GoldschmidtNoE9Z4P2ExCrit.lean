module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Loc

public section

namespace CFSG.Quasithin

namespace E9P2.ExCrit

section Counting

variable {X : Type} [Group X]

theorem card_modEq_one [Finite X] {D E : Subgroup X} (hE : IsPGroup 3 ↥E)
    (hnorm : ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D)
    (hfix : ∀ d ∈ D, (∀ e ∈ E, e * d * e⁻¹ = d) → d = 1) : Nat.card D ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : MulAction ↥E ↥D :=
    { smul := fun e d => ⟨(e : X) * (d : X) * (e : X)⁻¹, hnorm e e.2 d d.2⟩
      one_smul := fun d => Subtype.ext (by
        show ((1 : ↥E) : X) * (d : X) * ((1 : ↥E) : X)⁻¹ = d
        simp)
      mul_smul := fun a b d => Subtype.ext (by
        show ((a * b : ↥E) : X) * (d : X) * ((a * b : ↥E) : X)⁻¹ =
          (a : X) * ((b : X) * (d : X) * (b : X)⁻¹) * (a : X)⁻¹
        simp [mul_assoc]) }
  have hmod := hE.card_modEq_card_fixedPoints ↥D
  have hfp : MulAction.fixedPoints ↥E ↥D = {1} := by
    ext d
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hd
      apply Subtype.ext
      refine hfix d d.2 fun e he => ?_
      exact congrArg Subtype.val (hd ⟨e, he⟩)
    · rintro rfl g
      exact Subtype.ext (by
        show (g : X) * 1 * (g : X)⁻¹ = 1
        simp)
  have hc1 : Nat.card ↥({1} : Set ↥D) = 1 := by simp
  rwa [hfp, hc1] at hmod

theorem even_of_two_pow_modEq {d : ℕ} (h : 2 ^ d ≡ 1 [MOD 3]) : Even d := by
  rcases Nat.even_or_odd d with he | ⟨a, rfl⟩
  · exact he
  · exfalso
    have h2 : 2 ^ (2 * a + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h1 : 2 ^ (2 * a + 1) % 3 = 1 % 3 := h
    omega

theorem exists_pow_involution {x : X} (hx : x ≠ 1) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    ∃ n : ℕ, x ^ n * x ^ n = 1 ∧ x ^ n ≠ 1 := by
  induction k with
  | zero => exact absurd (by simpa using hk) hx
  | succ k ih =>
    by_cases h : x ^ 2 ^ k = 1
    · exact ih h
    · refine ⟨2 ^ k, ?_, h⟩
      rw [← pow_add, ← two_mul, ← pow_succ']
      exact hk

end Counting

section Quotient

variable {X : Type} [Group X]

theorem card_le_two_mul {Th R L : Subgroup X} (hRT : R ≤ Th)
    (φ : ↥Th →* Multiplicative (ZMod 4)) (hφ : ∀ x : ↥Th, φ x = 1 ↔ (x : X) ∈ R)
    (hgen : Subgroup.closure {x : X | x ∈ Th ⊓ L ∧ x * x = 1} = Th ⊓ L) :
    Nat.card ↥(Th ⊓ L) ≤ 2 * Nat.card ↥(R ⊓ L) := by
  have hDU : R ⊓ L ≤ Th ⊓ L := inf_le_inf_right L hRT
  let ψ : ↥(Th ⊓ L) →* Multiplicative (ZMod 4) := φ.comp (Subgroup.inclusion inf_le_left)
  have hker : ψ.ker = (R ⊓ L).subgroupOf (Th ⊓ L) := by
    ext u
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact ⟨fun hu => ⟨(hφ _).mp hu, u.2.2⟩, fun hu => (hφ _).mpr hu.1⟩
  let Y : Subgroup X :=
    ((powMonoidHom 2 : Multiplicative (ZMod 4) →* _).ker.comap φ).map Th.subtype
  have hY : Subgroup.closure {x : X | x ∈ Th ⊓ L ∧ x * x = 1} ≤ Y := by
    rw [Subgroup.closure_le]
    rintro x ⟨hxU, hxx⟩
    refine ⟨⟨x, hxU.1⟩, ?_, rfl⟩
    show φ ⟨x, hxU.1⟩ ^ 2 = 1
    rw [← map_pow]
    have : (⟨x, hxU.1⟩ : ↥Th) ^ 2 = 1 := Subtype.ext (by simpa [sq] using hxx)
    rw [this, map_one]
  have hsq : ∀ u : ↥(Th ⊓ L), ψ u * ψ u = 1 := by
    intro u
    have hu : (u : X) ∈ Y := hY (by rw [hgen]; exact u.2)
    obtain ⟨t, ht, htu⟩ := hu
    have : t = ⟨u, u.2.1⟩ := Subtype.ext htu
    subst this
    have ht' : φ ⟨u, u.2.1⟩ ^ 2 = 1 := ht
    rw [sq] at ht'
    exact ht'
  have hrange : Nat.card ↥ψ.range ≤ 2 := by
    have hsub : (ψ.range : Set (Multiplicative (ZMod 4))) ⊆ {1, Multiplicative.ofAdd 2} := by
      rintro _ ⟨u, rfl⟩
      have := hsq u
      generalize ψ u = x at this ⊢
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      revert x
      decide
    calc Nat.card ↥ψ.range = (ψ.range : Set _).ncard := Nat.card_coe_set_eq _
      _ ≤ ({1, Multiplicative.ofAdd 2} : Set (Multiplicative (ZMod 4))).ncard :=
        Set.ncard_le_ncard hsub
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
  calc Nat.card ↥(Th ⊓ L) = Nat.card ψ.ker * ψ.ker.index := (Subgroup.card_mul_index _).symm
    _ = Nat.card ψ.ker * Nat.card ψ.range := by rw [Subgroup.index_ker]
    _ ≤ Nat.card ψ.ker * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(R ⊓ L) := by
      rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDU).toEquiv, mul_comm]

end Quotient

end E9P2.ExCrit

section Criterion

variable {X : Type} [Group X] [Finite X]

theorem E9Local.false_of_criterion {L Th Hh Eh R : Subgroup X} (h : E9Local L Th Hh Eh R)
    (hF1 : ∃ k : ℕ, Nat.card ↥(Th ⊓ L) = 4 ^ k)
    (hF2 : Subgroup.closure {x : X | x ∈ Th ⊓ L ∧ x * x = 1} = Th ⊓ L)
    (hF3 : ∀ z ∈ L, z * z = 1 → (∀ e ∈ Eh, z * e = e * z) → z = 1)
    (hF4 : ∀ x ∈ L, x ∈ Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) → x ^ 3 = 1 →
      x = 1) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDU : R ⊓ L ≤ Th ⊓ L := inf_le_inf_right L h.R_le_T
  have hU2 : IsPGroup 2 ↥(Th ⊓ L) := h.sylow_T.2.1.to_inf_left
  have hD2 : IsPGroup 2 ↥(R ⊓ L) := hU2.to_le hDU
  have hRnorm : ∀ x ∈ Hh, x ∈ Subgroup.normalizer ((R ⊓ L : Subgroup X) : Set X) := fun x hx =>
    E9P2.Loc.mem_normalizer_inf (h.R_norm hx) (E9P2.Loc.mem_normalizer_of_normal h.normal_L x)
  have hEnorm : ∀ e ∈ Eh, ∀ d ∈ R ⊓ L, e * d * e⁻¹ ∈ R ⊓ L := fun e he d hd =>
    (Subgroup.mem_normalizer_iff.mp (hRnorm e (h.E_le_H he)) d).mp hd
  have hfix : ∀ d ∈ R ⊓ L, (∀ e ∈ Eh, e * d * e⁻¹ = d) → d = 1 := by
    intro d hd hfixd
    by_contra hd1
    obtain ⟨k, hk⟩ := hD2 ⟨d, hd⟩
    obtain ⟨n, hnn, hn1⟩ := E9P2.ExCrit.exists_pow_involution hd1
      (by simpa using congrArg Subtype.val hk)
    refine hn1 (hF3 (d ^ n) ((R ⊓ L).pow_mem hd n).2 hnn fun e he => ?_)
    have hc : Commute e d := by
      have := hfixd e he
      exact mul_inv_eq_iff_eq_mul.mp this
    exact (hc.pow_right n).symm.eq
  have hE3 : IsPGroup 3 ↥Eh := IsPGroup.of_card (n := 2) (by rw [h.card_E]; norm_num)
  have hmod := E9P2.ExCrit.card_modEq_one hE3 hEnorm hfix
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hD2
  rw [hd] at hmod
  have hdeven := E9P2.ExCrit.even_of_two_pow_modEq hmod
  obtain ⟨k, hk⟩ := hF1
  obtain ⟨φ, -, hφ⟩ := h.quot4
  have hle := E9P2.ExCrit.card_le_two_mul h.R_le_T φ hφ hF2
  have hDU' : R ⊓ L = Th ⊓ L := by
    refine Subgroup.eq_of_le_of_card_ge hDU ?_
    have h4 : Nat.card ↥(Th ⊓ L) = 2 ^ (2 * k) := by rw [hk, pow_mul]; norm_num
    have h5 : 2 ^ (2 * k) ≤ 2 ^ (d + 1) :=
      calc 2 ^ (2 * k) = Nat.card ↥(Th ⊓ L) := h4.symm
        _ ≤ 2 * Nat.card ↥(R ⊓ L) := hle
        _ = 2 ^ (d + 1) := by rw [hd, pow_succ, mul_comm]
    have hkd := (Nat.pow_le_pow_iff_right (by norm_num)).mp h5
    obtain ⟨a, ha⟩ := hdeven
    rw [h4, hd]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hUnorm : ∀ x ∈ Hh, x ∈ Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) := by
    rw [← hDU']
    exact hRnorm
  have hEne : Eh ≠ ⊥ := by
    intro hbot
    have := h.card_E
    rw [hbot] at this
    simp at this
  obtain ⟨⟨e, he⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hEne)
  exact he1 (Subtype.ext (hF4 e (h.E_le_L he) (hUnorm e (h.E_le_H he)) (h.exp_E e he)))

end Criterion

end CFSG.Quasithin
