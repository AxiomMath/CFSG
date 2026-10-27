module

public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch10SecQ9H53

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv

open CFSG.Quasithin
open scoped commutatorElement

variable {Y : Type} [Group Y]

theorem map_le_of_fix {K F : Subgroup Y} [F.Normal] (hKF : K ⊔ F = ⊤) (hKp : ⁅K, K⁆ = K)
    {w : Y} (hwK : ∀ k ∈ K, k * w = w * k)
    (hC : ∀ f ∈ F, w * f = f * w → (∀ k ∈ K, f * k = k * f) ∧
      ∀ f' ∈ F, w * f' = f' * w → f * f' = f' * f)
    (φ : MulAut Y) (hφw : φ w = w) : K.map φ.toMonoidHom ≤ K := by
  have hdec : ∀ k ∈ K, ∃ k₀ ∈ K, ∃ f ∈ F, w * f = f * w ∧ φ k = k₀ * f := by
    intro k hk
    have hmem : φ k ∈ ((K ⊔ F : Subgroup Y) : Set Y) := by
      rw [hKF]
      exact Set.mem_univ _
    rw [Subgroup.mul_normal] at hmem
    obtain ⟨k₀, hk₀, f, hf, hkf⟩ := hmem
    refine ⟨k₀, hk₀, f, hf, ?_, hkf.symm⟩
    have h1 : φ k * w = w * φ k := by
      rw [← hφw, ← map_mul, ← map_mul, hwK k hk]
    have h3 : w * k₀⁻¹ = k₀⁻¹ * w := (Commute.inv_right (hwK k₀ hk₀).symm).eq
    have hfe : f = k₀⁻¹ * φ k := by rw [← hkf, inv_mul_cancel_left]
    rw [hfe]
    calc w * (k₀⁻¹ * φ k) = w * k₀⁻¹ * φ k := (mul_assoc _ _ _).symm
      _ = k₀⁻¹ * (w * φ k) := by rw [h3, mul_assoc]
      _ = k₀⁻¹ * (φ k * w) := by rw [h1]
      _ = k₀⁻¹ * φ k * w := (mul_assoc _ _ _).symm
  have hcomm : ∀ a ∈ K.map φ.toMonoidHom, ∀ b ∈ K.map φ.toMonoidHom, ⁅a, b⁆ ∈ K := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨k₁, hk₁, f₁, hf₁, hwf₁, he₁⟩ := hdec x hx
    obtain ⟨k₂, hk₂, f₂, hf₂, hwf₂, he₂⟩ := hdec y hy
    simp only [MulEquiv.coe_toMonoidHom]
    rw [he₁, he₂]
    obtain ⟨hf₁K, hf₁f⟩ := hC f₁ hf₁ hwf₁
    obtain ⟨hf₂K, -⟩ := hC f₂ hf₂ hwf₂
    have c12 : f₁ * k₂ = k₂ * f₁ := hf₁K k₂ hk₂
    have d1 : f₂ * f₁⁻¹ = f₁⁻¹ * f₂ := (Commute.inv_left (hf₁f f₂ hf₂ hwf₂)).eq.symm
    have d2 : f₂ * k₁⁻¹ = k₁⁻¹ * f₂ := (Commute.inv_right (hf₂K k₁ hk₁)).eq
    have e : ⁅k₁ * f₁, k₂ * f₂⁆ = ⁅k₁, k₂⁆ := by
      calc ⁅k₁ * f₁, k₂ * f₂⁆
          = k₁ * (f₁ * k₂) * (f₂ * f₁⁻¹) * k₁⁻¹ * f₂⁻¹ * k₂⁻¹ := by
            rw [commutatorElement_def]
            group
        _ = k₁ * (k₂ * f₁) * (f₁⁻¹ * f₂) * k₁⁻¹ * f₂⁻¹ * k₂⁻¹ := by rw [c12, d1]
        _ = k₁ * k₂ * (f₂ * k₁⁻¹) * f₂⁻¹ * k₂⁻¹ := by group
        _ = k₁ * k₂ * (k₁⁻¹ * f₂) * f₂⁻¹ * k₂⁻¹ := by rw [d2]
        _ = ⁅k₁, k₂⁆ := by
            rw [commutatorElement_def]
            group
    rw [e]
    exact hKp ▸ Subgroup.commutator_mem_commutator hk₁ hk₂
  have hperf : ⁅K.map φ.toMonoidHom, K.map φ.toMonoidHom⁆ = K.map φ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hKp]
  rw [← hperf, Subgroup.commutator_le]
  exact hcomm

theorem inf_oddCore_eq_bot [Finite Y] {R : Subgroup Y} (hR : IsPGroup 2 ↥R) :
    R ⊓ CFSG.oddCore Y = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hR ⟨x, hx.1⟩
  have h1 : orderOf x ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h3 : Odd (orderOf x) := (QuasithinUnique.EscapingLocal.odd_card_oddCore Y).of_dvd_nat
    (Subgroup.orderOf_dvd_natCard _ hx.2)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · exfalso
    rw [hj] at h3
    exact (Nat.not_even_iff_odd.mpr h3) (Nat.even_pow.mpr ⟨even_two, by omega⟩)

theorem fix_of_inf_eq_bot {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (e : Y ⧸ CFSG.oddCore Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) {R : Subgroup Y}
    (hRF : R ⊓ CFSG.oddCore Y = ⊥) (φ : MulAut Y) (hφR : ∀ r ∈ R, φ r ∈ R) {w : Y}
    (hwR : w ∈ R) (hw2 : w * w = 1) (hw1 : w ≠ 1) : φ w = w := by
  have hRF' : ∀ x ∈ R, x ∈ CFSG.oddCore Y → x = 1 := fun x hxR hxF => by
    have h : x ∈ R ⊓ CFSG.oddCore Y := ⟨hxR, hxF⟩
    rwa [hRF, Subgroup.mem_bot] at h
  have hinv : ∀ x ∈ R, x * x = 1 → x ≠ 1 →
      e (x : Y ⧸ CFSG.oddCore Y) ^ 2 = 1 ∧ e (x : Y ⧸ CFSG.oddCore Y) ≠ 1 := by
    intro x hxR hx2 hx1
    refine ⟨by rw [pow_two, ← map_mul, ← QuotientGroup.mk_mul, hx2, QuotientGroup.mk_one,
      map_one], ?_⟩
    intro h
    have h' : (x : Y ⧸ CFSG.oddCore Y) = 1 := e.injective (h.trans (map_one e).symm)
    exact hx1 (hRF' x hxR ((QuotientGroup.eq_one_iff x).mp h'))
  have hφw2 : φ w * φ w = 1 := by rw [← map_mul, hw2, map_one]
  have hφw1 : φ w ≠ 1 := fun h => hw1 (φ.injective (h.trans (map_one φ).symm))
  obtain ⟨a1, a2⟩ := hinv w hwR hw2 hw1
  obtain ⟨b1, b2⟩ := hinv (φ w) (hφR w hwR) hφw2 hφw1
  have hpi : (w : Y ⧸ CFSG.oddCore Y) = (φ w : Y ⧸ CFSG.oddCore Y) :=
    e.injective (eq_of_sq_eq_one hp2 a1 a2 b1 b2)
  have hmem : w⁻¹ * φ w ∈ CFSG.oddCore Y := QuotientGroup.eq.mp hpi
  have h := hRF' _ (R.mul_mem (R.inv_mem hwR) (hφR w hwR)) hmem
  rw [inv_mul_eq_one] at h
  exact h.symm

theorem mem_of_odd_of_mem_sup [Finite Y] {K Q : Subgroup Y} (hQ : IsPGroup 2 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set Y)) {x : Y} (hx : x ∈ K ⊔ Q)
    (hxo : Odd (orderOf x)) : x ∈ K := by
  have hx' : x ∈ ((K ⊔ Q : Subgroup Y) : Set Y) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K Q hQK] at hx'
  obtain ⟨k, hk, q, hq, rfl⟩ := hx'
  have hpow : ∀ n : ℕ, ∃ k' ∈ K, (k * q) ^ n = k' * q ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, K.one_mem, by rw [pow_zero, pow_zero, mul_one]⟩
    | succ n ih =>
      obtain ⟨k', hk', he⟩ := ih
      refine ⟨k' * (q ^ n * k * (q ^ n)⁻¹), K.mul_mem hk' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hQK (Q.pow_mem hq n)) k).mp hk
      · rw [pow_succ, he, pow_succ]
        group
  obtain ⟨k', hk', he⟩ := hpow (orderOf (k * q))
  rw [pow_orderOf_eq_one] at he
  have hqK : q ^ orderOf (k * q) ∈ K := by
    rw [eq_inv_of_mul_eq_one_right he.symm]
    exact K.inv_mem hk'
  obtain ⟨a, ha⟩ := hQ ⟨q, hq⟩
  have hqa : orderOf q ∣ 2 ^ a :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val ha)
  have hcop : (orderOf (k * q)).Coprime (orderOf q) :=
    (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hxo)).coprime_dvd_right hqa
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hq' : q ∈ K := hm ▸ K.pow_mem hqK m
  exact K.mul_mem hk hq'

theorem le_of_le_sup [Finite Y] {K Q X : Subgroup Y} (hQ : IsPGroup 2 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set Y)) (hX : X ≤ K ⊔ Q) (hXp : ⁅X, X⁆ = X) : X ≤ K := by
  rw [eq_oTwoUpper_of_perfect hXp]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxX, hxo⟩
  exact mem_of_odd_of_mem_sup hQ hQK (hX hxX) hxo

end CFSG.Quasithin.Vol2.Ch10.SecB.SL2Inv
