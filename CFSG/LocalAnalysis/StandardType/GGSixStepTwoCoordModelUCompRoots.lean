module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompTorus
public import CFSG.RankThree.PartOne.KC.UnitaryNonsplitCount

public section

namespace CFSG.StandardType

namespace CoordSU

open Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary

section Roots

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] {p : ℕ} [NeZero p]

theorem zmodChar_natCast_mul {ζ : E} (hζ : ζ ^ p = 1) (m : ℕ) (e : ZMod p) :
    AddChar.zmodChar p hζ ((m : ZMod p) * e) = AddChar.zmodChar p hζ e ^ m := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

theorem zmodChar_injective {ζ : E} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (AddChar.zmodChar p hζ.pow_eq_one) := fun e e' h' => by
  rw [AddChar.zmodChar_apply, AddChar.zmodChar_apply] at h'
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h')

theorem aeval_pow_card_eq_zero {c : K[X]} {μ : E} (hμ : aeval μ c = 0) :
    aeval (μ ^ Nat.card K) c = 0 := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, ← expand_aeval, FiniteField.Polynomial.expand_card, map_pow, hμ,
    zero_pow Fintype.card_ne_zero]

theorem eq_pow_mul_of_roots (hp : p.Prime) (hpK : (p : K) ≠ 0) {c : K[X]} (hc : Irreducible c)
    (hcd : c ∣ cyclotomic p K) {ζ : E} (hζ : IsPrimitiveRoot ζ p) {e₀ e : ZMod p}
    (h₀ : aeval (AddChar.zmodChar p hζ.pow_eq_one e₀) c = 0)
    (he : aeval (AddChar.zmodChar p hζ.pow_eq_one e) c = 0) :
    ∃ j : ℕ, e = (Nat.card K : ZMod p) ^ j * e₀ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set ψ := AddChar.zmodChar p hζ.pow_eq_one with hψ
  set Q := Nat.card K with hQ
  have hψinj : Function.Injective ψ := zmodChar_injective hζ
  have he₀ : e₀ ≠ 0 := by
    rintro rfl
    rw [AddChar.map_zero_eq_one] at h₀
    obtain ⟨g, hg⟩ := hcd
    have h1 : aeval (algebraMap K E 1) (cyclotomic p K) = 0 := by
      rw [map_one, hg, map_mul, h₀, zero_mul]
    rw [aeval_algebraMap_apply_eq_algebraMap_eval, eval_one_cyclotomic_prime,
      map_eq_zero_iff _ (algebraMap K E).injective] at h1
    exact hpK h1
  have horb : ∀ j : ℕ, aeval (ψ ((Q : ZMod p) ^ j * e₀)) c = 0 := by
    intro j
    induction j with
    | zero => rwa [pow_zero, one_mul]
    | succ j ih =>
      rw [pow_succ', mul_assoc, zmodChar_natCast_mul]
      exact aeval_pow_card_eq_zero ih
  have hd : c.natDegree = orderOf (Q : ZMod p) := by
    rw [OrdPNS.natDegree_eq_ordQ hp hpK hc hcd, OrdPNS.ordQ_def]
  set d := c.natDegree with hddef
  have hinj : Set.InjOn (fun j : ℕ => (Q : ZMod p) ^ j * e₀) (Finset.range d : Set ℕ) := by
    intro j hj j' hj' hjj
    have h1 : (Q : ZMod p) ^ j = (Q : ZMod p) ^ j' := mul_right_cancel₀ he₀ hjj
    refine pow_injOn_Iio_orderOf ?_ ?_ h1
    · rw [Set.mem_Iio, ← hd]
      exact Finset.mem_range.mp hj
    · rw [Set.mem_Iio, ← hd]
      exact Finset.mem_range.mp hj'
  set R : Finset (ZMod p) := Finset.univ.filter fun e' => aeval (ψ e') c = 0 with hR
  have hc0 : c.map (algebraMap K E) ≠ 0 :=
    Polynomial.map_ne_zero (Irreducible.ne_zero hc)
  have hRcard : R.card ≤ d := by
    have h1 : R.card ≤ (c.map (algebraMap K E)).roots.toFinset.card := by
      refine Finset.card_le_card_of_injOn ψ (fun e' he' => ?_) hψinj.injOn
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hc0, IsRoot, eval_map,
        ← aeval_def]
      exact (Finset.mem_filter.mp he').2
    exact h1.trans ((Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (natDegree_map (algebraMap K E)).le))
  set T : Finset (ZMod p) := (Finset.range d).image fun j => (Q : ZMod p) ^ j * e₀ with hT
  have hTcard : T.card = d := by
    rw [hT, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hTR : T ⊆ R := by
    intro e' he'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp he'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, horb j⟩
  have hTR' : T = R := Finset.eq_of_subset_of_card_le hTR (by rw [hTcard]; exact hRcard)
  have heR : e ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  rw [← hTR'] at heR
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp heR
  exact ⟨j, hj.symm⟩

end Roots

section Dual

variable {f : ℕ} {K E : Type} [Field K] [Field E] [Algebra K E] {p : ℕ}

theorem dvd_cyclotomic_of_dvd (hp : p.Prime) {c : K[X]} (hc : Irreducible c) (hcm : c.Monic)
    (hcd : c ∣ X ^ p - C 1) (hc1 : c ≠ X - C 1) : c ∣ cyclotomic p K := by
  have : Fact p.Prime := ⟨hp⟩
  rw [C_1, ← cyclotomic_prime_mul_X_sub_one K p] at hcd
  rcases hc.prime.dvd_or_dvd hcd with h1 | h1
  · exact h1
  · exfalso
    apply hc1
    have hass := hc.associated_of_dvd (irreducible_X_sub_C 1) h1
    exact eq_of_monic_of_associated hcm (monic_X_sub_C 1) hass

theorem exists_negQ_of_roots [CharP E 2] (h : UnitaryFieldData 2 f K) (hp : p.Prime) (hp2 : p ≠ 2)
    [NeZero p] {a : K[X]}
    (ha : Irreducible a) (hacd : a ∣ cyclotomic p K) (had : Irreducible (dualPoly h.bar a))
    (hadcd : dualPoly h.bar a ∣ cyclotomic p K) (hdd : dualPoly h.bar (dualPoly h.bar a) = a)
    {ζ : E} (hζ : IsPrimitiveRoot ζ p) {k₁ k₂ : ZMod p}
    (h₁ : aeval (AddChar.zmodChar p hζ.pow_eq_one k₁) a = 0 ∨
      aeval (AddChar.zmodChar p hζ.pow_eq_one k₁) (dualPoly h.bar a) = 0)
    (h₂ : aeval (AddChar.zmodChar p hζ.pow_eq_one k₂) a = 0 ∨
      aeval (AddChar.zmodChar p hζ.pow_eq_one k₂) (dualPoly h.bar a) = 0) :
    ∃ t : ℕ, k₂ = (-((2 ^ f : ℕ) : ZMod p)) ^ t * k₁ := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := AddChar.zmodChar p hζ.pow_eq_one with hψ
  have hpK : (p : K) ≠ 0 := by
    have : CharP K 2 := h.charP
    rw [CFSG.RankThree.PartOne.OddIso.natCast_odd_eq_one (hp.odd_of_ne_two hp2)]
    exact one_ne_zero
  have hQ : ((Nat.card K : ℕ) : ZMod p) = (-((2 ^ f : ℕ) : ZMod p)) ^ 2 := by
    rw [neg_sq, ← Nat.cast_pow, h.card, ← pow_mul, mul_comm f 2]
  have horb : ∀ c : K[X], Irreducible c → c ∣ cyclotomic p K → ∀ e₀ e : ZMod p,
      aeval (ψ e₀) c = 0 → aeval (ψ e) c = 0 → ∃ t : ℕ, e = (-((2 ^ f : ℕ) : ZMod p)) ^ t * e₀ := by
    intro c hc hccd e₀ e h0 h1
    obtain ⟨j, hj⟩ := eq_pow_mul_of_roots hp hpK hc hccd hζ h0 h1
    exact ⟨2 * j, by rw [hj, hQ, ← pow_mul]⟩
  have hdual : ∀ c : K[X], c ∣ cyclotomic p K → ∀ k : ZMod p, aeval (ψ k) c = 0 →
      aeval (ψ (-((2 ^ f : ℕ) : ZMod p) * k)) (dualPoly h.bar c) = 0 := by
    intro c hccd k hk
    have hcX : c ∣ X ^ p - C 1 := by
      rw [C_1]
      exact hccd.trans (cyclotomic.dvd_X_pow_sub_one p K)
    have h0 : c.coeff 0 ≠ 0 := by
      intro h0
      obtain ⟨g, hg⟩ := hcX
      have h1 := congrArg (Polynomial.eval 0) hg
      rw [eval_mul, ← Polynomial.coeff_zero_eq_eval_zero c, h0, zero_mul] at h1
      simp [zero_pow hp.ne_zero] at h1
    have h1 := aeval_dualPoly_inv_pow (h := h) h0 hk
    have h2 : ψ (-((2 ^ f : ℕ) : ZMod p) * k) = (ψ k ^ 2 ^ f)⁻¹ := by
      rw [neg_mul, AddChar.map_neg_eq_inv, zmodChar_natCast_mul]
    rw [h2]
    exact h1
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact horb a ha hacd k₁ k₂ h₁ h₂
  · obtain ⟨t, ht⟩ := horb _ had hadcd _ k₂ (hdual a hacd k₁ h₁) h₂
    exact ⟨t + 1, by rw [ht, pow_succ, mul_assoc]⟩
  · have h3 := hdual _ hadcd k₁ h₁
    rw [hdd] at h3
    obtain ⟨t, ht⟩ := horb a ha hacd _ k₂ h3 h₂
    exact ⟨t + 1, by rw [ht, pow_succ, mul_assoc]⟩
  · exact horb _ had hadcd k₁ k₂ h₁ h₂

end Dual

end CoordSU

end CFSG.StandardType
