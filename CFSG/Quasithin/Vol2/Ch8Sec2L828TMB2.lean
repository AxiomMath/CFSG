module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828SMB
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TQMod
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open CFSG.Quasithin.H13.L828T

@[expose] def MB2_828 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H X : Subgroup (MulAut V)),
    X ≤ Subgroup.normalizer (H : Set (MulAut V)) → IsElemAbelian2 X →
    (((BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
        (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7)) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
        Nonempty (↥(commutant (s828BPrime H X) (fixV X)
          (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V))) ≃+* K)) ∧
    ((MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
        Nonempty (↥(commutant (s828BPrime H X) (fixV X)
          (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V))) ≃+* K)) ∧
    ((MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3) →
      Nonempty (↥(commutant (s828BPrime H X) (fixV X)
        (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V))) ≃+*
          Matrix (Fin 2) (Fin 2) (ZMod 2)))

private lemma mb2_eq_one_of_pow_eq_one_coprime {M : Type*} [Monoid M] {x : M} {a b : ℕ}
    (ha : x ^ a = 1) (hb : x ^ b = 1) (hab : Nat.Coprime a b) : x = 1 := by
  have h : x ^ Nat.gcd a b = 1 := pow_gcd_eq_one.mpr ⟨ha, hb⟩
  rwa [Nat.Coprime.gcd_eq_one hab, pow_one] at h

private lemma mb2_field_eq_one_of_pow_five {K : Type*} [Field K] [Finite K] {x : K} {n q : ℕ}
    (hq : Nat.card K = q) (hx : x ^ (5 ^ n) = 1) (hcop : Nat.Coprime (5 ^ n) (q - 1)) :
    x = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero n (by norm_num : (5 : ℕ) ≠ 0))] at hx
    exact zero_ne_one hx
  have hfermat : x ^ (q - 1) = 1 := by
    subst hq
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one x hx0
  exact mb2_eq_one_of_pow_eq_one_coprime hx hfermat hcop

private lemma mb2_matrix_two_eq_one_of_pow_five {x : Matrix (Fin 2) (Fin 2) (ZMod 2)} {n : ℕ}
    (hx : x ^ (5 ^ n) = 1) : x = 1 := by
  obtain ⟨u, rfl⟩ := IsUnit.of_pow_eq_one hx (pow_ne_zero n (by norm_num : (5 : ℕ) ≠ 0))
  have hu : u ^ (5 ^ n) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hx)
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    norm_num
  have h1 : orderOf u ∣ 5 ^ n := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ 6 := by
    rw [← hcard]
    exact orderOf_dvd_natCard u
  have hcop : Nat.Coprime (5 ^ n) 6 := Nat.Coprime.pow_left n (by decide)
  have h3 : orderOf u = 1 := by
    have h := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact Nat.dvd_one.mp h
  rw [orderOf_eq_one_iff.mp h3, Units.val_one]

private lemma mb2_eq_one_of_ringEquiv_field {R K : Type*} [Ring R] [Field K] [Finite K]
    (e : R ≃+* K) {r : R} {n q : ℕ} (hr : r ^ (5 ^ n) = 1) (hq : Nat.card K = q)
    (hcop : Nat.Coprime (5 ^ n) (q - 1)) : r = 1 := by
  apply e.injective
  rw [map_one]
  refine mb2_field_eq_one_of_pow_five hq ?_ hcop
  have h := congrArg e hr
  rwa [map_pow, map_one] at h

private lemma mb2_eq_one_of_ringEquiv_matrix {R : Type*} [Ring R]
    (e : R ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)) {r : R} {n : ℕ} (hr : r ^ (5 ^ n) = 1) :
    r = 1 := by
  apply e.injective
  rw [map_one]
  refine mb2_matrix_two_eq_one_of_pow_five (n := n) ?_
  have h := congrArg e hr
  rwa [map_pow, map_one] at h

theorem mb2_unit_five (hMB2 : MB2_828) (V : Type) [CommGroup V] [Finite V]
    (H X : Subgroup (MulAut V)) (hXH : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hX : IsElemAbelian2 X)
    (hrow : (BinaryNineTensor H ⊤ ⊥ 1 ∧ rk ↥X = 4 ∧ rk ↥(fixV X) = 4) ∨
      (MathieuCode22 H ⊤ ⊥ ∧ rk ↥X = 5 ∧ rkIdx (fixV X) = 6) ∨
      (MathieuCode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rkIdx (fixV X) = 7) ∨
      (MathieuCocode24 H ⊤ ⊥ ∧ rk ↥X = 6 ∧ rk ↥(fixV X) = 3))
    (φ : AddMonoid.End (QMod (s828BPrime H X) (fixV X)))
    (hφ : φ ∈ commutant (s828BPrime H X) (fixV X)
      (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V)))
    (n : ℕ) (hn : φ ^ (5 ^ n) = 1) : φ = 1 := by
  obtain ⟨h1, h2, h3⟩ := hMB2 V H X hXH hX
  obtain ⟨d, hdφ⟩ : ∃ d : ↥(commutant (s828BPrime H X) (fixV X)
      (perfectCore (H ⊓ stabSub (fixV X)) : Set (MulAut V))),
      (d : AddMonoid.End (QMod (s828BPrime H X) (fixV X))) = φ := ⟨⟨φ, hφ⟩, rfl⟩
  have hd : d ^ (5 ^ n) = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hdφ, Subring.coe_one]
    exact hn
  have hd1 : d = 1 := by
    rcases hrow with hr1 | hr2 | hr3 | hr4
    · obtain ⟨K, hKf, hKfin, hK4, ⟨e⟩⟩ := h1 (Or.inl hr1)
      exact mb2_eq_one_of_ringEquiv_field e hd hK4 (Nat.Coprime.pow_left n (by decide))
    · obtain ⟨K, hKf, hKfin, hK2, ⟨e⟩⟩ := h2 hr2
      exact mb2_eq_one_of_ringEquiv_field e hd hK2 (Nat.coprime_one_right _)
    · obtain ⟨K, hKf, hKfin, hK4, ⟨e⟩⟩ := h1 (Or.inr hr3)
      exact mb2_eq_one_of_ringEquiv_field e hd hK4 (Nat.Coprime.pow_left n (by decide))
    · obtain ⟨e⟩ := h3 hr4
      exact mb2_eq_one_of_ringEquiv_matrix e hd
  rw [← hdφ, hd1, Subring.coe_one]

end CFSG.Quasithin.H13
