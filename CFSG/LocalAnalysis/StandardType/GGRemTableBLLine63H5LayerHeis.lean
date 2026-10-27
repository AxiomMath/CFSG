module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj

public section

namespace CFSG.StandardType.Line63.H5

open CFSG.Assembly

section Algebra

variable {G : Type*} [Group G] {u A B : G}

theorem pow_mul_eq_central (hu : ∀ g : G, Commute u g) (h : A * B = u * (B * A)) (i : ℕ) :
    A ^ i * B = u ^ i * (B * A ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc A ^ (i + 1) * B = A * (A ^ i * B) := by rw [pow_succ', mul_assoc]
      _ = A * (u ^ i * (B * A ^ i)) := by rw [ih]
      _ = u ^ i * (A * (B * A ^ i)) := ((hu A).symm.pow_right i).left_comm _
      _ = u ^ i * ((A * B) * A ^ i) := by rw [mul_assoc]
      _ = u ^ i * ((u * (B * A)) * A ^ i) := by rw [h]
      _ = u ^ i * (u * (B * (A * A ^ i))) := by simp only [mul_assoc]
      _ = u ^ (i + 1) * (B * A ^ (i + 1)) := by rw [← mul_assoc, ← pow_succ, pow_succ' A i]

theorem mul_pow_eq_central (hu : ∀ g : G, Commute u g) (h : A * B = u * (B * A)) (j : ℕ) :
    A * B ^ j = u ^ j * (B ^ j * A) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc A * B ^ (j + 1) = (A * B) * B ^ j := by rw [pow_succ', mul_assoc]
      _ = (u * (B * A)) * B ^ j := by rw [h]
      _ = u * (B * (A * B ^ j)) := by simp only [mul_assoc]
      _ = u * (B * (u ^ j * (B ^ j * A))) := by rw [ih]
      _ = u * (u ^ j * (B * (B ^ j * A))) := by rw [((hu B).symm.pow_right j).left_comm]
      _ = u ^ (j + 1) * (B ^ (j + 1) * A) := by
          rw [← mul_assoc, ← pow_succ', pow_succ' B j, mul_assoc]

theorem pow_mul_pow_eq_central (hu : ∀ g : G, Commute u g) (h : A * B = u * (B * A)) (i j : ℕ) :
    A ^ i * B ^ j = u ^ (i * j) * (B ^ j * A ^ i) := by
  have h' : A * B ^ j = u ^ j * (B ^ j * A) := mul_pow_eq_central hu h j
  rw [pow_mul_eq_central (fun g => (hu g).pow_left j) h' i, ← pow_mul, mul_comm j i]

theorem mul_pow_three_eq_central (hu : ∀ g : G, Commute u g) (h : A * B = u * (B * A))
    (hu3 : u ^ 3 = 1) : (A * B) ^ 3 = A ^ 3 * B ^ 3 := by
  have hw : ∀ g : G, Commute (u ^ 2) g := fun g => (hu g).pow_left 2
  have hw2 : ∀ g : G, Commute ((u ^ 2) ^ 2) g := fun g => (hw g).pow_left 2
  have mc : ∀ X Y : G, X * (u ^ 2 * Y) = u ^ 2 * (X * Y) := fun X Y => (hw X).symm.left_comm Y
  have mc2 : ∀ X Y : G, X * ((u ^ 2) ^ 2 * Y) = (u ^ 2) ^ 2 * (X * Y) := fun X Y =>
    (hw2 X).symm.left_comm Y
  have h' : B * A = u ^ 2 * (A * B) := by
    have e3 : u ^ 3 = u ^ 2 * u := pow_succ u 2
    calc B * A = u ^ 3 * (B * A) := by rw [hu3, one_mul]
      _ = u ^ 2 * (u * (B * A)) := by rw [e3, mul_assoc]
      _ = u ^ 2 * (A * B) := by rw [h]
  have h2 : B ^ 2 * A = (u ^ 2) ^ 2 * (A * B ^ 2) := by
    have := pow_mul_pow_eq_central hw h' 2 1
    simpa only [pow_one, mul_one] using this
  have s1 : (A * B) ^ 2 = u ^ 2 * (A ^ 2 * B ^ 2) := by
    calc (A * B) ^ 2 = A * (B * A) * B := by rw [pow_two]; simp only [mul_assoc]
      _ = A * (u ^ 2 * (A * B)) * B := by rw [h']
      _ = u ^ 2 * (A * (A * B) * B) := by rw [mc, mul_assoc (u ^ 2)]
      _ = u ^ 2 * (A ^ 2 * B ^ 2) := by simp only [pow_two, mul_assoc]
  calc (A * B) ^ 3 = (A * B) ^ 2 * (A * B) := pow_succ _ 2
    _ = u ^ 2 * ((A ^ 2 * B ^ 2) * (A * B)) := by rw [s1, mul_assoc]
    _ = u ^ 2 * (A ^ 2 * (B ^ 2 * A) * B) := by simp only [mul_assoc]
    _ = u ^ 2 * (A ^ 2 * ((u ^ 2) ^ 2 * (A * B ^ 2)) * B) := by rw [h2]
    _ = u ^ 2 * ((u ^ 2) ^ 2 * (A ^ 2 * (A * B ^ 2) * B)) := by
        rw [mc2 (A ^ 2), mul_assoc ((u ^ 2) ^ 2)]
    _ = u ^ 2 * ((u ^ 2) ^ 2 * (A ^ 3 * B ^ 3)) := by
        simp only [pow_two, pow_three', mul_assoc]
    _ = (u ^ 3) ^ 2 * (A ^ 3 * B ^ 3) := by
        rw [← mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
    _ = A ^ 3 * B ^ 3 := by rw [hu3, one_pow, one_mul]

end Algebra

section Mono

variable {K : Type} [Field K] {x y z u : GL (Fin 6) K}

theorem commute_of_mem_largeEvenScalars {t : GL (Fin 6) K} (ht : t ∈ LargeEvenScalars (Fin 6) K)
    (g : GL (Fin 6) K) : Commute t g :=
  (Subgroup.mem_center_iff.mp (TableB.scalars_le_center ht) g).symm

theorem heis_pair_y (hu : ∀ g : GL (Fin 6) K, Commute u g) (hxy : x * y = u * (y * x)) (i j : ℕ) :
    (x ^ i * y ^ j) * y = u ^ i * (y * (x ^ i * y ^ j)) := by
  calc (x ^ i * y ^ j) * y = x ^ i * (y * y ^ j) := by rw [mul_assoc, ← pow_succ, pow_succ']
    _ = (x ^ i * y) * y ^ j := by rw [mul_assoc]
    _ = (u ^ i * (y * x ^ i)) * y ^ j := by rw [pow_mul_eq_central hu hxy i]
    _ = u ^ i * (y * (x ^ i * y ^ j)) := by simp only [mul_assoc]

theorem heis_pair_x (hu : ∀ g : GL (Fin 6) K, Commute u g) (hxy : x * y = u * (y * x)) (i j : ℕ) :
    x * (x ^ i * y ^ j) = u ^ j * ((x ^ i * y ^ j) * x) := by
  calc x * (x ^ i * y ^ j) = x ^ i * (x * y ^ j) := by
        rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc]
    _ = x ^ i * (u ^ j * (y ^ j * x)) := by rw [mul_pow_eq_central hu hxy j]
    _ = u ^ j * (x ^ i * (y ^ j * x)) := ((hu (x ^ i)).symm.pow_right j).left_comm _
    _ = u ^ j * ((x ^ i * y ^ j) * x) := by rw [mul_assoc]

theorem mono_y (hu : ∀ g : GL (Fin 6) K, Commute u g) (hxy : x * y = u * (y * x))
    (hyz : y * z = z * y) (i j k : ℕ) :
    (x ^ i * y ^ j * z ^ k) * y = u ^ i * (y * (x ^ i * y ^ j * z ^ k)) := by
  have hc : z ^ k * y = y * z ^ k := ((Commute.pow_right (show Commute y z from hyz) k).eq).symm
  calc (x ^ i * y ^ j * z ^ k) * y = (x ^ i * y ^ j) * (z ^ k * y) := by simp only [mul_assoc]
    _ = (x ^ i * y ^ j) * (y * z ^ k) := by rw [hc]
    _ = ((x ^ i * y ^ j) * y) * z ^ k := by simp only [mul_assoc]
    _ = (u ^ i * (y * (x ^ i * y ^ j))) * z ^ k := by rw [heis_pair_y hu hxy]
    _ = u ^ i * (y * (x ^ i * y ^ j * z ^ k)) := by simp only [mul_assoc]

theorem mono_x (hu : ∀ g : GL (Fin 6) K, Commute u g) (hxy : x * y = u * (y * x))
    (hxz : x * z = z * x) (i j k : ℕ) :
    x * (x ^ i * y ^ j * z ^ k) = u ^ j * ((x ^ i * y ^ j * z ^ k) * x) := by
  have hc : x * z ^ k = z ^ k * x := (Commute.pow_right (show Commute x z from hxz) k).eq
  calc x * (x ^ i * y ^ j * z ^ k) = (x * (x ^ i * y ^ j)) * z ^ k := by simp only [mul_assoc]
    _ = (u ^ j * ((x ^ i * y ^ j) * x)) * z ^ k := by rw [heis_pair_x hu hxy]
    _ = u ^ j * ((x ^ i * y ^ j) * (x * z ^ k)) := by simp only [mul_assoc]
    _ = u ^ j * ((x ^ i * y ^ j) * (z ^ k * x)) := by rw [hc]
    _ = u ^ j * ((x ^ i * y ^ j * z ^ k) * x) := by simp only [mul_assoc]

theorem mono_inj (hu : u ∈ LargeEvenScalars (Fin 6) K) (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hxy : x * y = u * (y * x)) (hxz : x * z = z * x) (hyz : y * z = z * y) (hz3 : z ^ 3 = 1)
    (hzs : z ∉ LargeEvenScalars (Fin 6) K) {t : GL (Fin 6) K}
    (ht : t ∈ LargeEvenScalars (Fin 6) K) {i j k i' j' k' : ℕ} (hj : j < 3) (hj' : j' < 3)
    (hi : i < 3) (hi' : i' < 3) (hk : k < 3) (hk' : k' < 3)
    (h : x ^ i * y ^ j * z ^ k = t * (x ^ i' * y ^ j' * z ^ k')) :
    i = i' ∧ j = j' ∧ k = k' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcu := commute_of_mem_largeEvenScalars hu
  have hct := commute_of_mem_largeEvenScalars ht
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hpow : ∀ a b : ℕ, a < 3 → b < 3 → u ^ a = u ^ b → a = b := by
    intro a b ha hb hab
    have := pow_eq_pow_iff_modEq.mp hab
    rw [hord] at this
    exact Nat.ModEq.eq_of_lt_of_lt this ha hb
  have hj_eq : j = j' := by
    refine hpow j j' hj hj' ?_
    have e1 := mono_x hcu hxy hxz i j k
    have e2 := mono_x hcu hxy hxz i' j' k'
    rw [h] at e1
    have e3 : x * (t * (x ^ i' * y ^ j' * z ^ k')) =
        t * (u ^ j' * ((x ^ i' * y ^ j' * z ^ k') * x)) := by
      rw [← e2]
      exact (hct x).symm.left_comm _
    have e4 : u ^ j * ((t * (x ^ i' * y ^ j' * z ^ k')) * x) =
        t * (u ^ j * ((x ^ i' * y ^ j' * z ^ k') * x)) := by
      rw [mul_assoc t]
      exact ((hcu t).pow_left j).left_comm _
    have e5 := e3.symm.trans (e1.trans e4)
    exact (mul_right_cancel (mul_left_cancel e5)).symm
  have hi_eq : i = i' := by
    refine hpow i i' hi hi' ?_
    have e1 := mono_y hcu hxy hyz i j k
    have e2 := mono_y hcu hxy hyz i' j' k'
    rw [h] at e1
    have e3 : (t * (x ^ i' * y ^ j' * z ^ k')) * y =
        t * (u ^ i' * (y * (x ^ i' * y ^ j' * z ^ k'))) := by
      rw [mul_assoc, e2]
    have e4 : u ^ i * (y * (t * (x ^ i' * y ^ j' * z ^ k'))) =
        t * (u ^ i * (y * (x ^ i' * y ^ j' * z ^ k'))) := by
      rw [(hct y).symm.left_comm, ((hcu t).pow_left i).left_comm]
    have e5 := e3.symm.trans (e1.trans e4)
    exact (mul_right_cancel (mul_left_cancel e5)).symm
  subst hj_eq hi_eq
  refine ⟨rfl, rfl, ?_⟩
  have e1 : z ^ k = t * z ^ k' := by
    have e2 : (x ^ i * y ^ j) * z ^ k = (x ^ i * y ^ j) * (t * z ^ k') := by
      calc (x ^ i * y ^ j) * z ^ k = t * ((x ^ i * y ^ j) * z ^ k') := h
        _ = (x ^ i * y ^ j) * (t * z ^ k') := ((hct (x ^ i * y ^ j)).symm.left_comm _).symm
    exact mul_left_cancel e2
  have hQ : (QuotientGroup.mk z : GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K) ^ k =
      (QuotientGroup.mk z) ^ k' := by
    rw [← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, e1, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff t).mpr ht, one_mul]
  have hz1 : (QuotientGroup.mk z : GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K) ≠ 1 := fun h1 =>
    hzs ((QuotientGroup.eq_one_iff z).mp h1)
  have hz3' : (QuotientGroup.mk z : GL (Fin 6) K ⧸ LargeEvenScalars (Fin 6) K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hz3, QuotientGroup.mk_one]
  have hordz := orderOf_eq_prime hz3' hz1
  have := pow_eq_pow_iff_modEq.mp hQ
  rw [hordz] at this
  exact Nat.ModEq.eq_of_lt_of_lt this hk hk'

end Mono

end CFSG.StandardType.Line63.H5

end
