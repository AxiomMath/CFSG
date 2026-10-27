module

public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint.Chevalley


theorem six_le_of_card_adjointGroup_G2_dvd_card_GL {K : Type} [Field K] [Finite K] {x : ℕ}
    (hx : 2 ≤ x) (hK : Nat.card K = 2 ^ x) {d : ℕ}
    (hd : Nat.card (adjointGroup Tag.G2 K) ∣ Nat.card (GL (Fin d) K)) :
    6 ≤ d := by
  by_contra hd6
  have hd5 : d ≤ 5 := by omega
  have horder : Nat.card (adjointGroup Tag.G2 K) =
      (2 ^ x) ^ 6 * ((2 ^ x) ^ 6 - 1) * ((2 ^ x) ^ 2 - 1) :=
    (CFSG.LieType.Chevalley.exact_G2_finite_order K (q := 2 ^ x) hK).2.1
  have hdvdG : 2 ^ (6 * x) - 1 ∣ Nat.card (adjointGroup Tag.G2 K) := by
    rw [horder]
    have h6 : (2 ^ x) ^ 6 = 2 ^ (6 * x) := by
      rw [← Nat.pow_mul, Nat.mul_comm x 6]
    have h2 : (2 ^ x) ^ 2 = 2 ^ (2 * x) := by
      rw [← Nat.pow_mul, Nat.mul_comm x 2]
    rw [h6, h2]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hdvdGL : 2 ^ (6 * x) - 1 ∣ Nat.card (GL (Fin d) K) := hdvdG.trans hd
  obtain ⟨p, hp, hpdvd, hpprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (6 * x) (by omega) (by omega)
  have hpGL : p ∣ Nat.card (GL (Fin d) K) := hpdvd.trans hdvdGL
  have hpq : ¬ p ∣ 2 ^ x := by
    intro hp2
    have hp6 : p ∣ 2 ^ (6 * x) := by
      have h : p ∣ (2 ^ x) ^ 6 := dvd_pow hp2 (by norm_num)
      rwa [← Nat.pow_mul, Nat.mul_comm x 6] at h
    have hsub : p ∣ 2 ^ (6 * x) - (2 ^ (6 * x) - 1) := Nat.dvd_sub hp6 hpdvd
    have hone : 2 ^ (6 * x) - (2 ^ (6 * x) - 1) = 1 := by
      have hpos : 0 < 2 ^ (6 * x) := by positivity
      omega
    exact hp.not_dvd_one (hone ▸ hsub)
  have hpqZ : ¬ (p : ℤ) ∣ (2 : ℤ) ^ x := by
    intro h
    have h' : (p : ℤ) ∣ ((2 ^ x : ℕ) : ℤ) := by simpa using h
    exact hpq (Int.natCast_dvd_natCast.mp h')
  haveI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ x := by
    rw [Fintype.card_eq_nat_card, hK]
  have hGLformula := CFSG.GroupTheory.WeirSylow.natCard_GL_cast K d
  have hGLformula' :
      (Nat.card (GL (Fin d) K) : ℤ) =
        (∏ i : Fin d, (2 : ℤ) ^ (x * (i : ℕ))) *
          ∏ j ∈ Finset.Icc 1 d, ((2 : ℤ) ^ (x * j) - 1) := by
    rw [hGLformula, hcardK]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
    · apply Finset.prod_congr rfl
      intro j _
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  have hpGLZ : (p : ℤ) ∣ (Nat.card (GL (Fin d) K) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hpGL
  rw [hGLformula'] at hpGLZ
  have hprimeZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpdvdA : ¬ (p : ℤ) ∣ ∏ i : Fin d, (2 : ℤ) ^ (x * (i : ℕ)) := by
    refine hprimeZ.not_dvd_finsetProd ?_
    intro i _
    rw [pow_mul]
    exact fun h => hpqZ (hprimeZ.dvd_of_dvd_pow h)
  have hpB : (p : ℤ) ∣ ∏ j ∈ Finset.Icc 1 d, ((2 : ℤ) ^ (x * j) - 1) :=
    (hprimeZ.dvd_mul.mp hpGLZ).resolve_left hpdvdA
  obtain ⟨j, hjmem, hjdvd⟩ :=
    (Prime.dvd_finsetProd_iff hprimeZ (fun j : ℕ => (2 : ℤ) ^ (x * j) - 1)).1 hpB
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjmem).1
  have hjd : j ≤ d := (Finset.mem_Icc.mp hjmem).2
  have hjpos : 0 < x * j := Nat.mul_pos (by omega) hj1
  have hjlt : x * j < 6 * x := by
    have h := Nat.mul_lt_mul_of_pos_left (by omega : j < 6) (by omega : 0 < x)
    rwa [Nat.mul_comm x 6] at h
  have hjdvdNat : p ∣ 2 ^ (x * j) - 1 := by
    refine Int.natCast_dvd_natCast.mp ?_
    rw [Nat.cast_sub (by exact Nat.one_le_pow _ _ (by norm_num))]
    push_cast
    exact hjdvd
  exact hpprim (x * j) hjpos hjlt hjdvdNat

end CFSG.RankThree.GF2n.Stroth80
