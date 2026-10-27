module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.RankThree.GF2n

open CFSG CFSG.Timmesfeld CFSG.RankThree.GF2n.Stroth80

theorem stroth37_artin_primitive_prime_not_dvd_card_gl {d e ℓ : ℕ} (he : 0 < e) (hd : d < e)
    (hℓ : ℓ.Prime) (hord : orderOf (2 : ZMod ℓ) = e) :
    ¬ ℓ ∣ Nat.card (GL (Fin d) (ZMod 2)) := by
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h0 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    rw [h0, orderOf_zero (ZMod 2)] at hord
    omega
  intro hdvd
  rw [Matrix.card_GL_field (n := d) (𝔽 := ZMod 2), ZMod.card] at hdvd
  obtain ⟨i, -, hi⟩ :=
    (hℓ.prime.dvd_finsetProd_iff (fun i : Fin d => 2 ^ d - 2 ^ (i : ℕ))).mp hdvd
  have hile : (i : ℕ) ≤ d := Nat.le_of_lt i.2
  have hfact : 2 ^ d - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (d - (i : ℕ)) - 1) := by
    have h1 : 2 ^ d = 2 ^ (i : ℕ) * 2 ^ (d - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hile]
    calc 2 ^ d - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * 2 ^ (d - (i : ℕ)) - 2 ^ (i : ℕ) * 1 := by
          rw [h1, mul_one]
      _ = 2 ^ (i : ℕ) * (2 ^ (d - (i : ℕ)) - 1) := (Nat.mul_sub_left_distrib ..).symm
  have hi' : ℓ ∣ 2 ^ (i : ℕ) * (2 ^ (d - (i : ℕ)) - 1) := hfact ▸ hi
  have hnot : ¬ ℓ ∣ 2 ^ (i : ℕ) := by
    intro h
    have h2 : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow h
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h2)
  have hdvd2 : ℓ ∣ 2 ^ (d - (i : ℕ)) - 1 :=
    (hℓ.coprime_iff_not_dvd.mpr hnot).dvd_of_dvd_mul_left hi'
  have hpow : (2 : ZMod ℓ) ^ (d - (i : ℕ)) = 1 :=
    (Bang.dvd_two_pow_sub_one_iff (d - (i : ℕ))).mp hdvd2
  have horddvd : e ∣ d - (i : ℕ) := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hpow
  have hpos : 0 < d - (i : ℕ) := by omega
  have hle : e ≤ d - (i : ℕ) := Nat.le_of_dvd hpos horddvd
  omega

end CFSG.RankThree.GF2n
