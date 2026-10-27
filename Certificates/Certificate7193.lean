module

public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public meta import CFSG.Sporadic.Schreier.J1Tables
public meta import CFSG.Sporadic.Schreier.ClassSum
import Certificates.Certificate2164
import Certificates.Certificate2165
import Certificates.Certificate2166
import Certificates.Certificate2167
import CFSG.Sporadic.Schreier.J1Counts
import CFSG.Literature.GL52Group
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs

public section

open CFSG.Sporadic.Schreier CFSG.Literature.GL52

namespace Certificates

theorem card_orderOf_eq_21_of_card {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 175560)
    (h3 : Nat.card {g : G // orderOf g = 3} = 5852) : Nat.card {g : G // orderOf g = 21} = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : (Nat.card G).factorization 3 = 1 := by
    rw [hG, show (175560 : ℕ) = 3 * 58520 by norm_num, Nat.factorization_mul (by norm_num)
      (by norm_num), Finsupp.add_apply, Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [card_orderOf_eq_prime hf] at h3
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun ⟨x, hx⟩ => ?_⟩
  have ht : orderOf (x ^ 7) = 3 := by
    rw [orderOf_pow' x (by norm_num), hx]
    norm_num
  have hN := card_normalizer_mul_card_sylow (zpowersSylow hf (x ^ 7) ht)
  have key : ∀ h ∈ Subgroup.zpowers (x ^ 7), x * h * x⁻¹ = h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [((Commute.self_pow x 7).zpow_right k).eq, mul_inv_cancel_right]
  have hxN : x ∈ Subgroup.normalizer (zpowersSylow hf (x ^ 7) ht : Set G) := by
    change x ∈ Subgroup.normalizer ((Subgroup.zpowers (x ^ 7) : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => by rwa [key h hh], fun hh => ?_⟩
    have e : x * h * x⁻¹ = h :=
      (MulAut.conj x).injective (by simpa only [MulAut.conj_apply] using key _ hh)
    rwa [e] at hh
  have hd := Subgroup.orderOf_dvd_natCard _ hxN
  rw [hx] at hd
  have hs : Nat.card (Sylow 3 G) = 2926 := by omega
  rw [hG, hs] at hN
  have h60 : Nat.card ↥(Subgroup.normalizer (zpowersSylow hf (x ^ 7) ht : Set G)) = 60 := by
    omega
  rw [h60] at hd
  norm_num at hd

open CFSG.Sporadic.Schreier in
theorem certificate7193 : (j1OrderTables 21).length = 0 := by
  have := certificate2164
  have := certificate2165
  have := certificate2166
  have := certificate2167
  obtain ⟨Q, hrec, hQ, -, -, -, hP, hcard, -⟩ := fam_j1_order
  have hord : orderTables Q 21 = j1OrderTables 21 := by
    rw [orderTables, j1_levelTables hrec]
    rfl
  have h := card_orderOf_eq (by norm_num) Q hQ (m := 21) (by norm_num)
  rw [hord, hP] at h
  rw [← h]
  exact card_orderOf_eq_21_of_card hcard at_j1_image_pair_count.2.2.2.2.2.1

end Certificates
