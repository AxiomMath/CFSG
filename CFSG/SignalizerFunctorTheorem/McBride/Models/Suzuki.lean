module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
import CFSG.SignalizerFunctorTheorem.NearModels.Main
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable
import CFSG.SignalizerFunctorTheorem.McBride.Models.OddFrame
import CFSG.SignalizerFunctorTheorem.McBride.Models.OddFrame.Items
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Aut
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.NearModels

namespace CFSG.SignalizerFunctorTheorem.McBride

namespace SzModel

theorem card_sz_zero : Nat.card (Sz 0) = 20 := by
  obtain ⟨e⟩ := Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
  rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (by simp)]
  norm_num

variable {n : ℕ}

theorem one_le_of_prime (hp : (2 * n + 1).Prime) : 1 ≤ n :=
  Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_prime_one hp)

theorem ne_five
    (hp : (2 * n + 1).Prime) (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n))) :
    2 * n + 1 ≠ 5 := by
  intro h5
  have hn := one_le_of_prime hp
  have hN := card_sz hn
  generalize Nat.card (Sz n) = N at hN hcop
  rw [h5] at hcop
  have h5d : 5 ∣ N := by
    rw [hN]
    exact ((five_dvd_sq_add_one n).mul_left _).mul_right _
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop h5d) (by norm_num)

theorem card_fixed
    (hp : (2 * n + 1).Prime) (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (f : MulAut (Sz n)) (hf : orderOf f = 2 * n + 1) :
    Nat.card (signalizerFixedSubgroup f) = 5 * (5 - 1) := by
  obtain ⟨e⟩ := sz_fixedSubgroup_mulEquiv n hp hcop f hf
  rw [Nat.card_congr e.toEquiv, card_sz_zero]

end SzModel

open SzModel

variable {n : ℕ}

theorem exists_aut_sz (hp : (2 * n + 1).Prime)
    (_hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n))) :
    ∃ f : MulAut (Sz n), orderOf f = 2 * n + 1 :=
  SzModel.exists_aut hp

theorem frame_sz
    (hp : (2 * n + 1).Prime) (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (hY : signalizerNearPSolvable (2 * n + 1) (Sz n)) (f : MulAut (Sz n))
    (hf : orderOf f = 2 * n + 1) : Frame (2 * n + 1) 5 f := by
  have hn := one_le_of_prime hp
  obtain ⟨e⟩ := sz_fixedSubgroup_mulEquiv n hp hcop f hf
  have hsol : Group.IsSolvable (signalizerFixedSubgroup f) := by
    have := isSolvable_sz_zero
    exact isSolvable_of_mulEquiv e
  have h25 : ¬ 5 ^ 2 ∣ Nat.card (Sz n) := by
    rw [card_sz hn]
    exact not_twentyfive_dvd_card hp (ne_five hp hcop)
  exact Frame.of_odd f hp (Or.inr rfl) hf hcop (sz_isSimpleGroup hn)
    (card_fixed hp hcop f hf) hsol h25 (sz_involution_centralizer hn)
    (fun _ hS hSp => sz_not_five_dvd_card_normalizer hn hS hSp)
    (fun H hH => isSolvable_of_lt_top_sz hp hY H hH)

theorem fixedCore1_sz (hp : (2 * n + 1).Prime)
    (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n))) (f : MulAut (Sz n))
    (hf : orderOf f = 2 * n + 1) : fixedCore1 f = signalizerFixedSubgroup f :=
  fixedCore1_eq_of_odd f (Or.inr rfl) (card_fixed hp hcop f hf)
    (sz_involution_centralizer (one_le_of_prime hp))

theorem itemC_sz
    (hp : (2 * n + 1).Prime) (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (f : MulAut (Sz n)) (hf : orderOf f = 2 * n + 1) : ItemC (2 * n + 1) f := by
  have hn := one_le_of_prime hp
  exact ItemC.of_inner hp (fun g hg => SzModel.exists_conj_of_coprime_orderOf hn g hg)
    fun _ hx => eq_one_of_commute_fixed_of_odd f (Or.inr rfl) (card_fixed hp hcop f hf)
      (sz_involution_centralizer hn) hx

theorem itemG_sz
    (hp : (2 * n + 1).Prime) (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (hY : signalizerNearPSolvable (2 * n + 1) (Sz n)) (f : MulAut (Sz n))
    (hf : orderOf f = 2 * n + 1) : ItemG (2 * n + 1) f :=
  ItemG.of_inner (frame_sz hp hcop hY f hf) fun g hg =>
    SzModel.exists_conj_of_coprime_orderOf (one_le_of_prime hp) g hg

theorem itemO_sz
    (hp : (2 * n + 1).Prime) (hcop : Nat.Coprime (2 * n + 1) (Nat.card (Sz n)))
    (hY : signalizerNearPSolvable (2 * n + 1) (Sz n)) (f : MulAut (Sz n))
    (hf : orderOf f = 2 * n + 1) : ItemO f := by
  have hn := one_le_of_prime hp
  have hF := frame_sz hp hcop hY f hf
  have hC := card_fixed hp hcop f hf
  obtain ⟨c, t, core, hFit⟩ :=
    OddFrame.exists_core f (Or.inr rfl) hC (sz_involution_centralizer hn)
  have hZ : Nat.card (Subgroup.centralizer (fixedFitting f : Set (Sz n))) ∣
      (2 ^ (2 * n + 1)) ^ 2 + 1 := by
    rw [hFit, OddFrame.centralizer_zpowers_eq]
    exact sz_card_centralizer_dvd hn core.ord_c
  have hM := hF.card_fixedNormalizer_dvd
  have hq8 : 8 ≤ 2 ^ (2 * n + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqodd : Odd (2 ^ (2 * n + 1) - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd (show 2 ^ (2 * n + 1) - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hqodd
    obtain ⟨j, hj⟩ := hrq
    omega
  have hr5 : r ≠ 5 := by
    rintro rfl
    exact not_five_dvd_two_pow_sub_one n hrq
  have hrZ : ¬ r ∣ (2 ^ (2 * n + 1)) ^ 2 + 1 := by
    intro hd
    obtain ⟨k, hk⟩ := hrq
    have hq : 2 ^ (2 * n + 1) = r * k + 1 := by omega
    have h2 : (2 ^ (2 * n + 1)) ^ 2 + 1 = r * (r * k * k + 2 * k) + 2 := by rw [hq]; ring
    rw [h2] at hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
      ((Nat.dvd_add_right (dvd_mul_right r _)).mp hd))
  have hrM : ¬ r ∣ Nat.card (fixedNormalizer f) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hr).mp (hd.trans hM) with h | h
    · exact hrZ (h.trans hZ)
    · rw [hC] at h
      rcases (Nat.Prime.dvd_mul hr).mp h with h5 | h4
      · exact hr5 ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h5)
      · have h4' : r ∣ 2 ^ 2 := by simpa using h4
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h4'))
  refine ⟨⟨r, hr, ?_, hrM⟩, fun r' hr' _ hr'M R => ?_⟩
  · rw [card_sz hn]
    exact Dvd.dvd.mul_left hrq _
  · have h2M : 2 ∣ Nat.card (fixedNormalizer f) := by
      have := Subgroup.orderOf_dvd_natCard (fixedNormalizer f)
        (fixed_le_fixedNormalizer f core.mem_t)
      rwa [core.ord_t] at this
    have hr'2 : r' ≠ 2 := fun h => hr'M (h ▸ h2M)
    have := Fact.mk hr'
    have := sz_oddSylow_isCyclic hr'2 R
    infer_instance

theorem outer_perfect_sz (hp : (2 * n + 1).Prime) :
    ∀ P : Subgroup (MulAut (Sz n)), Group.IsPerfect P →
      P ≤ (MulAut.conj : Sz n →* MulAut (Sz n)).range := fun P hP =>
  SzModel.perfect_le_inner (one_le_of_prime hp) P hP

theorem outer_coprime_pow_six_sz (hp : (2 * n + 1).Prime) :
    ∀ g : MulAut (Sz n), Nat.Coprime (2 * n + 1) (orderOf g) →
      g ^ 6 ∈ (MulAut.conj : Sz n →* MulAut (Sz n)).range := by
  intro g hg
  obtain ⟨x, rfl⟩ := SzModel.exists_conj_of_coprime_orderOf (one_le_of_prime hp) g hg
  exact ⟨x ^ 6, by rw [map_pow]⟩

end CFSG.SignalizerFunctorTheorem.McBride
