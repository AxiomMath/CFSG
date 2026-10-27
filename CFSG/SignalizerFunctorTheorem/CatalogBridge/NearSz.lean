module

public import CFSG.Open.SignalizerFunctorDefs
import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection
import CFSG.Open.BenderStronglyEmbedded
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import CFSG.Timmesfeld.Orders.Bang
import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem not_three_dvd_two_pow (f : ℕ) : ¬ 3 ∣ 2 ^ f := fun h =>
  absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)

theorem three_dvd_sq_sub_one_of_not_dvd {q : ℕ} (h : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; exact h (dvd_zero 3))
  have h1 : q ^ 2 % 3 = 1 := by
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [Nat.pow_mod, h]
  have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ h0
  omega

theorem three_dvd_card_psl2_two_pow {f : ℕ} (hf : f ≠ 0) :
    3 ∣ Nat.card PSL(2, GaloisField 2 f) := by
  rw [McBride.NearSolvable.card_psl2_even hf]
  exact (three_dvd_sq_sub_one_of_not_dvd (not_three_dvd_two_pow f)).mul_left _

theorem three_dvd_card_psu3 {f : ℕ} (hf : 1 ≤ f) : 3 ∣ Nat.card (PSU3 2 f) := by
  have h := McBride.NearSolvable.card_psu3_mul_gcd hf
  have hq := not_three_dvd_two_pow f
  have h1 := three_dvd_sq_sub_one_of_not_dvd hq
  generalize 2 ^ f = q at h hq h1
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q + 1)) with hg | hg
  · rw [hg, mul_one] at h
    rw [h]
    exact (h1.mul_right _).mul_left _
  · have h3 : 3 ∣ q + 1 := by
      have := Nat.gcd_dvd_right 3 (q + 1)
      rwa [hg] at this
    have hq2 : q % 3 = 2 := by omega
    rw [hg] at h
    have h9 : 3 * 3 ∣ (q ^ 2 - 1) * (q ^ 3 + 1) :=
      mul_dvd_mul h1 (McBride.NearSolvable.three_dvd_cube_add_one hq2)
    have h9' : 3 * 3 ∣ Nat.card (PSU3 2 f) * 3 := by
      rw [h]
      exact h9.mul_left _
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h9'

theorem not_three_dvd_card_sz (n : ℕ) : ¬ 3 ∣ Nat.card (Sz n) := by
  rw [McBride.NearSolvable.card_sz]
  exact McBride.NearSolvable.not_three_dvd_suzuki
    (McBride.NearSolvable.two_pow_mod_three (odd_two_mul_add_one n))

theorem eq_of_card_sz_dvd
    {n a : ℕ} (hp : (2 * n + 1).Prime) (ha : 1 ≤ a)
    (hdvd : Nat.card (Sz a) ∣ Nat.card (Sz n)) : a = n := by
  rw [McBride.NearSolvable.card_sz, McBride.NearSolvable.card_sz] at hdvd
  have hk : 0 < 4 * (2 * a + 1) := by omega
  obtain ⟨ℓ, hℓ⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor
    (k := 4 * (2 * a + 1)) (by omega) (by omega)
  have hℓp : ℓ.Prime := hℓ.prime
  have h1 : ℓ ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [← pow_mul, mul_comm (2 * a + 1) 2]
    refine (hℓ.dvd_add_one_iff hk _).mpr ⟨⟨1, by ring⟩, ?_⟩
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have h2 : ℓ ∣ (2 ^ (2 * n + 1)) ^ 2 * ((2 ^ (2 * n + 1)) ^ 2 + 1) * (2 ^ (2 * n + 1) - 1) :=
    h1.trans (((dvd_mul_left _ _).mul_right _).trans hdvd)
  rcases hℓp.dvd_mul.mp h2 with h3 | h3
  · rcases hℓp.dvd_mul.mp h3 with h4 | h4
    · exfalso
      have h5 : ℓ ∣ 2 ^ (2 * n + 1) := hℓp.dvd_of_dvd_pow h4
      exact hℓ.ne_two hk ((Nat.prime_dvd_prime_iff_eq hℓp Nat.prime_two).mp
        (hℓp.dvd_of_dvd_pow h5))
    · rw [← pow_mul, mul_comm (2 * n + 1) 2] at h4
      have h5 := ((hℓ.dvd_add_one_iff hk _).mp h4).1
      have h6 : 2 * a + 1 ∣ 2 * n + 1 :=
        Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) (by
          rw [show 4 * (2 * n + 1) = 2 * (2 * (2 * n + 1)) by ring]
          exact h5)
      rcases hp.eq_one_or_self_of_dvd _ h6 with h7 | h7 <;> omega
  · exfalso
    have h5 := (hℓ.dvd_sub_one_iff hk _).mp h3
    have h6 : 4 ∣ 2 * n + 1 := (dvd_mul_right 4 _).trans h5
    omega

theorem nearSimpleModel_top_section {p : ℕ} {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hmodel : signalizerNearSimpleModel p Y) (L : Subgroup Y)
    [(L.subgroupOf (⊤ : Subgroup Y)).Normal]
    (hsimple : IsSimpleGroup ((⊤ : Subgroup Y) ⧸ L.subgroupOf (⊤ : Subgroup Y))) :
    signalizerNearSimpleModel p ((⊤ : Subgroup Y) ⧸ L.subgroupOf (⊤ : Subgroup Y)) := by
  have hLn : L.Normal := by
    have h := ‹(L.subgroupOf (⊤ : Subgroup Y)).Normal›.map (⊤ : Subgroup Y).subtype
      (fun y => ⟨⟨y, trivial⟩, rfl⟩)
    rwa [Subgroup.map_subgroupOf_eq_of_le le_top] at h
  have := hLn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L with hL | hL
  · subst hL
    let e : (⊤ : Subgroup Y) ⧸ (⊥ : Subgroup Y).subgroupOf ⊤ ≃* Y :=
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := ⊤))).trans
        (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
    exact TransportA.nearSimpleModel_of_mulEquiv e.symm hmodel
  · exfalso
    subst hL
    have : Subsingleton ((⊤ : Subgroup Y) ⧸ (⊤ : Subgroup Y).subgroupOf ⊤) := by
      rw [Subgroup.subgroupOf_self]
      exact QuotientGroup.subsingleton_quotient_top
    exact hsimple.toNontrivial.exists_pair_ne.elim fun a ⟨b, hab⟩ => hab (Subsingleton.elim a b)

theorem nearPSolvable_sz
    (n : ℕ) (hp : (2 * n + 1).Prime)
    (hcop : Nat.Coprime (2 * n + 1) (Nat.card (CFSG.Open.Sz n))) :
    CFSG.Open.signalizerNearPSolvable (2 * n + 1) (CFSG.Open.Sz n) := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_prime_one hp)
  have : IsSimpleGroup (Sz n) := McBride.SzModel.sz_isSimpleGroup hn
  refine ⟨hcop, ?_⟩
  intro K L hLK hnorm hsimple hnonab
  by_cases hK : K = ⊤
  · subst hK
    exact nearSimpleModel_top_section (Or.inr (Or.inr (Or.inl ⟨n, rfl, ⟨MulEquiv.refl _⟩⟩)))
      L hsimple
  · exfalso
    have hB := isBenderGroup_of_simple_section (CFSG.Open.Open.bender_suzuki_borel n hn) K L hLK
      hsimple hnonab
    have hdvdK : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
    have hdvd : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card (Sz n) :=
      hdvdK.trans (Subgroup.card_subgroup_dvd_card K)
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv] at hdvd
      exact not_three_dvd_card_sz n ((three_dvd_card_psl2_two_pow (by omega)).trans hdvd)
    · rw [Nat.card_congr e.toEquiv] at hdvd
      exact not_three_dvd_card_sz n ((three_dvd_card_psu3 (by omega)).trans hdvd)
    · rw [Nat.card_congr e.toEquiv] at hdvd
      obtain rfl := eq_of_card_sz_dvd hp ha hdvd
      refine hK ((Subgroup.card_eq_iff_eq_top K).mp (Nat.dvd_antisymm
        (Subgroup.card_subgroup_dvd_card K) ?_))
      rw [Nat.card_congr e.toEquiv] at hdvdK
      exact hdvdK

end CFSG.SignalizerFunctorTheorem.CatalogBridge
