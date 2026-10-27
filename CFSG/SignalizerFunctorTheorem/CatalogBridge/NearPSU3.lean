module

public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.Timmesfeld.Orders.Bang
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection
import CFSG.Open.BenderStronglyEmbedded
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic

public section

open CFSG.Open
open CFSG.Timmesfeld
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem prime_dvd_card_psu3_iff {f ℓ : ℕ} (hf : 1 ≤ f) (hℓ : ℓ.Prime) (h3 : ℓ ≠ 3) :
    ℓ ∣ Nat.card (PSU3 2 f) ↔ ℓ ∣ 2 ^ f ∨ ℓ ∣ 2 ^ (2 * f) - 1 ∨ ℓ ∣ 2 ^ (3 * f) + 1 := by
  have h := McBride.NearSolvable.card_psu3_mul_gcd hf
  have hsq : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hcu : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  rw [hsq, hcu] at h
  have hg : ¬ ℓ ∣ Nat.gcd 3 (2 ^ f + 1) := fun hd =>
    h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hd.trans (Nat.gcd_dvd_left _ _)))
  constructor
  · intro hd
    have h1 : ℓ ∣ 2 ^ (3 * f) * ((2 ^ (2 * f) - 1) * (2 ^ (3 * f) + 1)) :=
      h ▸ dvd_mul_of_dvd_left hd _
    rcases hℓ.dvd_mul.mp h1 with h2 | h2
    · exact Or.inl (hℓ.dvd_of_dvd_pow (by rwa [← hcu] at h2))
    · rcases hℓ.dvd_mul.mp h2 with h4 | h4
      · exact Or.inr (Or.inl h4)
      · exact Or.inr (Or.inr h4)
  · intro hd
    have h1 : ℓ ∣ 2 ^ (3 * f) * ((2 ^ (2 * f) - 1) * (2 ^ (3 * f) + 1)) := by
      rcases hd with h2 | h2 | h2
      · exact dvd_mul_of_dvd_left (hcu ▸ dvd_pow h2 (by norm_num)) _
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left h2 _) _
      · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right h2 _) _
    rw [← h] at h1
    exact (hℓ.dvd_mul.mp h1).resolve_right hg

theorem isPrimitivePrimeDivisor_dvd_card_psu3_iff {f k ℓ : ℕ} (hf : 1 ≤ f) (hk : 3 ≤ k)
    (hℓ : IsPrimitivePrimeDivisor ℓ k) :
    ℓ ∣ Nat.card (PSU3 2 f) ↔ k ∣ 2 * f ∨ (k ∣ 2 * (3 * f) ∧ ¬ k ∣ 3 * f) := by
  have hk0 : 0 < k := by omega
  have h2 : ℓ ≠ 2 := hℓ.ne_two hk0
  have h3 : ℓ ≠ 3 := fun h => by
    subst h
    have := hℓ.eq_two_of_dvd_three hk0 (dvd_refl _)
    omega
  have h4 : ¬ ℓ ∣ 2 ^ f := fun hd =>
    h2 ((Nat.prime_dvd_prime_iff_eq hℓ.prime Nat.prime_two).mp (hℓ.prime.dvd_of_dvd_pow hd))
  rw [prime_dvd_card_psu3_iff hf hℓ.prime h3, hℓ.dvd_sub_one_iff hk0, hℓ.dvd_add_one_iff hk0]
  simp [h4]

theorem isPrimitivePrimeDivisor_seven : IsPrimitivePrimeDivisor 7 3 :=
  ⟨by norm_num, by norm_num, fun j hj hjk => by interval_cases j <;> norm_num⟩

theorem two_dvd_card_psu3 {f : ℕ} (hf : 1 ≤ f) : 2 ∣ Nat.card (PSU3 2 f) :=
  (prime_dvd_card_psu3_iff hf Nat.prime_two (by norm_num)).mpr
    (Or.inl (dvd_pow_self 2 (by omega)))

theorem not_five_dvd_card_psu3 {f : ℕ} (hf : Odd f) : ¬ 5 ∣ Nat.card (PSU3 2 f) := by
  intro hd
  rw [McBride.NearSolvable.card_psu3_of_odd hf] at hd
  exact McBride.NearSolvable.not_five_dvd_unitary (McBride.NearSolvable.two_pow_mod_five hf)
    (hd.trans (McBride.NearSolvable.psu3_order_dvd (McBride.NearSolvable.two_pow_mod_three hf)))

theorem five_le_of_coprime_card_psu3 {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) : 5 ≤ p := by
  by_contra hlt
  have h2 := hp.two_le
  have h1 : 1 ≤ p := by omega
  have hd : p ∣ Nat.card (PSU3 2 p) := by
    interval_cases p
    · exact two_dvd_card_psu3 h1
    · exact three_dvd_card_psu3 h1
    · exact absurd hp (by norm_num)
  exact hp.one_lt.ne' (hcop.eq_one_of_dvd hd)

theorem eq_of_card_psl2_dvd {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hf : 2 ≤ f)
    (hdvd : Nat.card PSL(2, GaloisField 2 f) ∣ Nat.card (PSU3 2 p)) : f = p := by
  rw [McBride.NearSolvable.card_psl2_even (by omega)] at hdvd
  have hsq : (2 ^ f) ^ 2 = 2 ^ (2 * f) := by rw [← pow_mul, mul_comm]
  rw [hsq] at hdvd
  by_cases hf3 : f = 3
  · exfalso
    subst hf3
    have h7 : 7 ∣ Nat.card (PSU3 2 p) :=
      (by norm_num : 7 ∣ 2 ^ 3 * (2 ^ (2 * 3) - 1)).trans hdvd
    rcases (isPrimitivePrimeDivisor_dvd_card_psu3_iff (by omega) le_rfl
      isPrimitivePrimeDivisor_seven).mp h7 with h | ⟨-, h⟩
    · have h3 : 3 ∣ p := by omega
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
      omega
    · exact h (dvd_mul_right 3 p)
  · obtain ⟨ℓ, hℓ⟩ := exists_isPrimitivePrimeDivisor (k := 2 * f) (by omega) (by omega)
    have hℓN : ℓ ∣ Nat.card (PSU3 2 p) := hℓ.dvd.trans ((dvd_mul_left _ _).trans hdvd)
    rcases (isPrimitivePrimeDivisor_dvd_card_psu3_iff (by omega) (by omega) hℓ).mp hℓN with
      h | ⟨h, -⟩
    · have h1 : f ∣ p := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
      rcases (Nat.dvd_prime hp).mp h1 with h' | h' <;> omega
    · have h1 : f ∣ 3 * p := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
      obtain ⟨a, b, ha, hb, hab⟩ := Nat.dvd_mul.mp h1
      rcases (Nat.dvd_prime Nat.prime_three).mp ha with rfl | rfl <;>
        rcases (Nat.dvd_prime hp).mp hb with hb1 | hbp
      · omega
      · omega
      · omega
      · exfalso
        have hf3p : f = 3 * p := by omega
        subst hf3p
        obtain ⟨ℓ', hℓ'⟩ := exists_isPrimitivePrimeDivisor (k := 3 * p) (by omega) (by omega)
        have hdiv : 2 ^ (3 * p) - 1 ∣ 2 ^ (2 * (3 * p)) - 1 := by
          rw [IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one]
          exact dvd_mul_right _ _
        have hℓ'N : ℓ' ∣ Nat.card (PSU3 2 p) :=
          hℓ'.dvd.trans (hdiv.trans ((dvd_mul_left _ _).trans hdvd))
        rcases (isPrimitivePrimeDivisor_dvd_card_psu3_iff (by omega) (by omega) hℓ').mp hℓ'N with
          h | ⟨-, h⟩
        · have := Nat.le_of_dvd (by omega) h
          omega
        · exact h (dvd_refl _)

theorem eq_of_card_psu3_dvd {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hf : 2 ≤ f)
    (hdvd : Nat.card (PSU3 2 f) ∣ Nat.card (PSU3 2 p)) : f = p := by
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimitivePrimeDivisor (k := 6 * f) (by omega) (by omega)
  have hℓf : ℓ ∣ Nat.card (PSU3 2 f) :=
    (isPrimitivePrimeDivisor_dvd_card_psu3_iff (by omega) (by omega) hℓ).mpr
      (Or.inr ⟨⟨1, by ring⟩, Nat.not_dvd_of_pos_of_lt (by omega) (by omega)⟩)
  rcases (isPrimitivePrimeDivisor_dvd_card_psu3_iff (by omega) (by omega) hℓ).mp
    (hℓf.trans hdvd) with h | ⟨h, -⟩
  · have h1 : 3 * f ∣ p := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
      (by rw [show 2 * (3 * f) = 6 * f by ring]; exact h)
    rcases (Nat.dvd_prime hp).mp h1 with h' | h'
    · omega
    · have h3 : 3 ∣ p := ⟨f, h'.symm⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
      omega
  · have h1 : f ∣ p := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 6)
      (by rw [show 6 * p = 2 * (3 * p) by ring]; exact h)
    rcases (Nat.dvd_prime hp).mp h1 with h' | h' <;> omega

theorem five_dvd_card_sz (a : ℕ) : 5 ∣ Nat.card (Sz a) := by
  rw [McBride.NearSolvable.card_sz]
  exact ((McBride.NearSolvable.five_dvd_sq_add_one
    (McBride.NearSolvable.two_pow_mod_five (odd_two_mul_add_one a))).mul_left _).mul_right _

theorem nearPSolvable_psu3
    {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (CFSG.Open.PSU3 2 p))) :
    CFSG.Open.signalizerNearPSolvable p (CFSG.Open.PSU3 2 p) := by
  have h5 := five_le_of_coprime_card_psu3 hp hcop
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have : IsSimpleGroup (PSU3 2 p) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inr (Or.inl ⟨p, by omega, ⟨MulEquiv.refl _⟩⟩))
  refine ⟨hcop, ?_⟩
  intro K L hLK hnorm hsimple hnonab
  by_cases hK : K = ⊤
  · subst hK
    exact nearSimpleModel_top_section (Or.inr (Or.inr (Or.inr ⟨MulEquiv.refl _⟩))) L hsimple
  · have hB := isBenderGroup_of_simple_section (CFSG.Open.Open.bender_psu3_borel p (by omega))
      K L hLK hsimple hnonab
    have hdvdK : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card K := Subgroup.card_quotient_dvd_card _
    have hdvd : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card (PSU3 2 p) :=
      hdvdK.trans (Subgroup.card_subgroup_dvd_card K)
    rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · rw [Nat.card_congr e.toEquiv] at hdvd
      obtain rfl := eq_of_card_psl2_dvd hp h5 hf hdvd
      exact Or.inl ⟨e⟩
    · exfalso
      rw [Nat.card_congr e.toEquiv] at hdvd
      obtain rfl := eq_of_card_psu3_dvd hp h5 hf hdvd
      refine hK ((Subgroup.card_eq_iff_eq_top K).mp (Nat.dvd_antisymm
        (Subgroup.card_subgroup_dvd_card K) ?_))
      rw [Nat.card_congr e.toEquiv] at hdvdK
      exact hdvdK
    · exfalso
      rw [Nat.card_congr e.toEquiv] at hdvd
      exact not_five_dvd_card_psu3 hodd ((five_dvd_card_sz a).trans hdvd)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
