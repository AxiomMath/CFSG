module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCartanF
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
public import CFSG.LocalAnalysis.WeakClosure81.SzStructureFacts
public import CFSG.GH74.Uniqueness.Section15HeringEnd2
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc22r3e5c_coe_eq_mul_of_card {B P C : Subgroup G} (hPB : P ≤ B)
    (hBP : B ≤ normalizer (P : Set G)) (hCB : C ≤ B)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card C))
    (hcard : Nat.card B = Nat.card P * Nat.card C) :
    (B : Set G) = (P : Set G) * (C : Set G) := by
  have hinf : C ⊓ P = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop.symm
  have hsup := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := C) (K := P) (hCB.trans hBP)
  rw [sup_comm] at hsup
  rw [hinf, Subgroup.card_bot, mul_one] at hsup
  have hle : P ⊔ C ≤ B := sup_le hPB hCB
  have heq : P ⊔ C = B :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hsup, hcard]; exact le_of_eq (mul_comm _ _))
  rw [← heq, Subgroup.coe_mul_of_right_le_normalizer_left P C (hCB.trans hBP)]

private theorem uc22r3e5c_exists_hall_invariant {B : Subgroup G} (hB : Group.IsSolvable ↥B)
    {b : G} (hbB : b ∈ normalizer (B : Set G)) (hcop : Nat.Coprime (orderOf b) (Nat.card B))
    {a m : ℕ} (hm : Odd m) (hcard : Nat.card B = 2 ^ a * m) :
    ∃ C : Subgroup G, C ≤ B ∧ Nat.card C = m ∧ b ∈ normalizer (C : Set G) := by
  let A : Subgroup G := Subgroup.zpowers b
  have hAcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
    show Nat.Coprime (Nat.card ↥(Subgroup.zpowers b)) (Nat.card ↥B)
    rw [Nat.card_zpowers]
    exact hcop
  letI : MulDistribMulAction ↥A ↥B :=
    CFSG.SignalizerFunctor.Helpers.conjugationAction A B (Subgroup.zpowers_le.mpr hbB)
  obtain ⟨C, hCHall, hCinv⟩ := CFSG.exists_isHallSubgroup_isInvariant
    (G := ↥B) (A := ↥A) hB hAcop {p : Nat.Primes | (p : ℕ) ≠ 2}
  have hCcard : Nat.card ↥C = m := uc22r3e5c_card_of_isHall_two (a := a) hCHall hm hcard
  set C₀ : Subgroup G := C.map B.subtype with hC₀
  have hC₀le : C₀ ≤ B := by
    rw [hC₀]
    exact Subgroup.map_subtype_le C
  have hC₀card : Nat.card ↥C₀ = m := by
    rw [hC₀, Subgroup.card_map_of_injective Subtype.coe_injective, hCcard]
  have hmap_mem : ∀ (a : ↥A), ∀ x ∈ C₀, (a : G) * x * (a : G)⁻¹ ∈ C₀ := by
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hz : a • y ∈ C :=
      (CFSG.IsInvariant.invariant (A := ↥A) (G := ↥B) (H := C) a y).mp hy
    exact Subgroup.mem_map.mpr ⟨a • y, hz, rfl⟩
  refine ⟨C₀, hC₀le, hC₀card, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hmap_mem ⟨b, Subgroup.mem_zpowers b⟩ x hx
  · intro hx
    have h1 := hmap_mem (⟨b, Subgroup.mem_zpowers b⟩ : ↥A)⁻¹ _ hx
    simpa [mul_assoc] using h1

theorem uc22r3e5c_exists_cartan_hall
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn : 2 < n) (hSz : IsSz (Bar2 L) n)
    {b : G} (hbB : b ∈ c.B0) (hb3 : orderOf b = 3) :
    ∃ C : Subgroup G,
      C ≤ conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) ∧
      Odd (Nat.card C) ∧ Nat.card C = (2 ^ n - 1) ^ 2 ∧
      b ∈ normalizer (C : Set G) ∧
      (conjClosure D.M L ⊓ normalizer (D.T ⊓ conjClosure D.M L : Set G) : Set G) =
        (D.T ⊓ conjClosure D.M L : Set G) * (C : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  let P : Subgroup G := D.T ⊓ conjClosure D.M L
  let β : Subgroup G := conjClosure D.M L ⊓ normalizer (P : Set G)
  have hcard : Nat.card ↥β = Nat.card ↥P * (2 ^ n - 1) ^ 2 :=
    uc22r3e5c_card_beta hL hKC hKne hset hSz
  have hP2 : IsPGroup 2 ↥P := (uc22r3e5c_isSylowTwoOf_inf hL).2.1
  obtain ⟨a, ha⟩ := hP2.exists_card_eq
  have h3not : ¬ 3 ∣ 2 ^ n - 1 :=
    CFSG.GH74.Uniqueness.Hering.three_not_dvd_two_pow_sub_one
      (CFSG.LocalAnalysis.WeakClosure81.SevenK.odd_and_three_le_of_isSz
        (uc22r3e5c_quasithin_isSz_of_isSz hSz)).1
  have hm : Odd ((2 ^ n - 1) ^ 2) :=
    (Nat.Even.sub_odd (Nat.one_le_two_pow)
      (Even.pow_of_ne_zero (by norm_num) (by omega : n ≠ 0)) odd_one).pow
  have hβcard : Nat.card ↥β = 2 ^ a * (2 ^ n - 1) ^ 2 := by
    rw [hcard, ha]
  have hcop : Nat.Coprime (orderOf b) (Nat.card ↥β) := by
    rw [hb3, hβcard]
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => ?_
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h1 | h1
    · exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
    · exact h3not (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1)
  have hbBc : b ∈ Subgroup.normalizer (β : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
      ⟨uc22r3e5c_B0_le_normalizer_conjClosure h5 h1930 c hL hc2 hbB,
        Subgroup.le_normalizer (H := Subgroup.normalizer (P : Set G))
          (uc22r3e5c_normalizes_inf h5 h1930 c hL hc2 hn hSz b hbB)⟩)
  obtain ⟨C, hCB, hCcard, hbC⟩ := uc22r3e5c_exists_hall_invariant
    (uc22r3e5c_isSolvable_beta hL hKC hKne hset hSz) hbBc hcop hm hβcard
  refine ⟨C, hCB, hCcard.symm ▸ hm, hCcard, hbC, ?_⟩
  exact uc22r3e5c_coe_eq_mul_of_card (le_inf inf_le_right (Subgroup.le_normalizer (H := P)))
    inf_le_right hCB (by rw [ha, hCcard]; exact (Nat.coprime_two_left.mpr hm).pow_left a)
    (by rw [hβcard, ha, hCcard])

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
