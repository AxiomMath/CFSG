module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Defs
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCSetup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.SPEBasics
import CFSG.GH74.GLS.SP.GenOrder
import TauCeti.GroupTheory.SemidirectProduct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC

open CFSG.Open (IsElemAbelian)

variable {X : Type} [Group X] [Finite X]

theorem good_m11Row {N K Q S : Subgroup X} (hQN : Q ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (Q : Set X))
    (hNK : N ⊓ K = K ⊓ Subgroup.normalizer (Q : Set X)) (hK : K = ⊤) (hE : IsElemAbelian 3 Q)
    (hQ9 : Nat.card ↥Q = 9) (hS : S ≤ K ⊓ Subgroup.normalizer (Q : Set X))
    (hsup : Q ⊔ S = K ⊓ Subgroup.normalizer (Q : Set X)) (hS16 : Nat.card ↥S = 16)
    (hSC : S ⊓ Subgroup.centralizer (Q : Set X) = ⊥) : SEFive.Good 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  subst hK
  haveI : IsMulCommutative ↥Q := hE.1
  have hQC : Q ≤ Subgroup.centralizer (Q : Set X) := Subgroup.le_centralizer Q
  have hQ3 : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num)
  have hSn : S ≤ Subgroup.normalizer (Q : Set X) := hS.trans inf_le_right
  have hCQ : Subgroup.centralizer (Q : Set X) ≤ Q := by
    intro c hc
    have hcΓ : c ∈ Q ⊔ S := by
      rw [hsup]
      exact ⟨Subgroup.mem_top c, Subgroup.centralizer_le_normalizer _ hc⟩
    obtain ⟨x, hx, s, hs, rfl⟩ := (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left hSn).1 hcΓ
    have hsC : x⁻¹ * (x * s) ∈ Subgroup.centralizer (Q : Set X) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hQC hx)) hc
    rw [inv_mul_cancel_left] at hsC
    have hs1 : s ∈ S ⊓ Subgroup.centralizer (Q : Set X) := ⟨hs, hsC⟩
    rw [hSC, Subgroup.mem_bot] at hs1
    rwa [hs1, mul_one]
  refine ⟨SEFive.pPrimeCore_eq_bot_of_centralizer_le hQN hQ3 hnorm hCQ, ?_⟩
  have hQS : Q ⊓ S = ⊥ := le_bot_iff.1 ((le_inf inf_le_right (inf_le_left.trans hQC)).trans hSC.le)
  have hcard : Nat.card ↥(N ⊓ ⊤) = 2 ^ 4 * 3 ^ 2 := by
    rw [hNK, ← hsup, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hSn hQS, hQ9, hS16]
    norm_num
  refine centralizerHasPElementOutside_of_pow_eq_one Nat.prime_three 4 2 fun y hy => ?_
  have h := pow_index_mul_card_eq_one (K := ⊤) hy
  rwa [Subgroup.index_top, one_mul, hcard] at h

theorem dihedral_nine_pow_nine :
    ∀ g h : DihedralGroup 9, h ^ 9 = 1 → h ^ 3 ≠ 1 → g * h = h * g → g ^ 9 = 1 := by
  decide

theorem pow_nine_of_commute {Γ : Subgroup X} (φ : ↥Γ ≃* DihedralGroup 9) {a b : X} (ha : a ∈ Γ)
    (hb : b ∈ Γ) (hb9 : b ^ 9 = 1) (hb3 : b ^ 3 ≠ 1) (hab : a * b = b * a) : a ^ 9 = 1 := by
  have h := dihedral_nine_pow_nine (φ ⟨a, ha⟩) (φ ⟨b, hb⟩)
    (by rw [← map_pow, EmbeddingLike.map_eq_one_iff]; exact Subtype.ext (by simpa using hb9))
    (by
      rw [← map_pow, Ne, EmbeddingLike.map_eq_one_iff]
      exact fun h => hb3 (by simpa using congrArg Subtype.val h))
    (by rw [← map_mul, ← map_mul]; exact congrArg φ (Subtype.ext (by simpa using hab)))
  rw [← map_pow, EmbeddingLike.map_eq_one_iff] at h
  simpa using congrArg Subtype.val h

theorem good_l28Row {N K Q : Subgroup X} [K.Normal] (hQN : Q ≤ N) (hQK : Q ≤ K)
    (hnorm : N ≤ Subgroup.normalizer (Q : Set X))
    (hNK : N ⊓ K = K ⊓ Subgroup.normalizer (Q : Set X)) (hidx : K.index = 3)
    (hQc : IsCyclic ↥Q) (hQ9 : Nat.card ↥Q = 9)
    (hD : Nonempty (↥(K ⊓ Subgroup.normalizer (Q : Set X)) ≃* DihedralGroup 9)) :
    SEFive.Good 3 N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hD
  have hQ3 : IsPGroup 3 ↥Q := IsPGroup.of_card (n := 2) (by rw [hQ9]; norm_num)
  obtain ⟨g, hg⟩ := @IsCyclic.exists_generator _ _ hQc
  have hog : orderOf (g : X) = 9 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hQ9]
  have hgΓ : (g : X) ∈ K ⊓ Subgroup.normalizer (Q : Set X) :=
    ⟨hQK g.2, Subgroup.le_normalizer g.2⟩
  have hg9 : (g : X) ^ 9 = 1 := hog ▸ pow_orderOf_eq_one _
  have hg3 : (g : X) ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by omega)
  have hO : CFSG.pPrimeCore 3 ↥N = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hz : y ^ 3 ∈ CFSG.pPrimeCore 3 ↥N := Subgroup.pow_mem _ hy 3
    have hzΓ : ((y ^ 3 : ↥N) : X) ∈ K ⊓ Subgroup.normalizer (Q : Set X) := by
      rw [← hNK]
      refine ⟨(y ^ 3).2, ?_⟩
      rw [Subgroup.coe_pow, ← hidx]
      exact K.pow_index_mem _
    have h9 := pow_nine_of_commute φ hzΓ hgΓ hg9 hg3 (commute_of_mem_pPrimeCore hQN hQ3 hnorm hz g.2)
    have h27 : y ^ 27 = 1 := Subtype.ext (by simpa [← pow_mul] using h9)
    have hcard : y ^ Nat.card ↥(CFSG.pPrimeCore 3 ↥N) = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨y, hy⟩ : ↥(CFSG.pPrimeCore 3 ↥N))))
    have hcop : Nat.Coprime (3 ^ 3) (Nat.card ↥(CFSG.pPrimeCore 3 ↥N)) :=
      Nat.Coprime.pow_left 3 (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥N))
    have h1 := pow_gcd_eq_one.2 ⟨h27, hcard⟩
    rwa [show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  refine ⟨hO, centralizerHasPElementOutside_of_pow_eq_one Nat.prime_three 1 3 fun y hy => ?_⟩
  have h := pow_index_mul_card_eq_one (K := K) hy
  rw [hidx, hNK, Nat.card_congr φ.toEquiv, DihedralGroup.nat_card] at h
  simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC
