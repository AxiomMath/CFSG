module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Index

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open Subgroup

namespace FA5

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_normalized_of_not_dvd {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (L B : Subgroup G) (hBq : IsPGroup q B) (hBL : B ≤ normalizer (L : Set G))
    (hcard : ¬ q ∣ Nat.card (Sylow p L)) :
    ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup p Q ∧
      (∀ n : ℕ, p ^ n ∣ Nat.card L → p ^ n ∣ Nat.card Q) ∧ B ≤ normalizer (Q : Set G) := by
  classical
  let φ : B →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  let _ : MulDistribMulAction B L := MulDistribMulAction.compHom L φ
  let _ : MulAction B (Sylow p L) := Sylow.pointwiseMulAction
  obtain ⟨Q₀, hQ₀⟩ := hBq.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p L) hcard
  refine ⟨(Q₀ : Subgroup L).map L.subtype, map_subtype_le _, Q₀.isPGroup'.map _,
    fun n hn => ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact Q₀.pow_dvd_card_of_pow_dvd_card hn
  · rw [le_normalizer_iff]
    rintro b hb _ ⟨y, hy, rfl⟩
    have hfix : (⟨b, hb⟩ : B) • Q₀ = Q₀ := (MulAction.mem_fixedPoints.mp hQ₀) ⟨b, hb⟩
    have hmem : (⟨b, hb⟩ : B) • y ∈ (Q₀ : Subgroup L) := by
      have h := Subgroup.smul_mem_pointwise_smul y (⟨b, hb⟩ : B) (Q₀ : Subgroup L) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    refine ⟨_, hmem, ?_⟩
    change (((L.normalizerMonoidHom) (Subgroup.inclusion hBL ⟨b, hb⟩)) y : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl

theorem centralizes_of_card_three {D Q : Subgroup G} (hD : Nat.card D = 3) (hQ : Nat.card Q = 5)
    (hN : D ≤ normalizer (Q : Set G)) : D ≤ centralizer (Q : Set G) := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcyc : IsCyclic Q := isCyclic_of_prime_card (p := 5) hQ
  let ψ : D →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hN)
  have hAut : Nat.card (MulAut Q) = 4 := by
    rw [IsCyclic.card_mulAut, hQ]
    decide
  intro d hd q hq
  have h3 : orderOf (ψ ⟨d, hd⟩) ∣ 3 :=
    (orderOf_map_dvd ψ _).trans (hD ▸ orderOf_dvd_natCard _)
  have h4 : orderOf (ψ ⟨d, hd⟩) ∣ 4 := hAut ▸ orderOf_dvd_natCard _
  have h1 : orderOf (ψ ⟨d, hd⟩) = 1 := by
    have := Nat.dvd_gcd h3 h4
    simpa using this
  have hid : ψ ⟨d, hd⟩ = 1 := orderOf_eq_one_iff.mp h1
  have h := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : G)) hid
  change ((Q.normalizerMonoidHom (Subgroup.inclusion hN ⟨d, hd⟩)) ⟨q, hq⟩ : G) = q at h
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  have h' : d * q * d⁻¹ = q := h
  calc q * d = d * q * d⁻¹ * d := by rw [h']
    _ = d * q := by group

namespace Pair

variable {L1 L2 S : Subgroup G} (h : Pair L1 L2 S)
include h

theorem card_left : ∃ b : ℕ, Nat.card L1 = 2 ^ b * 5 := by
  obtain ⟨k, -, hcard⟩ := h.card1
  have h1 : Nat.card L1 = Nat.card (OTwoQuot L1) * Nat.card (Open.pCore 2 L1) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.pCore 2 L1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥L1) 2).exists_card_eq
  refine ⟨k + a, ?_⟩
  rw [h1, hcard, ha]
  ring

theorem coprime_card_sylow_left : Nat.Coprime 5 (Nat.card (S ⊓ L1 : Subgroup G)) := by
  obtain ⟨c, hc⟩ := (h.hyp.hyp.h1.pgroup.to_le (inf_le_left : S ⊓ L1 ≤ S)).exists_card_eq
  rw [hc]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem exists_five {D : Subgroup G} (hD : D ≤ normalizer (L1 : Set G)) (hD3 : Nat.card D = 3) :
    ∃ X : Subgroup G, X ≤ L1 ∧ Nat.card X = 5 ∧ D ≤ centralizer (X : Set G) ∧
      X ⊓ borelOf L1 S = ⊥ ∧ ∀ l ∈ L1, ∃ x ∈ X, ∃ b ∈ borelOf L1 S, l = x * b := by
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h3 : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨b, hb⟩ := h.card_left
  have hf : (Nat.card L1).factorization 5 = 1 := by
    rw [hb, Nat.factorization_mul (by positivity) (by norm_num)]
    simp [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 2),
      Nat.Prime.factorization_self (by norm_num : Nat.Prime 5)]
  have hSyl : ¬ 3 ∣ Nat.card (Sylow 5 L1) := by
    obtain ⟨P⟩ : Nonempty (Sylow 5 L1) := inferInstance
    have hP : Nat.card (P : Subgroup L1) = 5 := by
      rw [P.card_eq_multiplicity, hf]
      norm_num
    have hidx : (P : Subgroup L1).index = 2 ^ b := by
      have := Subgroup.card_mul_index (P : Subgroup L1)
      rw [hP, hb] at this
      omega
    have hdvd : Nat.card (Sylow 5 L1) ∣ 2 ^ b := hidx ▸ Sylow.card_dvd_index P
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rw [hj]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hd
    omega
  have hDq : IsPGroup 3 D := IsPGroup.of_card (n := 1) (by simpa using hD3)
  obtain ⟨Q, hQL, hQp, hQcard, hDQ⟩ :=
    exists_sylow_normalized_of_not_dvd (p := 5) (q := 3) L1 D hDq hD hSyl
  have h5Q : 5 ∣ Nat.card Q := by
    have := hQcard 1 (by rw [hb]; simp)
    simpa using this
  have hQ5 : Nat.card Q = 5 := by
    obtain ⟨j, hj⟩ := hQp.exists_card_eq
    have hdvd : Nat.card Q ∣ Nat.card L1 := Subgroup.card_dvd_of_le hQL
    have hj1 : 1 ≤ j := by
      by_contra hlt
      have hj0 : j = 0 := by omega
      rw [hj, hj0] at h5Q
      norm_num at h5Q
    have hj2 : j ≤ 1 := by
      by_contra hgt
      have h25 : 5 ^ 2 ∣ Nat.card L1 := by
        refine (pow_dvd_pow 5 (by omega : 2 ≤ j)).trans ?_
        rw [← hj]
        exact hdvd
      rw [hb] at h25
      have : 5 ∣ 2 ^ b := by
        have h5 : 5 * 5 ∣ 5 * (2 ^ b) := by
          have : 5 ^ 2 ∣ 2 ^ b * 5 := h25
          rw [pow_two, mul_comm (2 ^ b)] at *
          exact this
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h5
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) this) (by norm_num)
    have : j = 1 := le_antisymm hj2 hj1
    rw [hj, this]
    norm_num
  have hcent : D ≤ centralizer (Q : Set G) := centralizes_of_card_three hD3 hQ5 hDQ
  have hinf : Q ⊓ borelOf L1 S = ⊥ := by
    have hB : borelOf L1 S = S ⊓ L1 := h.borelOf_left_eq
    have hcop := h.coprime_card_sylow_left
    have hd1 : Nat.card (Q ⊓ borelOf L1 S : Subgroup G) ∣ 5 := by
      rw [← hQ5]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card (Q ⊓ borelOf L1 S : Subgroup G) ∣ Nat.card (S ⊓ L1 : Subgroup G) := by
      rw [← hB]
      exact Subgroup.card_dvd_of_le inf_le_right
    have h1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact Subgroup.eq_bot_of_card_eq _ h1
  refine ⟨Q, hQL, hQ5, hcent, hinf, ?_⟩
  have hBL : borelOf L1 S ≤ L1 := F1.borelOf_le L1 S
  have hcardB : Nat.card ((borelOf L1 S).subgroupOf L1) = Nat.card (borelOf L1 S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  have hcardQ : Nat.card (Q.subgroupOf L1) = 5 := by
    rw [← hQ5]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  have hmulB := Subgroup.card_mul_index ((borelOf L1 S).subgroupOf L1)
  have hidx : ((borelOf L1 S).subgroupOf L1).index = 5 := h.relIndex_borelOf_left
  rw [hidx] at hmulB
  have hcop : Nat.Coprime (Nat.card (Q.subgroupOf L1))
      (Nat.card ((borelOf L1 S).subgroupOf L1)) := by
    rw [hcardQ, hcardB, h.borelOf_left_eq]
    exact h.coprime_card_sylow_left
  have hcompl : (Q.subgroupOf L1).IsComplement' ((borelOf L1 S).subgroupOf L1) := by
    refine isComplement'_of_coprime ?_ hcop
    rw [hcardQ, ← hmulB, mul_comm]
  intro l hl
  obtain ⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, hac⟩ := (Subgroup.isComplement'_def.mp hcompl).2 ⟨l, hl⟩
  have hl' : l = a * c := by simpa using congrArg Subtype.val hac.symm
  exact ⟨a, ha, c, hc, hl'⟩

end Pair

end FA5

end CFSG.Quasithin
