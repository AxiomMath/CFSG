module

public import CFSG.Quasithin.EmptyFaithful.S152XS5
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.S152X

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem eq_one_of_pow_two_pow_of_pow_three {X : Type*} [Group X] {x : X} {a : ℕ} (h2 : x ^ 2 ^ a = 1)
    (h3 : x ^ 3 = 1) : x = 1 := by
  have hd : orderOf x ∣ Nat.gcd (2 ^ a) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hg : Nat.gcd (2 ^ a) 3 = 1 := Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 3)
  rw [hg] at hd
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)

section Borel

variable [Finite G]

theorem not_oTwoUpper_le {B S : Subgroup G} (hSB : S ≤ B) (hn : B ≤ Subgroup.normalizer (S : Set G))
    (h3 : S.relIndex B = 3) : ¬ oTwoUpper B ≤ S := by
  intro hX
  have : (S.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).2 hn
  have hcard : Nat.card (↥B ⧸ S.subgroupOf B) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact h3
  have hBS : B ≤ S := by
    intro b hb
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper B hb
    have hq3 : (QuotientGroup.mk (⟨b, hb⟩ : ↥B) : ↥B ⧸ S.subgroupOf B) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥B ⧸ S.subgroupOf B)
        (x := (QuotientGroup.mk (⟨b, hb⟩ : ↥B) : ↥B ⧸ S.subgroupOf B))
      rwa [hcard] at this
    have hq2 : (QuotientGroup.mk (⟨b, hb⟩ : ↥B) : ↥B ⧸ S.subgroupOf B) ^ 2 ^ k = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hX hk
    have h1 := eq_one_of_pow_two_pow_of_pow_three hq2 hq3
    rw [QuotientGroup.eq_one_iff] at h1
    exact h1
  have := Subgroup.relIndex_eq_one.2 hBS
  omega

theorem oTwoUpper_borel {B S : Subgroup G} (hSB : S ≤ B) (hn : B ≤ Subgroup.normalizer (S : Set G))
    (hp : IsPGroup 2 S) (h3 : S.relIndex B = 3) :
    B ≤ oTwoUpper B ⊔ S ∧ (pCoreOf 2 (oTwoUpper B)).relIndex (oTwoUpper B) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXB : oTwoUpper B ≤ B := oTwoUpper_le B
  have hXS : ¬ oTwoUpper B ≤ S := not_oTwoUpper_le hSB hn h3
  have hZB : oTwoUpper B ⊔ S ≤ B := sup_le hXB hSB
  have hmul := Subgroup.relIndex_mul_relIndex S (oTwoUpper B ⊔ S) B le_sup_right hZB
  rw [h3] at hmul
  have hd : S.relIndex (oTwoUpper B ⊔ S) ∣ 3 := ⟨_, hmul.symm⟩
  have hZ3 : S.relIndex (oTwoUpper B ⊔ S) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
    · exfalso
      exact hXS (le_sup_left.trans (Subgroup.relIndex_eq_one.1 h1))
    · exact h1
  have hBZ : B ≤ oTwoUpper B ⊔ S := by
    rw [hZ3] at hmul
    exact Subgroup.relIndex_eq_one.1 (by omega)
  refine ⟨hBZ, ?_⟩
  have hZeq : oTwoUpper B ⊔ S = B := le_antisymm hZB hBZ
  have hXN : oTwoUpper B ≤ Subgroup.normalizer (S : Set G) := hXB.trans hn
  have hP3 : (oTwoUpper B ⊓ S).relIndex (oTwoUpper B) = 3 := by
    rw [Subgroup.inf_relIndex_left, ← F1.relIndex_sup_eq_of_le_normalizer hXN, hZeq]
    exact h3
  have hPN : oTwoUpper B ≤ Subgroup.normalizer ((oTwoUpper B ⊓ S : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hXN hg⟩
  have hPO : oTwoUpper B ⊓ S ≤ pCoreOf 2 (oTwoUpper B) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hPN (hp.to_le inf_le_right)
  have hOX : pCoreOf 2 (oTwoUpper B) ≤ oTwoUpper B := pCoreOf_le 2 _
  have hmul2 := Subgroup.relIndex_mul_relIndex (oTwoUpper B ⊓ S) (pCoreOf 2 (oTwoUpper B))
    (oTwoUpper B) hPO hOX
  rw [hP3] at hmul2
  have hd2 : (pCoreOf 2 (oTwoUpper B)).relIndex (oTwoUpper B) ∣ 3 := ⟨_, by rw [← hmul2, mul_comm]⟩
  rcases (Nat.dvd_prime Nat.prime_three).1 hd2 with h1 | h1
  · exfalso
    have hX2 : IsPGroup 2 (oTwoUpper B) :=
      (pCoreOf_isPGroup 2 (oTwoUpper B)).to_le (Subgroup.relIndex_eq_one.1 h1)
    obtain ⟨n, hn2⟩ := hX2.exists_card_eq
    have h1' := Subgroup.relIndex_mul_card (oTwoUpper B ⊓ S) (oTwoUpper B)
    rw [inf_eq_left.2 (inf_le_left : oTwoUpper B ⊓ S ≤ oTwoUpper B), hP3] at h1'
    have h3d : 3 ∣ 2 ^ n := by
      rw [← hn2, ← h1']
      exact Dvd.intro _ rfl
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    omega
  · exact h1

end Borel

section SelfNormalizing

variable [Finite G]

theorem inf_normalizer_eq_of_card {L S : Subgroup G} (hS : IsSylowTwoOf S L)
    (hF : Nat.card (OTwoQuot L) = 10 ∨ Nat.card (OTwoQuot L) = 20) :
    L ⊓ Subgroup.normalizer (S : Set G) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Subgroup ↥L := S.subgroupOf L with hS'
  set Q' : Subgroup ↥L := CFSG.Open.pCore 2 ↥L with hQ'
  have hQ'n : Q'.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hS2 : IsPGroup 2 S' := A4.isPGroup_subgroupOf_of_le hS.1 hS.2.1
  have hQS : Q' ≤ S' :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥L)).le_sylow_of_normal (hS2.toSylow hS.2.2)
  have hQidx : Q'.index = Nat.card (OTwoQuot L) := rfl
  have hQ1 : Q'.index ≠ 1 := by
    rw [hQidx]
    rcases hF with h | h <;> rw [h] <;> norm_num
  have hQ5 : Q'.index ≠ 5 := by
    rw [hQidx]
    rcases hF with h | h <;> rw [h] <;> norm_num
  have hSQ_of_normal : S'.Normal → S' = Q' := fun hnS =>
    le_antisymm (le_pCore 2 hnS hS2) hQS
  have hdvd1 : S'.index ∣ Q'.index := Subgroup.index_dvd_of_le hQS
  have hS5 : S'.index = 5 := by
    have hodd : ¬ 2 ∣ S'.index := hS.2.2
    have hcop : Nat.Coprime S'.index 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have h5 : S'.index ∣ 5 := by
      rw [hQidx] at hdvd1
      rcases hF with h | h
      · rw [h, show (10 : ℕ) = 5 * 2 by norm_num] at hdvd1
        exact hcop.dvd_of_dvd_mul_right hdvd1
      · rw [h, show (20 : ℕ) = 5 * 2 ^ 2 by norm_num] at hdvd1
        exact (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_right hdvd1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 h5 with h1 | h1
    · exfalso
      have htop : S' = ⊤ := Subgroup.index_eq_one.1 h1
      have hn : S'.Normal := by rw [htop]; exact Subgroup.normal_top
      exact hQ1 (by rw [← hSQ_of_normal hn, h1])
    · exact h1
  set N' : Subgroup ↥L := Subgroup.normalizer (S' : Set ↥L) with hN'
  have hSN : S' ≤ N' := Subgroup.le_normalizer
  have hN5 : N'.index = 5 := by
    have hd : N'.index ∣ 5 := hS5 ▸ Subgroup.index_dvd_of_le hSN
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hd with h1 | h1
    · exfalso
      have htop : N' = ⊤ := Subgroup.index_eq_one.1 h1
      have hn : S'.Normal := Subgroup.normalizer_eq_top_iff.1 htop
      exact hQ5 (by rw [← hSQ_of_normal hn, hS5])
    · exact h1
  have hNS : N' ≤ S' := by
    have h := Subgroup.relIndex_mul_index hSN
    rw [hN5, hS5] at h
    exact Subgroup.relIndex_eq_one.1 (by omega)
  have hEq : (L ⊓ Subgroup.normalizer (S : Set G)).subgroupOf L = S.subgroupOf L := by
    rw [inf_normalizer_subgroupOf' hS.1]
    exact le_antisymm hNS hSN
  have := Subgroup.subgroupOf_inj.1 hEq
  rw [inf_eq_left.2 (inf_le_left : L ⊓ Subgroup.normalizer (S : Set G) ≤ L),
    inf_eq_left.2 hS.1] at this
  exact this

end SelfNormalizing

end CFSG.Quasithin.S152X
