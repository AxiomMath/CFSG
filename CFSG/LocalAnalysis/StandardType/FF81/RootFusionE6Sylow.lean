module

public import Mathlib.GroupTheory.Sylow
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Coset.Card
import CFSG.Open.Defs

public section

namespace CFSG.StandardType.FF81

open scoped Pointwise

theorem exists_conj_mem_of_card_eq_mul {G : Type} [Group G] [Finite G] {C Q L : Subgroup G}
    (hQC : Q ≤ C) (hLC : L ≤ C) (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hQ3 : ¬ 3 ∣ Nat.card Q) (hQL : Q ⊓ L = ⊥) (hcard : Nat.card C = Nat.card Q * Nat.card L)
    {β : G} (hβ : β ∈ C) (hβ3 : orderOf β = 3) :
    ∃ q ∈ Q, q * β * q⁻¹ ∈ L := by
  have hCnorm : C ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer_iff.mpr hQn
  have hLnorm : L ≤ Subgroup.normalizer (Q : Set G) := hLC.trans hCnorm
  have hβnorm : Subgroup.zpowers β ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le.mpr hβ).trans hCnorm
  have hCeq : C = Q ⊔ L := by
    have hcard_sup : Nat.card (Q ⊔ L : Subgroup G) = Nat.card Q * Nat.card L := by
      have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := L) (K := Q) hLnorm
      rw [sup_comm, inf_comm, hQL, Subgroup.card_bot, mul_one] at h
      exact h.trans (mul_comm _ _)
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hQC hLC) ?_).symm
    exact le_of_eq (hcard.trans hcard_sup.symm)
  have hQβ : Q ⊓ Subgroup.zpowers β = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have hdvd : Nat.card (Q ⊓ Subgroup.zpowers β : Subgroup G) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : Q ⊓ Subgroup.zpowers β ≤ Subgroup.zpowers β)
      rwa [Nat.card_zpowers, hβ3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact h1
    · exfalso
      apply hQ3
      have hdiv := Subgroup.card_dvd_of_le (inf_le_left : Q ⊓ Subgroup.zpowers β ≤ Q)
      rwa [h3] at hdiv
  have hHcard : Nat.card (Q ⊔ Subgroup.zpowers β : Subgroup G) = 3 * Nat.card Q := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Subgroup.zpowers β) (K := Q) hβnorm
    rw [sup_comm, inf_comm, hQβ, Subgroup.card_bot, mul_one, Nat.card_zpowers, hβ3] at h
    exact h
  have hfacH : (Nat.card (Q ⊔ Subgroup.zpowers β : Subgroup G)).factorization 3 = 1 := by
    rw [hHcard, Nat.factorization_mul (by norm_num) (Nat.card_pos (α := ↥Q)).ne',
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hQ3, add_zero]
  have hβsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers β) (Q ⊔ Subgroup.zpowers β) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_sup_right (by
      rw [Nat.card_zpowers, hβ3, hfacH, pow_one])
  have hHC : Q ⊔ Subgroup.zpowers β ≤ C :=
    sup_le hQC (Subgroup.zpowers_le.mpr hβ)
  have hPnorm : L ⊓ (Q ⊔ Subgroup.zpowers β) ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    hCnorm (hHC hx.2)
  have hprod :
      (Q : Set G) * (((L ⊓ (Q ⊔ Subgroup.zpowers β)) : Subgroup G) : Set G) =
        ((Q ⊔ Subgroup.zpowers β : Subgroup G) : Set G) := by
    rw [Subgroup.mul_inf_assoc Q L (Q ⊔ Subgroup.zpowers β) le_sup_left]
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q L hLnorm]
    rw [← hCeq]
    exact Set.inter_eq_right.mpr hHC
  have hdedekind : (L ⊓ (Q ⊔ Subgroup.zpowers β)) ⊔ Q = Q ⊔ Subgroup.zpowers β := by
    apply le_antisymm
    · exact sup_le inf_le_right le_sup_left
    · intro x hx
      have hxprod : x ∈ (Q : Set G) * (((L ⊓ (Q ⊔ Subgroup.zpowers β)) : Subgroup G) : Set G) := by
        rw [hprod]
        exact hx
      rw [Set.mem_mul] at hxprod
      obtain ⟨q, hq, p, hp, rfl⟩ := hxprod
      exact mul_mem (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left hp)
  have hQP : (L ⊓ (Q ⊔ Subgroup.zpowers β)) ⊓ Q = ⊥ := by
    rw [inf_right_comm, inf_comm L Q, hQL, bot_inf_eq]
  have hcard_mul :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := L ⊓ (Q ⊔ Subgroup.zpowers β)) (K := Q) hPnorm
  have hPcard : Nat.card (L ⊓ (Q ⊔ Subgroup.zpowers β) : Subgroup G) = 3 := by
    have h := hcard_mul
    rw [hdedekind, hQP, Subgroup.card_bot, mul_one, hHcard] at h
    exact (Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Q)) h).symm
  have hPsyl :
      CFSG.ABGLocalTools.IsSylowOf 3 (L ⊓ (Q ⊔ Subgroup.zpowers β))
        (Q ⊔ Subgroup.zpowers β) :=
    CFSG.ABGLocalTools.isSylowOf_of_card inf_le_right (by
      rw [hPcard, hfacH, pow_one])
  obtain ⟨k, hkH, hkconj⟩ := hβsyl.exists_mem_conj hPsyl
  have hkβP : k * β * k⁻¹ ∈ L ⊓ (Q ⊔ Subgroup.zpowers β) := by
    apply (hkconj (k * β * k⁻¹)).mpr
    have hk : k⁻¹ * (k * β * k⁻¹) * k = β := by group
    rw [hk]
    exact Subgroup.mem_zpowers β
  have hkβL : k * β * k⁻¹ ∈ L := hkβP.1
  have hkprod : k ∈ (Q : Set G) * ((Subgroup.zpowers β) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q (Subgroup.zpowers β) hβnorm]
    exact hkH
  rw [Set.mem_mul] at hkprod
  obtain ⟨q, hqQ, z, hzβ, hqz⟩ := hkprod
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hzβ
  refine ⟨q, hqQ, ?_⟩
  have hkrewrite : k * β * k⁻¹ = q * β * q⁻¹ := by
    rw [← hqz, ← hi]
    group
  rwa [hkrewrite] at hkβL

end CFSG.StandardType.FF81
