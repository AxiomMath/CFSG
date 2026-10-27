module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_sylowOf_three {C P Q : Subgroup G} (hP : IsSylowOf 3 P C) (hQ : IsPGroup 3 Q)
    (hQC : Q ≤ C) : Nat.card Q ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [L41.isSylowOf_card_p hP]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hd : 3 ^ k ∣ Nat.card C := hk ▸ Subgroup.card_dvd_of_le hQC
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num)
    ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp hd)

theorem eq_of_sylowOf_three_le {C P Q : Subgroup G} (hP : IsSylowOf 3 P C) (hQ : IsPGroup 3 Q)
    (hQC : Q ≤ C) (hPQ : P ≤ Q) : P = Q :=
  Subgroup.eq_of_le_of_card_ge hPQ (card_le_of_sylowOf_three hP hQ hQC)

theorem sylowOf_sup_zpowers {b : G} (hb : orderOf b = 3) {C As : Subgroup G}
    (hbC : b ∈ Nor C) (hbnot : b ∉ C) (hAs : IsSylowOf 3 As C) (hbAs : b ∈ Nor As) :
    IsSylowOf 3 (As ⊔ Subgroup.zpowers b) (C ⊔ Subgroup.zpowers b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbAs' : b ∉ As := fun h => hbnot (hAs.1 h)
  have hZC : Subgroup.zpowers b ≤ Subgroup.normalizer (C : Set G) := (Subgroup.zpowers_le).mpr hbC
  have hZAs : Subgroup.zpowers b ≤ Subgroup.normalizer (As : Set G) :=
    (Subgroup.zpowers_le).mpr hbAs
  have hcZ : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hb]
  have inf_bot : ∀ {H : Subgroup G}, b ∉ H → H ⊓ Subgroup.zpowers b = ⊥ := by
    intro H hbH
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    obtain ⟨hxH, hxz⟩ := hx
    have hxo : orderOf x = 3 := by
      have h1 : orderOf x ∣ 3 := by
        rw [← hb]; exact orderOf_dvd_of_mem_zpowers hxz
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers b := (Subgroup.zpowers_le).mpr hxz
    have heq : Subgroup.zpowers x = Subgroup.zpowers b := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hb]
    have : b ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers b
    exact hbH ((Subgroup.zpowers_le).mpr hxH this)
  have hN : Nat.card ↥(C ⊔ Subgroup.zpowers b) = Nat.card C * 3 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZC (inf_bot hbnot), hcZ]
  have hS : Nat.card ↥(As ⊔ Subgroup.zpowers b) = Nat.card As * 3 := by
    rw [CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hZAs (inf_bot hbAs'), hcZ]
  have hk := L41.isSylowOf_card_p hAs
  refine L41.isSylowOf_of_card_p (sup_le_sup_right hAs.1 _) ?_
  rw [hS, hN, hk, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply]
  have h3 : (3 : ℕ).factorization 3 = 1 := by simp [Nat.Prime.factorization Nat.prime_three]
  rw [h3, pow_succ]

theorem sylow_conj_core {b : G} (hb : orderOf b = 3) {C As R : Subgroup G}
    (hbC : b ∈ Nor C) (hbnot : b ∉ C) (hAs : IsSylowOf 3 As C) (hbAs : b ∈ Nor As)
    (hR3 : IsPGroup 3 R) (hbR : b ∈ R) (hRN : R ≤ C ⊔ Subgroup.zpowers b) :
    ∃ c ∈ C, (∀ y ∈ R ⊓ C, c * y * c⁻¹ ∈ As) ∧ c * b * c⁻¹ * b⁻¹ ∈ As := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT := sylowOf_sup_zpowers hb hbC hbnot hAs hbAs
  have hAsT : As ≤ As ⊔ Subgroup.zpowers b := le_sup_left
  have hbT : b ∈ As ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hTC : (As ⊔ Subgroup.zpowers b) ⊓ C = As := by
    refine (eq_of_sylowOf_three_le hAs (hT.2.1.to_inf_left) inf_le_right
      (le_inf hAsT hAs.1)).symm
  have hZC : Subgroup.zpowers b ≤ Subgroup.normalizer (C : Set G) := (Subgroup.zpowers_le).mpr hbC
  obtain ⟨k, hk, hkR⟩ := L41.exists_conj_le_sylowOf_p hT hRN hR3
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left C (Subgroup.zpowers b) hZC
  have hk' : k ∈ (C : Set G) * (Subgroup.zpowers b : Set G) := by
    rw [← hset]; exact hk
  obtain ⟨c, hc, z, hz, rfl⟩ := Set.mem_mul.mp hk'
  have hzR : z ∈ R := (Subgroup.zpowers_le).mpr hbR hz
  have hcR : ∀ x ∈ R, c * x * c⁻¹ ∈ As ⊔ Subgroup.zpowers b := by
    intro x hx
    have := hkR (z⁻¹ * x * z) (R.mul_mem (R.mul_mem (R.inv_mem hzR) hx) hzR)
    have e : c * z * (z⁻¹ * x * z) * (c * z)⁻¹ = c * x * c⁻¹ := by group
    rwa [e] at this
  refine ⟨c, hc, fun y hy => ?_, ?_⟩
  · rw [← hTC]
    exact ⟨hcR y hy.1, C.mul_mem (C.mul_mem hc hy.2) (C.inv_mem hc)⟩
  · rw [← hTC]
    refine ⟨(As ⊔ Subgroup.zpowers b).mul_mem (hcR b hbR) ((As ⊔ Subgroup.zpowers b).inv_mem hbT),
      ?_⟩
    have h1 : b * c⁻¹ * b⁻¹ ∈ C := by
      have := (Subgroup.mem_normalizer_iff.mp hbC c⁻¹).mp (C.inv_mem hc)
      exact this
    have e : c * b * c⁻¹ * b⁻¹ = c * (b * c⁻¹ * b⁻¹) := by group
    rw [e]
    exact C.mul_mem hc h1

theorem exp3_comm {b x w : G} {As : Subgroup G} (hcomm : IsMulCommutative As)
    (hbAs : b ∈ Nor As) (hx : x ∈ As) (hw : w ∈ As)
    (h : (w * b) * ((w * b) * x * (w * b)⁻¹ * x⁻¹) * (w * b)⁻¹ =
      (w * b) * x * (w * b)⁻¹ * x⁻¹) : ⁅⁅x, b⁆, b⁆ = 1 := by
  have hconj : ∀ y ∈ As, b * y * b⁻¹ ∈ As := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp hbAs y).mp hy
  have hcm : ∀ y ∈ As, ∀ z ∈ As, y * z = z * y := fun y hy z hz =>
    hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩ |> fun e => congrArg Subtype.val e
  have hbx := hconj x hx
  have ht : b * x * b⁻¹ * x⁻¹ ∈ As := As.mul_mem hbx (As.inv_mem hx)
  have hbt := hconj _ ht
  have e1 : (w * b) * x * (w * b)⁻¹ * x⁻¹ = b * x * b⁻¹ * x⁻¹ := by
    have := hcm w hw _ hbx
    calc (w * b) * x * (w * b)⁻¹ * x⁻¹ = (w * (b * x * b⁻¹)) * w⁻¹ * x⁻¹ := by group
      _ = ((b * x * b⁻¹) * w) * w⁻¹ * x⁻¹ := by rw [this]
      _ = b * x * b⁻¹ * x⁻¹ := by group
  rw [e1] at h
  have e2 : (w * b) * (b * x * b⁻¹ * x⁻¹) * (w * b)⁻¹ = b * (b * x * b⁻¹ * x⁻¹) * b⁻¹ := by
    have := hcm w hw _ hbt
    calc (w * b) * (b * x * b⁻¹ * x⁻¹) * (w * b)⁻¹
        = (w * (b * (b * x * b⁻¹ * x⁻¹) * b⁻¹)) * w⁻¹ := by group
      _ = ((b * (b * x * b⁻¹ * x⁻¹) * b⁻¹) * w) * w⁻¹ := by rw [this]
      _ = b * (b * x * b⁻¹ * x⁻¹) * b⁻¹ := by group
  rw [e2] at h
  have h' : b * (b * x * b⁻¹ * x⁻¹) = (b * x * b⁻¹ * x⁻¹) * b := by
    have := congrArg (· * b) h
    simpa [mul_assoc] using this
  have hv : ⁅x, b⁆ = (b * x * b⁻¹ * x⁻¹)⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [hv, commutatorElement_def]
  generalize b * x * b⁻¹ * x⁻¹ = t at h'
  calc t⁻¹ * b * t⁻¹⁻¹ * b⁻¹ = t⁻¹ * (b * t) * b⁻¹ := by group
    _ = t⁻¹ * (t * b) * b⁻¹ := by rw [h']
    _ = 1 := by group

end CFSG.RankThree.PartTwo.Sec21.FF79
