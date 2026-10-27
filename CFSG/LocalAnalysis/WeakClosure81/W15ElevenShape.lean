module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFifteenSetup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ : Subgroup G} {p : ℕ}

theorem inf_eq (c : Cfg1511 M V₀ V U S H P Q₀ p) : Q₀ ⊓ V₀ = v1Sub15 V₀ U :=
  c.odd.inf_eq c.w81 c.std c.cex c.hyp

theorem not_le_iHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) : ¬ Q₀ ≤ iHull15 V₀ U H :=
  c.odd.not_le_iHull15 c.cex c.hyp

theorem le_commutator_sup (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    Q₀ ≤ ⁅Q₀, V₀⁆ ⊔ iHull15 V₀ U H :=
  c.odd.le_commutator_sup c.inputs c.w81 c.std c.cex c.hyp

private theorem b15_mul_self_eq_one (c : Cfg1511 M V₀ V U S H P Q₀ p) {x : G}
    (hx : x ∈ V₀) : x * x = 1 := by
  have h := c.cex.hyp.elemAbelian₀.2 x hx
  simpa [pow_two] using h

private theorem b15_comm (c : Cfg1511 M V₀ V U S H P Q₀ p) {x y : G} (hx : x ∈ V₀)
    (hy : y ∈ V₀) : x * y = y * x :=
  B2F.isElemAbelian_comm c.cex.hyp.elemAbelian₀ hx hy

private theorem b15_exists_not_mem_v1Sub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    ∃ v ∈ V₀, v ∉ v1Sub15 V₀ U := by
  have hrel : (v1Sub15 V₀ U).relIndex V₀ = 2 := c.w81.relIndex_eq_two c.std c.cex
  have hnot : ¬ V₀ ≤ v1Sub15 V₀ U := by
    intro hle
    have h1 : (v1Sub15 V₀ U).relIndex V₀ = 1 := Subgroup.relIndex_eq_one.2 hle
    omega
  exact SetLike.not_le_iff_exists.1 hnot

private theorem b15_mul_mem_v1Sub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) {v w : G}
    (hv : v ∈ V₀) (hw : w ∈ V₀) (hv1 : v ∉ v1Sub15 V₀ U) (hw1 : w ∉ v1Sub15 V₀ U) :
    w * v ∈ v1Sub15 V₀ U := by
  have h : v⁻¹ * w ∈ v1Sub15 V₀ U :=
    inv_mul_mem_of_relIndex_eq_two (c.w81.relIndex_eq_two c.std c.cex) hv hw hv1 hw1
  have hinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left (b15_mul_self_eq_one c hv)
  rw [hinv, b15_comm c hv hw] at h
  exact h

private theorem b15_exists_mul_of_mem_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) {a : G}
    (ha : a ∈ kHull15 V₀ H) : ∃ q ∈ Q₀, ∃ w ∈ V₀, a = q * w := by
  have hnorm : V₀ ≤ normalizer (Q₀ : Set G) := c.hyp.V₀_le_H.trans c.odd.normal
  rw [← c.odd.sup_eq, sup_comm] at ha
  change a ∈ (↑(V₀ ⊔ Q₀) : Set G) at ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right V₀ Q₀ hnorm] at ha
  obtain ⟨w, hw, q, hq, hwq⟩ := ha
  refine ⟨w * q * w⁻¹, (Subgroup.mem_normalizer_iff.1 (hnorm hw) q).1 hq, w, hw, ?_⟩
  rw [← hwq]
  group

theorem relIndex_eq (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    (iHull15 V₀ U H).relIndex Q₀ = p ∨ (iHull15 V₀ U H).relIndex Q₀ = p ^ 3 := by
  haveI : ((iHull15 V₀ U H).subgroupOf Q₀).Normal := c.odd.normal_subgroupOf c.hyp
  have hshape := c.shape
  simp only [OddCoreShape15] at hshape
  rcases hshape with h | ⟨h, -, -⟩
  · left
    rwa [Subgroup.relIndex, Subgroup.index_eq_card]
  · right
    rwa [Subgroup.relIndex, Subgroup.index_eq_card]

theorem p_ne_two (c : Cfg1511 M V₀ V U S H P Q₀ p) : p ≠ 2 := by
  intro hp
  have hodd := c.odd.odd
  rcases c.relIndex_eq with h | h
  · rw [h, hp] at hodd
    exact (by decide : ¬ Odd (2 : ℕ)) hodd
  · rw [h, hp] at hodd
    exact (by decide : ¬ Odd (2 ^ 3 : ℕ)) hodd

theorem isPGroup_quot [hN : ((iHull15 V₀ U H).subgroupOf Q₀).Normal]
    (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    IsPGroup p (↥Q₀ ⧸ (iHull15 V₀ U H).subgroupOf Q₀) := by
  have hshape := c.shape
  simp only [OddCoreShape15] at hshape
  rcases hshape with h | ⟨h, -, -⟩
  · exact IsPGroup.of_card (n := 1) (by simpa using h)
  · exact IsPGroup.of_card (n := 3) (by simpa using h)

theorem relIndex_Q₀_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    Q₀.relIndex (kHull15 V₀ H) = 2 := by
  have hdvd : Q₀.relIndex (kHull15 V₀ H) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    obtain ⟨v₀, hv₀V, hv₀V1⟩ := b15_exists_not_mem_v1Sub15 c
    refine ⟨v₀, Hyp1510.V₀_le_kHull15 V₀ H hv₀V, fun b hb => ?_⟩
    obtain ⟨q, hq, w, hw, rfl⟩ := b15_exists_mul_of_mem_kHull15 c hb
    by_cases hw1 : w ∈ v1Sub15 V₀ U
    · right
      exact Q₀.mul_mem hq (c.odd.iHull_le (Hyp1510.v1Sub15_le_iHull15 V₀ U H hw1))
    · left
      have hwv : w * v₀ ∈ v1Sub15 V₀ U := b15_mul_mem_v1Sub15 c hv₀V hw hv₀V1 hw1
      have hmem : q * (w * v₀) ∈ Q₀ :=
        Q₀.mul_mem hq (c.odd.iHull_le (Hyp1510.v1Sub15_le_iHull15 V₀ U H hwv))
      simpa [mul_assoc] using hmem
  have hne : Q₀.relIndex (kHull15 V₀ H) ≠ 1 := by
    intro h1
    have hle : kHull15 V₀ H ≤ Q₀ := Subgroup.relIndex_eq_one.1 h1
    have hVQ : V₀ ≤ Q₀ := (Hyp1510.V₀_le_kHull15 V₀ H).trans hle
    have hV1 : V₀ ≤ v1Sub15 V₀ U := by
      rw [← c.inf_eq]
      exact le_inf hVQ le_rfl
    have hrel : (v1Sub15 V₀ U).relIndex V₀ = 2 := c.w81.relIndex_eq_two c.std c.cex
    rw [Subgroup.relIndex_eq_one.2 hV1] at hrel
    norm_num at hrel
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h hne
  · exact h

theorem exists_mul_of_mem_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) {a : G}
    (ha : a ∈ kHull15 V₀ H) : ∃ q ∈ Q₀, ∃ w ∈ V₀, a = q * w :=
  b15_exists_mul_of_mem_kHull15 c ha

theorem sylow_le (c : Cfg1511 M V₀ V U S H P Q₀ p) {X : Subgroup G}
    (hX : IsSylowIn p X (kHull15 V₀ H)) : X ≤ Q₀ := by
  intro x hx
  obtain ⟨q, hq, w, hw, rfl⟩ := b15_exists_mul_of_mem_kHull15 c (hX.le hx)
  have hnorm : V₀ ≤ normalizer (Q₀ : Set G) := c.hyp.V₀_le_H.trans c.odd.normal
  have hwqw : w * q * w⁻¹ ∈ Q₀ := (Subgroup.mem_normalizer_iff.1 (hnorm hw) q).1 hq
  have hx2 : (q * w) ^ 2 ∈ Q₀ := by
    have he : (q * w) ^ 2 = q * (w * q * w⁻¹) * (w * w) := by
      rw [pow_two]
      group
    rw [he, b15_mul_self_eq_one c hw, mul_one]
    exact Q₀.mul_mem hq hwqw
  obtain ⟨k, hk⟩ := hX.isPGroup ⟨q * w, hx⟩
  have hkG : (q * w) ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : Odd (p ^ k) := (c.prime.odd_of_ne_two c.p_ne_two).pow
  obtain ⟨m, hm⟩ := hodd
  have hx' : q * w = (((q * w) ^ 2) ^ m)⁻¹ := by
    have h1 : (q * w) ^ (p ^ k) = (q * w) * ((q * w) ^ 2) ^ m := by
      rw [hm, pow_succ', pow_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← h1, hkG])
  rw [hx']
  exact Q₀.inv_mem (Q₀.pow_mem hx2 m)

theorem sylow_sup (c : Cfg1511 M V₀ V U S H P Q₀ p) {X : Subgroup G}
    (hX : IsSylowIn p X (kHull15 V₀ H)) : X ⊔ iHull15 V₀ U H = Q₀ := by
  set A : Subgroup G := X ⊔ iHull15 V₀ U H with hA
  have hA_le : A ≤ Q₀ := sup_le (sylow_le c hX) c.odd.iHull_le
  have hQ_le_A : Q₀ ≤ A := by
    rw [← Subgroup.relIndex_eq_one]
    have hdvdI : A.relIndex Q₀ ∣ (iHull15 V₀ U H).relIndex Q₀ := by
      have h := Subgroup.relIndex_mul_relIndex (iHull15 V₀ U H) A Q₀ le_sup_right hA_le
      rw [← h]
      exact dvd_mul_left _ _
    have hdvd_p3 : A.relIndex Q₀ ∣ p ^ 3 := by
      rcases relIndex_eq c with h | h
      · exact hdvdI.trans (by rw [h]; exact dvd_pow_self p (n := 3) (by norm_num))
      · exact hdvdI.trans (by rw [h])
    have hXQ : X ≤ Q₀ := sylow_le c hX
    have hmulX : X.relIndex Q₀ * Q₀.relIndex (kHull15 V₀ H) = X.relIndex (kHull15 V₀ H) :=
      Subgroup.relIndex_mul_relIndex X Q₀ (kHull15 V₀ H) hXQ c.odd.le_kHull
    rw [relIndex_Q₀_kHull15 c] at hmulX
    have hpndvdX : ¬ p ∣ X.relIndex Q₀ := by
      intro hdiv
      apply hX.not_dvd_relIndex
      rw [← hmulX]
      exact dvd_mul_of_dvd_left hdiv 2
    have hdvdX : A.relIndex Q₀ ∣ X.relIndex Q₀ := by
      have h := Subgroup.relIndex_mul_relIndex X A Q₀ le_sup_left hA_le
      rw [← h]
      exact dvd_mul_left _ _
    have hpndvdA : ¬ p ∣ A.relIndex Q₀ := fun hdiv => hpndvdX (hdiv.trans hdvdX)
    exact Nat.eq_one_of_dvd_coprimes (c.prime.coprime_pow_of_not_dvd hpndvdA) dvd_rfl hdvd_p3
  exact le_antisymm hA_le hQ_le_A

theorem exists_mul_mul_of_mem_kHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) {X : Subgroup G}
    (hX : IsSylowIn p X (kHull15 V₀ H)) {a : G} (ha : a ∈ kHull15 V₀ H) :
    ∃ x ∈ X, ∃ i ∈ iHull15 V₀ U H, ∃ w ∈ V₀, a = x * i * w := by
  obtain ⟨q, hq, w, hw, rfl⟩ := b15_exists_mul_of_mem_kHull15 c ha
  have hqA : q ∈ X ⊔ iHull15 V₀ U H := by
    rw [sylow_sup c hX]
    exact hq
  have hnorm : X ≤ normalizer (iHull15 V₀ U H : Set G) :=
    hX.le.trans (c.hyp.kHull15_le.trans (Hyp1510.le_normalizer_iHull15 V₀ U H))
  change q ∈ (↑(X ⊔ iHull15 V₀ U H) : Set G) at hqA
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X (iHull15 V₀ U H) hnorm] at hqA
  obtain ⟨x, hx, i, hi, hxi⟩ := hqA
  refine ⟨x, hx, i, hi, w, hw, ?_⟩
  rw [← hxi]

theorem relIndex_iHull15_sup (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    (iHull15 V₀ U H).relIndex (V₀ ⊔ iHull15 V₀ U H) = 2 := by
  have hnorm : V₀ ≤ normalizer (iHull15 V₀ U H : Set G) :=
    c.hyp.V₀_le_H.trans (Hyp1510.le_normalizer_iHull15 V₀ U H)
  obtain ⟨v₀, hv₀V, hv₀V1⟩ := b15_exists_not_mem_v1Sub15 c
  have hdvd : (iHull15 V₀ U H).relIndex (V₀ ⊔ iHull15 V₀ U H) ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    refine ⟨v₀, Subgroup.mem_sup_left hv₀V, fun b hb => ?_⟩
    have hb' : b ∈ (↑(iHull15 V₀ U H ⊔ V₀) : Set G) := by
      rw [sup_comm]
      exact hb
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (iHull15 V₀ U H) V₀ hnorm] at hb'
    obtain ⟨i, hi, w, hw, hiw⟩ := hb'
    by_cases hw1 : w ∈ v1Sub15 V₀ U
    · right
      rw [← hiw]
      exact (iHull15 V₀ U H).mul_mem hi (Hyp1510.v1Sub15_le_iHull15 V₀ U H hw1)
    · left
      have hwv : w * v₀ ∈ v1Sub15 V₀ U := b15_mul_mem_v1Sub15 c hv₀V hw hv₀V1 hw1
      rw [← hiw, mul_assoc]
      exact (iHull15 V₀ U H).mul_mem hi (Hyp1510.v1Sub15_le_iHull15 V₀ U H hwv)
  have hne : (iHull15 V₀ U H).relIndex (V₀ ⊔ iHull15 V₀ U H) ≠ 1 := by
    intro h1
    have hle : V₀ ⊔ iHull15 V₀ U H ≤ iHull15 V₀ U H := Subgroup.relIndex_eq_one.1 h1
    exact c.hyp.not_V₀_le_iHull15 c.cex fun x hx => hle (Subgroup.mem_sup_left hx)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h hne
  · exact h

theorem isSylowIn_two_sup (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    IsSylowIn 2 (V₀ ⊔ iHull15 V₀ U H) (kHull15 V₀ H) := by
  have hW : V₀ ⊔ iHull15 V₀ U H ≤ kHull15 V₀ H :=
    sup_le (Hyp1510.V₀_le_kHull15 V₀ H) (Hyp1510.iHull15_le_kHull15 V₀ U H)
  refine ⟨hW, ?_, ?_⟩
  · exact c.hyp.sylow.isPGroup.to_le (sup_le c.hyp.V₀_le (c.hyp.iHull15_le_P c.cex))
  · have hrelW : (V₀ ⊔ iHull15 V₀ U H).relIndex (kHull15 V₀ H)
        = (iHull15 V₀ U H).relIndex Q₀ := by
      have h1 := Subgroup.relIndex_mul_relIndex (iHull15 V₀ U H) Q₀ (kHull15 V₀ H)
        c.odd.iHull_le c.odd.le_kHull
      have h2 := Subgroup.relIndex_mul_relIndex (iHull15 V₀ U H) (V₀ ⊔ iHull15 V₀ U H)
        (kHull15 V₀ H) le_sup_right hW
      rw [relIndex_Q₀_kHull15 c] at h1
      rw [relIndex_iHull15_sup c] at h2
      have hmain : 2 * (V₀ ⊔ iHull15 V₀ U H).relIndex (kHull15 V₀ H)
          = 2 * (iHull15 V₀ U H).relIndex Q₀ := by
        rw [h2, ← h1, mul_comm]
      exact mul_left_cancel₀ (by norm_num : (2 : ℕ) ≠ 0) hmain
    rw [hrelW]
    exact c.odd.odd.not_two_dvd_nat

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
