module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal

import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalFieldInner
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.Quasithin.Recognition.St84.Gen.AmalVertexLocal

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.ClassicalGroups.PCoreSection CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

private theorem odd_two_pow_sub_one_of_ne_zero {k : ℕ} (hk : k ≠ 0) : Odd (2 ^ k - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow ((show Even 2 by norm_num).pow_of_ne_zero hk) odd_one

section Amalgam

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem U4qLocalData.le_borelOf_left (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : S ≤ borelOf L1 S := by
  rw [borelOf_eq_inf_of_le (hD.le_left hH hS)]
  exact le_inf (hD.le_left hH hS) Subgroup.le_normalizer

private theorem U4qLocalData.le_borelOf_right (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) : S ≤ borelOf L2 S := by
  rw [borelOf_eq_inf_of_le (hD.le_right hH hS)]
  exact le_inf (hD.le_right hH hS) Subgroup.le_normalizer

theorem U4qLocalData.borelOf_inf_borelOf (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : borelOf L1 S ⊓ borelOf L2 S = S := by
  classical
  obtain ⟨F, hFfield, hFfin, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  obtain ⟨K, hKfield, -, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hFfield
  letI := hKfield
  letI := hFfin
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  obtain ⟨ρ, κ, hκ, -, -, -, -, -, hC⟩ := hD.exists_ringHom_field hH hS c₁ c₂
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hmem₁ : ∀ x : ↥L1, (x : G) ∈ S ↔ c₁.α x ∈ utri F := fun x =>
    (c₁.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  have hmem₂ : ∀ x : ↥L2, (x : G) ∈ S ↔ c₂.α x ∈ utri K := fun x =>
    (c₂.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  refine le_antisymm ?_ (le_inf (hD.le_borelOf_left hH hS) (hD.le_borelOf_right hH hS))
  rintro d ⟨hd1, hd2⟩
  have hdS : d ∈ Subgroup.normalizer (S : Set G) := mem_normalizer_of_mem_borelOf hSL1 hd1
  have hdL1 : d ∈ L1 := borelOf_le L1 S hd1
  have hdL2 : d ∈ L2 := borelOf_le L2 S hd2
  set A : SL(2, K) := c₂.α ⟨d, hdL2⟩ with hA_def
  have hA10 : A 1 0 = 0 := mem_borel_iff.mp
    ((mem_normalizer_iff_alpha_mem_borel hSL2 c₂.α c₂.surjective_α hmem₂ ⟨d, hdL2⟩).mp hdS)
  have h0 : (0 : K) ^ 2 ^ f = 0 := zero_pow (pow_ne_zero _ two_ne_zero)
  have hE : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K).map (· ^ 2 ^ f) =
      (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K).transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0]
  obtain ⟨z, hz⟩ := (c₂.range_iff _).mpr hE
  have hzZ : (z : G) ∈ centerOf (pCoreOf 2 L1) :=
    (c₂.mem_center_iff z).mpr ⟨by rw [hz]; simp, by rw [hz]; simp⟩
  have hdz : d * (z : G) * d⁻¹ = z := by
    have h := Subgroup.mem_centralizer_iff.mp (hD.center_left hdL1) _ hzZ
    rw [← h]
    group
  have hE' := c₂.equivariant ⟨d, hdL2⟩ z z hdz.symm
  rw [hz] at hE'
  have hA00 : A 0 0 * A 0 0 ^ 2 ^ f = 1 := by
    have h := congrFun (congrFun hE' 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← hA_def] at h
    linear_combination -1 * h
  have hdet : A 0 0 * A 1 1 = 1 := by
    have h := sl2_det A
    rw [hA10] at h
    linear_combination h
  have hdet' : A 0 0 ^ 2 ^ f * A 1 1 ^ 2 ^ f = 1 := by
    rw [← mul_pow, hdet, one_pow]
  have hN : A 1 1 * A 1 1 ^ 2 ^ f = 1 := by
    linear_combination (-(A 1 1 * A 1 1 ^ 2 ^ f)) * hA00 +
      (A 0 0 ^ 2 ^ f * A 1 1 ^ 2 ^ f) * hdet + hdet'
  set D : SL(2, F) := c₁.α ⟨d, hdL1⟩ with hD_def
  have hD10 : D 1 0 = 0 := mem_borel_iff.mp
    ((mem_normalizer_iff_alpha_mem_borel hSL1 c₁.α c₁.surjective_α hmem₁ ⟨d, hdL1⟩).mp hdS)
  obtain ⟨c, hcQ2, hcα⟩ := c₁.exists_pCoreOf_right hH hD hS 1
  have hv2 : d * c * d⁻¹ ∈ pCoreOf 2 L2 := conj_mem_pCoreOf hdL2 hcQ2
  have hv1 : d * c * d⁻¹ ∈ L1 := L1.mul_mem (L1.mul_mem hdL1 c.2) (L1.inv_mem hdL1)
  have hαv : (c₁.α ⟨d * c * d⁻¹, hv1⟩ : Matrix (Fin 2) (Fin 2) F) 0 1 = D 0 0 ^ 2 := by
    have e : (⟨d * c * d⁻¹, hv1⟩ : ↥L1) = ⟨d, hdL1⟩ * c * ⟨d, hdL1⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, eq_utriElt_of_eq_unitri hcα, ← hD_def,
      conj_utriElt_apply_01, mul_one]
  have hC1 := hC c hcQ2 c.2
  have hC2 := hC (d * c * d⁻¹) hv2 hv1
  rw [hαv] at hC2
  rw [Subtype.coe_eta, hcα] at hC1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, map_one, mul_one] at hC1
  have h11 : Multiplicative.toAdd (c₂.β ⟨d * c * d⁻¹, hv2⟩) 1 1 =
      A 1 1 * Multiplicative.toAdd (c₂.β ⟨c, hcQ2⟩) 1 1 * A 1 1 ^ 2 ^ f := by
    rw [c₂.equivariant ⟨d, hdL2⟩ ⟨c, hcQ2⟩ ⟨_, hv2⟩ rfl]
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA10, h0, ← hA_def]
  rw [hC1, hC2] at h11
  have hρ : ρ (D 0 0 ^ 2) = ρ 1 := by
    apply mul_left_cancel₀ hκ
    rw [map_one, mul_one, h11]
    linear_combination κ * hN
  have hD00 : D 0 0 = 1 := CharTwo.sq_injective (by simpa using ρ.injective hρ)
  exact (hmem₁ ⟨d, hdL1⟩).mpr (mem_utri_entries.mpr ⟨hD10, hD00⟩)

private theorem U4qLocalData.borelOf_right_le_normalizer_left (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    borelOf L2 S ≤ Subgroup.normalizer (borelOf L1 S : Set G) := by
  intro b hb
  have hbS := mem_normalizer_of_mem_borelOf (hD.le_right hH hS) hb
  rw [borelOf_eq_inf_of_le (hD.le_left hH hS)]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hH.h1.borel_le hb, Subgroup.le_normalizer hbS⟩

private theorem U4qLocalData.borelOf_left_le_normalizer_right (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    borelOf L1 S ≤ Subgroup.normalizer (borelOf L2 S : Set G) := by
  intro b hb
  have hbS := mem_normalizer_of_mem_borelOf (hD.le_left hH hS) hb
  rw [borelOf_eq_inf_of_le (hD.le_right hH hS)]
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hH.h2.borel_le hb, Subgroup.le_normalizer hbS⟩

theorem U4qLocalData.bigB_eq_sup (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : bigB L1 L2 S = borelOf L1 S ⊔ borelOf L2 S :=
  sup_eq_left.mpr ((hD.le_borelOf_left hH hS).trans le_sup_left)

theorem U4qLocalData.bigB_le_normalizer (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) :
    bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) ⊓ Subgroup.normalizer (L2 : Set G) ⊓
      Subgroup.normalizer (S : Set G) := by
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  refine sup_le (sup_le ?_ ?_) ?_
  · intro b hb
    exact ⟨⟨Subgroup.le_normalizer (borelOf_le L1 S hb), hH.h2.borel_le hb⟩,
      mem_normalizer_of_mem_borelOf hSL1 hb⟩
  · intro b hb
    exact ⟨⟨hH.h1.borel_le hb, Subgroup.le_normalizer (borelOf_le L2 S hb)⟩,
      mem_normalizer_of_mem_borelOf hSL2 hb⟩
  · intro s hs
    exact ⟨⟨hH.h1.normalizes hs, hH.h2.normalizes hs⟩, Subgroup.le_normalizer hs⟩

theorem U4qLocalData.normal_subgroupOf_bigB (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    (S.subgroupOf (bigB L1 L2 S)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer ((hD.bigB_le_normalizer hH hS).trans inf_le_right)

theorem U4qLocalData.commutator_mem_of_mem_bigB (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    ∀ x ∈ bigB L1 L2 S, ∀ y ∈ bigB L1 L2 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
  classical
  obtain ⟨F, hFfield, -, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  obtain ⟨K, hKfield, -, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hFfield
  letI := hKfield
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hmem₁ : ∀ x : ↥L1, (x : G) ∈ S ↔ c₁.α x ∈ utri F := fun x =>
    (c₁.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  have hmem₂ : ∀ x : ↥L2, (x : G) ∈ S ↔ c₂.α x ∈ utri K := fun x =>
    (c₂.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  have hB₁ := mem_borelOf_iff_alpha_mem_borel hSL1 c₁.α c₁.surjective_α hmem₁
  have hB₂ := mem_borelOf_iff_alpha_mem_borel hSL2 c₂.α c₂.surjective_α hmem₂
  have h11 : ∀ x ∈ borelOf L1 S, ∀ y ∈ borelOf L1 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    exact commutator_mem_of_alpha_mem_borel c₁.α hmem₁
      ((hB₁ ⟨x, borelOf_le L1 S hx⟩).mp hx) ((hB₁ ⟨y, borelOf_le L1 S hy⟩).mp hy)
  have h22 : ∀ x ∈ borelOf L2 S, ∀ y ∈ borelOf L2 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    exact commutator_mem_of_alpha_mem_borel c₂.α hmem₂
      ((hB₂ ⟨x, borelOf_le L2 S hx⟩).mp hx) ((hB₂ ⟨y, borelOf_le L2 S hy⟩).mp hy)
  have hN21 := hD.borelOf_right_le_normalizer_left hH hS
  have hN12 := hD.borelOf_left_le_normalizer_right hH hS
  have h12 : ∀ x ∈ borelOf L1 S, ∀ y ∈ borelOf L2 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    rw [← hD.borelOf_inf_borelOf hH hS]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hN21 hy) x⁻¹).mp (inv_mem hx)
      have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hx h
    · have h := (Subgroup.mem_normalizer_iff.mp (hN12 hx) y).mp hy
      exact mul_mem h (inv_mem hy)
  have h21 : ∀ x ∈ borelOf L2 S, ∀ y ∈ borelOf L1 S, x * y * x⁻¹ * y⁻¹ ∈ S := by
    intro x hx y hy
    have h := inv_mem (h12 y hy x hx)
    have e : (y * x * y⁻¹ * x⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
    rwa [e] at h
  haveI := hD.normal_subgroupOf_bigB hH hS
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  intro x hx y hy
  have hx' : x ∈ borelOf L1 S ⊔ borelOf L2 S := by rw [← hD.bigB_eq_sup hH hS]; exact hx
  have hy' : y ∈ borelOf L1 S ⊔ borelOf L2 S := by rw [← hD.bigB_eq_sup hH hS]; exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hN21).mp hx'
  obtain ⟨c, hc, e, he, rfl⟩ := (mem_sup_iff_exists_mul_of_normalizes hN21).mp hy'
  refine (commute_mk_iff_commutator_mem (S := S) (⟨a, hB1B ha⟩ * ⟨b, hB2B hb⟩ : ↥(bigB L1 L2 S))
    (⟨c, hB1B hc⟩ * ⟨e, hB2B he⟩)).mp ?_
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
  have hac := (commute_mk_iff_commutator_mem ⟨a, hB1B ha⟩ ⟨c, hB1B hc⟩).mpr (h11 a ha c hc)
  have hae := (commute_mk_iff_commutator_mem ⟨a, hB1B ha⟩ ⟨e, hB2B he⟩).mpr (h12 a ha e he)
  have hbc := (commute_mk_iff_commutator_mem ⟨b, hB2B hb⟩ ⟨c, hB1B hc⟩).mpr (h21 b hb c hc)
  have hbe := (commute_mk_iff_commutator_mem ⟨b, hB2B hb⟩ ⟨e, hB2B he⟩).mpr (h22 b hb e he)
  exact (hac.mul_right hae).mul_left (hbc.mul_right hbe)

theorem U4qLocalData.card_borelOf_left (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : Nat.card (borelOf L1 S) = 2 ^ (6 * f) * (2 ^ f - 1) := by
  classical
  obtain ⟨F, hFfield, -, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  letI := hFfield
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hmem₁ : ∀ x : ↥L1, (x : G) ∈ S ↔ c₁.α x ∈ utri F := fun x =>
    (c₁.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  rw [card_eq_card_mul_card_of_alpha c₁.α c₁.surjective_α c₁.eq_one_iff (borelOf_le L1 S)
    (hH.pCoreOf_le_left.trans (hD.le_borelOf_left hH hS)) (borel F)
    (mem_borelOf_iff_alpha_mem_borel hSL1 c₁.α c₁.surjective_α hmem₁), hD.card_left,
    card_borel, c₁.card, show 6 * f = 5 * f + f by ring, pow_add, mul_assoc]

theorem U4qLocalData.card_borelOf_right (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) : Nat.card (borelOf L2 S) = 2 ^ (6 * f) * (4 ^ f - 1) := by
  classical
  obtain ⟨K, hKfield, -, ⟨c₂⟩⟩ := hD.exists_coordRight hH hS
  letI := hKfield
  have hSL2 : S ≤ L2 := hD.le_right hH hS
  have hmem₂ : ∀ x : ↥L2, (x : G) ∈ S ↔ c₂.α x ∈ utri K := fun x =>
    (c₂.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  rw [card_eq_card_mul_card_of_alpha c₂.α c₂.surjective_α c₂.eq_one_iff (borelOf_le L2 S)
    (hH.pCoreOf_le_right.trans (hD.le_borelOf_right hH hS)) (borel K)
    (mem_borelOf_iff_alpha_mem_borel hSL2 c₂.α c₂.surjective_α hmem₂), hD.card_right,
    card_borel, c₂.card, show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num,
    show 6 * f = 4 * f + 2 * f by ring, pow_add, mul_assoc]

theorem U4qLocalData.card_bigB (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) :
    Nat.card (bigB L1 L2 S) = 2 ^ (6 * f) * ((2 ^ f - 1) * (4 ^ f - 1)) := by
  have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (hD.borelOf_right_le_normalizer_left hH hS)
  rw [sup_comm, inf_comm, ← hD.bigB_eq_sup hH hS, hD.borelOf_inf_borelOf hH hS, hS,
    hD.card_borelOf_left hH hS, hD.card_borelOf_right hH hS] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ (6 * f) by positivity)
  rw [h]
  ring

theorem U4qLocalData.exists_hall_bigB (hH : Hyp111 L1 L2 S) (hD : U4qLocalData L1 L2 S f)
    (hS : Nat.card S = 2 ^ (6 * f)) :
    ∃ H : Subgroup G, H ≤ bigB L1 L2 S ∧ S ⊔ H = bigB L1 L2 S ∧ S ⊓ H = ⊥ ∧
      Nat.card H = (2 ^ f - 1) * (4 ^ f - 1) ∧ ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  have hf := hD.one_le
  have hodd : Odd ((2 ^ f - 1) * (4 ^ f - 1)) := by
    refine (odd_two_pow_sub_one_of_ne_zero (by omega)).mul ?_
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact odd_two_pow_sub_one_of_ne_zero (by omega)
  have hcop : Nat.Coprime (2 ^ (6 * f)) ((2 ^ f - 1) * (4 ^ f - 1)) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) :=
    (hD.bigB_le_normalizer hH hS).trans inf_le_right
  have hSB : S ≤ bigB L1 L2 S := le_sup_right
  obtain ⟨H, hHB, hsup, hcard⟩ := exists_sup_eq_of_coprime hSB hBN ((2 ^ f - 1) * (4 ^ f - 1))
    (by rw [hD.card_bigB hH hS, hS]) (by rw [hS]; exact hcop)
  have hinf : S ⊓ H = ⊥ := Subgroup.inf_eq_bot_of_coprime (by rw [hS, hcard]; exact hcop)
  refine ⟨H, hHB, hsup, hinf, hcard, fun a ha b hb => ?_⟩
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ S ⊓ H := Subgroup.mem_inf.mpr
    ⟨hD.commutator_mem_of_mem_bigB hH hS a (hHB ha) b (hHB hb),
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)⟩
  rw [hinf, Subgroup.mem_bot] at h1
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)

private theorem U4qLocalData.borelOf_right_le_sup_trivOTwoQuot (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    borelOf L2 S ≤ borelOf L1 S ⊔ (bigB L1 L2 S ⊓ trivOTwoQuot L1) := by
  classical
  obtain ⟨F, hFfield, -, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  letI := hFfield
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hmem₁ : ∀ x : ↥L1, (x : G) ∈ S ↔ c₁.α x ∈ utri F := fun x =>
    (c₁.mem_iff x).trans mem_utri_iff_eq_unitri.symm
  intro b hb
  obtain ⟨g, hgL, hg⟩ := hD.exists_inner_borelOf_right hH hS b hb
  have hbS := mem_normalizer_of_mem_borelOf (hD.le_right hH hS) hb
  have hgS : ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro s hs
    have h1 := hg s (hSL1 hs)
    have h2 : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hbS s).mp hs
    have e : g * s * g⁻¹ = (b * s * b⁻¹ * (g * s * g⁻¹)⁻¹)⁻¹ * (b * s * b⁻¹) := by group
    rw [e]
    exact mul_mem (inv_mem (hH.pCoreOf_le_left h1)) h2
  have hgB : g ∈ borelOf L1 S :=
    (mem_borelOf_iff_alpha_mem_borel hSL1 c₁.α c₁.surjective_α hmem₁ ⟨g, hgL⟩).mpr
      (alpha_mem_borel_of_conj_mem c₁.α c₁.surjective_α hmem₁ (d := ⟨g, hgL⟩) hgS)
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  have hX : g⁻¹ * b ∈ bigB L1 L2 S ⊓ trivOTwoQuot L1 := by
    refine Subgroup.mem_inf.mpr
      ⟨mul_mem (inv_mem (hB1B hgB)) (hB2B hb), mem_trivOTwoQuot.mpr ⟨?_, fun x hx => ?_⟩⟩
    · exact mul_mem (inv_mem (Subgroup.le_normalizer hgL)) (hH.h1.borel_le hb)
    · have h := conj_mem_pCoreOf (inv_mem hgL) (hg x hx)
      have e : g⁻¹ * b * x * (g⁻¹ * b)⁻¹ * x⁻¹ =
          g⁻¹ * (b * x * b⁻¹ * (g * x * g⁻¹)⁻¹) * g⁻¹⁻¹ := by group
      rw [e]
      exact h
  have e : b = g * (g⁻¹ * b) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hgB) (Subgroup.mem_sup_right hX)

private theorem U4qLocalData.pCoreOf_le_inf_trivOTwoQuot (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    pCoreOf 2 L1 ≤ bigB L1 L2 S ⊓ trivOTwoQuot L1 :=
  le_inf ((hH.pCoreOf_le_left.trans (hD.le_borelOf_left hH hS)).trans
    (le_sup_left.trans le_sup_left)) (pCoreOf_le_trivOTwoQuot L1)

private theorem U4qLocalData.borelOf_sup_trivOTwoQuot (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    borelOf L1 S ⊔ (bigB L1 L2 S ⊓ trivOTwoQuot L1) = bigB L1 L2 S := by
  refine le_antisymm (sup_le (le_sup_left.trans le_sup_left) inf_le_left) ?_
  calc bigB L1 L2 S = borelOf L1 S ⊔ borelOf L2 S := hD.bigB_eq_sup hH hS
    _ ≤ _ := sup_le le_sup_left (hD.borelOf_right_le_sup_trivOTwoQuot hH hS)

private theorem U4qLocalData.inf_trivOTwoQuot_inf_borelOf (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    bigB L1 L2 S ⊓ trivOTwoQuot L1 ⊓ borelOf L1 S = pCoreOf 2 L1 := by
  classical
  obtain ⟨F, hFfield, hFfin, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  letI := hFfield
  letI := hFfin
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  refine le_antisymm ?_ (le_inf (hD.pCoreOf_le_inf_trivOTwoQuot hH hS)
    (hH.pCoreOf_le_left.trans (hD.le_borelOf_left hH hS)))
  rintro x ⟨⟨-, hxT⟩, hxB⟩
  exact mem_pCoreOf_of_mem_trivOTwoQuot c₁.α c₁.surjective_α c₁.eq_one_iff hxT
    (borelOf_le L1 S hxB)

private theorem U4qLocalData.card_inf_trivOTwoQuot (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    Nat.card ↥(bigB L1 L2 S ⊓ trivOTwoQuot L1) = 2 ^ (5 * f) * (4 ^ f - 1) := by
  have hf := hD.one_le
  have hXN : bigB L1 L2 S ⊓ trivOTwoQuot L1 ≤ Subgroup.normalizer (borelOf L1 S : Set G) := by
    refine inf_le_left.trans ?_
    rw [hD.bigB_eq_sup hH hS]
    exact sup_le Subgroup.le_normalizer (hD.borelOf_right_le_normalizer_left hH hS)
  have h := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hXN
  rw [sup_comm, hD.borelOf_sup_trivOTwoQuot hH hS, hD.inf_trivOTwoQuot_inf_borelOf hH hS,
    hD.card_bigB hH hS, hD.card_left, hD.card_borelOf_left hH hS] at h
  have hpos : 0 < 2 ^ (6 * f) * (2 ^ f - 1) :=
    Nat.mul_pos (by positivity) (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega)))
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← h]
  ring

theorem U4qLocalData.exists_torus_complement (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    ∃ H₀ : Subgroup G, H₀ ≤ bigB L1 L2 S ∧ (∀ a ∈ H₀, ∀ b ∈ H₀, a * b = b * a) ∧
      Nat.card H₀ = 4 ^ f - 1 ∧
      (∀ h ∈ H₀, ∀ x ∈ L1, h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L1) ∧
      H₀ ⊓ L1 = ⊥ ∧ L1 ⊔ bigB L1 L2 S = L1 ⊔ H₀ ∧
      (∀ b ∈ bigB L1 L2 S, (∀ x ∈ L1, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 L1) →
        b ∈ pCoreOf 2 L1 ⊔ H₀) ∧
      H₀ ≤ Subgroup.normalizer (L1 : Set G) ⊓ Subgroup.normalizer (L2 : Set G) ⊓
        Subgroup.normalizer (S : Set G) ∧
      Nat.Coprime (Nat.card H₀) 2 ∧
      (∀ h ∈ H₀, ∀ c ∈ pCoreOf 2 L2, h * c * h⁻¹ * c⁻¹ ∈ pCoreOf 2 L1) := by
  have hf := hD.one_le
  have hSL1 : S ≤ L1 := hD.le_left hH hS
  have hodd : Odd (4 ^ f - 1) := by
    rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact odd_two_pow_sub_one_of_ne_zero (by omega)
  have hQX := hD.pCoreOf_le_inf_trivOTwoQuot hH hS
  have hXN : bigB L1 L2 S ⊓ trivOTwoQuot L1 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    inf_le_left.trans ((hD.bigB_le_normalizer hH hS).trans
      (inf_le_left.trans (inf_le_left.trans (normalizer_le_normalizer_pCoreOf 2 L1))))
  obtain ⟨F, hFfield, hFfin, ⟨c₁⟩⟩ := hD.exists_coordLeft hH hS
  letI := hFfield
  letI := hFfin
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c₁.card])
  have hXL : ∀ x ∈ bigB L1 L2 S ⊓ trivOTwoQuot L1, x ∈ L1 → x ∈ pCoreOf 2 L1 :=
    fun x hx hxL =>
      mem_pCoreOf_of_mem_trivOTwoQuot c₁.α c₁.surjective_α c₁.eq_one_iff hx.2 hxL
  obtain ⟨H₀, hH₀X, hsup, hcard⟩ := exists_sup_eq_of_coprime hQX hXN (4 ^ f - 1)
    (by rw [hD.card_inf_trivOTwoQuot hH hS, hD.card_left])
    (by rw [hD.card_left]; exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd))
  have hinf : H₀ ⊓ pCoreOf 2 L1 = ⊥ := Subgroup.inf_eq_bot_of_coprime
    (by rw [hcard, hD.card_left]; exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
  have hH₀B : H₀ ≤ bigB L1 L2 S := hH₀X.trans inf_le_left
  have hH₀T : ∀ h ∈ H₀, ∀ x ∈ L1, h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L1 :=
    fun h hh => (mem_trivOTwoQuot.mp (hH₀X hh).2).2
  refine ⟨H₀, hH₀B, fun a ha b hb => ?_, hcard, hH₀T, ?_, ?_, fun b hb hbT => ?_,
    hH₀B.trans (hD.bigB_le_normalizer hH hS), (by rw [hcard]; exact Nat.coprime_two_right.mpr hodd),
    fun h hh c hc => hH₀T h hh c (hSL1 (hH.pCoreOf_le_right hc))⟩
  ·
    have hX' : a * b * a⁻¹ * b⁻¹ ∈ bigB L1 L2 S ⊓ trivOTwoQuot L1 :=
      mul_mem (mul_mem (mul_mem (hH₀X ha) (hH₀X hb)) (inv_mem (hH₀X ha))) (inv_mem (hH₀X hb))
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ H₀ ⊓ pCoreOf 2 L1 := Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb),
        hXL _ hX' (hSL1 (hD.commutator_mem_of_mem_bigB hH hS a (hH₀B ha) b (hH₀B hb)))⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  ·
    rw [eq_bot_iff]
    rintro h ⟨hh, hhL⟩
    have h1 : h ∈ H₀ ⊓ pCoreOf 2 L1 := Subgroup.mem_inf.mpr ⟨hh, hXL h (hH₀X hh) hhL⟩
    rwa [hinf] at h1
  ·
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left (hH₀B.trans le_sup_right))
    calc bigB L1 L2 S = borelOf L1 S ⊔ (bigB L1 L2 S ⊓ trivOTwoQuot L1) :=
          (hD.borelOf_sup_trivOTwoQuot hH hS).symm
      _ ≤ L1 ⊔ H₀ := by
          refine sup_le ((borelOf_le L1 S).trans le_sup_left) ?_
          rw [← hsup]
          exact sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 L1).trans le_sup_left) le_sup_right
  ·
    rw [hsup]
    exact Subgroup.mem_inf.mpr
      ⟨hb, mem_trivOTwoQuot.mpr ⟨((hD.bigB_le_normalizer hH hS) hb).1.1, hbT⟩⟩

theorem U4qLocalData.exists_torus (_hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : U4qLocalData L1 L2 S f) (hS : Nat.card S = 2 ^ (6 * f)) :
    ∃ H₀ : Subgroup G, H₀ ≤ bigB L1 L2 S ∧ (∀ a ∈ H₀, ∀ b ∈ H₀, a * b = b * a) ∧
      Nat.card H₀ = 4 ^ f - 1 ∧
      (∀ h ∈ H₀, ∀ x ∈ L1, h * x * h⁻¹ * x⁻¹ ∈ pCoreOf 2 L1) ∧
      H₀ ⊓ L1 = ⊥ ∧ L1 ⊔ bigB L1 L2 S = L1 ⊔ H₀ := by
  obtain ⟨H₀, h1, h2, h3, h4, h5, h6, -⟩ := hD.exists_torus_complement hH hS
  exact ⟨H₀, h1, h2, h3, h4, h5, h6⟩

end Amalgam

end CFSG.Quasithin.F112R.St84

end
