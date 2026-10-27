module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplitCase
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem twoPart_eq_of_card {X : Subgroup G} {a u : ℕ} (hu : Odd u)
    (hcard : Nat.card ↥X = 2 ^ a * u) : twoPart X = 2 ^ a := by
  have hnot : ¬ 2 ∣ u := fun hdvd => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr hdvd)
  unfold twoPart
  rw [hcard, Nat.factorization_mul (by positivity) hu.pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnot, add_zero, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two]
  simp

private theorem card_eq_card_oTwoQuot_mul_card (L : Subgroup G) :
    Nat.card ↥L = Nat.card (oTwoQuot ↥L) * Nat.card (pCoreOf 2 L) := by
  have hpc : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) := by
    rw [CFSG.Open.pCoreOf, Subgroup.card_map_of_injective L.subtype_injective]
  rw [hpc]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)

private theorem twoPart_eq_of_isL2Quot {L : Subgroup G} (hf : 1 ≤ f)
    (h : IsL2Quot f (oTwoQuot ↥L)) (hc : Nat.card (pCoreOf 2 L) = 2 ^ (5 * f)) :
    twoPart L = 2 ^ (6 * f) := by
  refine twoPart_eq_of_card (u := 4 ^ f - 1) ?_ ?_
  · rw [show (4 : ℕ) ^ f = 2 ^ (2 * f) by rw [pow_mul]; norm_num]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  · rw [card_eq_card_oTwoQuot_mul_card, IsL2Quot.card hf h, hc,
      show 6 * f = f + 5 * f by ring, pow_add]
    ring

private theorem mem_centerOf_iff' {Q : Subgroup G} {z : G} :
    z ∈ centerOf Q ↔ z ∈ Q ∧ ∀ a ∈ Q, a * z = z * a := by
  rw [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

private theorem commutator_mem_centerOf (hD : G2qLocalData L1 L2 S f) {a b : G}
    (ha : a ∈ pCoreOf 2 L2) (hb : b ∈ pCoreOf 2 L2) : ⁅a, b⁆ ∈ centerOf (pCoreOf 2 L2) := by
  obtain ⟨-, hab | ⟨hcomm, -, -⟩⟩ := hD.special_right
  · have h : (⟨a, ha⟩ : ↥(pCoreOf 2 L2)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      hab.1.is_comm.comm _ _
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (congrArg Subtype.val h)]
    exact one_mem _
  · have hc : ⁅(⟨a, ha⟩ : ↥(pCoreOf 2 L2)), ⟨b, hb⟩⁆ ∈ Subgroup.center ↥(pCoreOf 2 L2) := by
      rw [← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    refine mem_centerOf_iff'.mpr ⟨?_, fun x hx => ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩)

private theorem exists_splitData (hD : G2qLocalData L1 L2 S f) (c : G2qCoordRight L2 S f) :
    letI := c.field
    ∃ nv zv : G → Fin 2 → c.F,
      G2qSplitData L2 (pCoreOf 2 L2) (centerOf (pCoreOf 2 L2)) c.W c.α nv zv := by
  letI := c.field
  have hQn : ∀ ℓ ∈ L2, ∀ x ∈ pCoreOf 2 L2, ℓ * x * ℓ⁻¹ ∈ pCoreOf 2 L2 := fun ℓ hℓ x hx =>
    CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hℓ hx
  have hZn : ∀ ℓ ∈ L2, ∀ x ∈ centerOf (pCoreOf 2 L2),
      ℓ * x * ℓ⁻¹ ∈ centerOf (pCoreOf 2 L2) := by
    intro ℓ hℓ x hx
    obtain ⟨hxQ, hxc⟩ := mem_centerOf_iff'.mp hx
    refine mem_centerOf_iff'.mpr ⟨hQn ℓ hℓ x hxQ, fun a ha => ?_⟩
    have ha' : ℓ⁻¹ * a * ℓ ∈ pCoreOf 2 L2 := by simpa using hQn ℓ⁻¹ (inv_mem hℓ) a ha
    calc a * (ℓ * x * ℓ⁻¹) = ℓ * ((ℓ⁻¹ * a * ℓ) * x) * ℓ⁻¹ := by group
      _ = ℓ * (x * (ℓ⁻¹ * a * ℓ)) * ℓ⁻¹ := by rw [hxc _ ha']
      _ = ℓ * x * ℓ⁻¹ * a := by group
  obtain ⟨nv, hnv⟩ := c.natW.exists_isNatSecCoord hQn
  obtain ⟨zv, hzv⟩ := c.nat.exists_isNatSecCoord hZn
  exact ⟨nv, zv, c.surj, CFSG.LieType.BorelTits.pCoreOf_le 2 L2, c.center_le, c.le_pCoreOf,
    fun z hz a ha => (mem_centerOf_iff'.mp hz).2 a ha,
    fun a ha h => mem_centerOf_iff'.mpr ⟨ha, h⟩, fun a ha b hb => commutator_mem_centerOf hD ha hb,
    fun w hw ℓ hℓ => c.commutator_le (Subgroup.commutator_mem_commutator hw hℓ), hnv, hzv⟩

theorem G2qCoordRight.commute_of_commutator_inf_W_eq (hD : G2qLocalData L1 L2 S f)
    (c : G2qCoordRight L2 S f)
    (hsplit : ⁅pCoreOf 2 L2, L2⁆ ⊓ c.W = centerOf (pCoreOf 2 L2)) :
    ∀ a ∈ ⁅pCoreOf 2 L2, L2⁆, ∀ b ∈ ⁅pCoreOf 2 L2, L2⁆, a * b = b * a := by
  letI := c.field
  letI := c.fintype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP c.F 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, c.card])
  obtain ⟨nv, zv, hd⟩ := exists_splitData hD c
  exact hd.commute_of_commutator_inf_eq hsplit

variable [Finite G]

private theorem mem_pCoreOf_of_centralizes (hH : Hyp111 L1 L2 S) (hS1 : S ≤ L1) (hS2 : S ≤ L2)
    {k : G} (hkB : k ∈ bigB L1 L2 S) (hk : ∀ a ∈ pCoreOf 2 L2, k * a * k⁻¹ = a) :
    k ∈ pCoreOf 2 L2 := by
  have hP : L2 ⊔ S ⊔ borelOf L1 S = L2 ⊔ bigB L1 L2 S := by
    rw [sup_eq_left.mpr hS2, sup_bigB_right_of_le hS2]
  have hcore : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 :=
    pCoreOf_sup_bigB_right_of_le hH hS1 hS2
  have hkP : k ∈ L2 ⊔ S ⊔ borelOf L1 S := by
    rw [hP]
    exact Subgroup.mem_sup_right hkB
  have hkC : k ∈ Subgroup.centralizer (pCoreOf 2 (L2 ⊔ S ⊔ borelOf L1 S) : Set G) := by
    rw [hP, hcore, Subgroup.mem_centralizer_iff]
    intro a ha
    calc a * k = k * a * k⁻¹ * k := by rw [hk a ha]
      _ = k * a := by group
  have h := hH.h2.charTwo (Subgroup.mem_inf.mpr ⟨hkP, hkC⟩)
  rwa [hP, hcore] at h

theorem G2qCoordRight.commutator_inf_W_eq_or (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) :
    ⁅pCoreOf 2 L2, L2⁆ ⊓ c.W = centerOf (pCoreOf 2 L2) ∨ c.W ≤ ⁅pCoreOf 2 L2, L2⁆ := by
  classical
  letI := c.field
  letI := c.fintype
  obtain ⟨nv, zv, hd⟩ := exists_splitData hD c
  obtain ⟨H₀, hH₀B, -, hcard, htriv, hinf, -⟩ := hD.exists_torus_right hf hH h1 h2
  have hS1 : S ≤ L1 :=
    hH.le_left_of_twoPart (by rw [twoPart_eq_of_isL2Quot (by omega) h1 hD.card_left, hD.card_S])
  have hS2 : S ≤ L2 :=
    hH.le_right_of_twoPart (by rw [twoPart_eq_of_isL2Quot (by omega) h2 hD.card_right, hD.card_S])
  have hNB := hD.bigB_le_normalizer hH h1 h2
  have hL : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (L2 : Set G) := fun k hk =>
    (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hNB (hH₀B hk))).1).2
  have hQ : ∀ k ∈ H₀, k ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) := fun k hk =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L2 (hL k hk)
  have hodd : Odd (Nat.card H₀) := by
    rw [hcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  refine hd.commutator_inf_eq_or (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 L2)
    (by rw [hcard, c.card]) hodd hL hQ htriv fun k hk hkQ => ?_
  have hk2 := mem_pCoreOf_of_centralizes hH hS1 hS2 (hH₀B hk) hkQ
  have hk' : k ∈ H₀ ⊓ L2 :=
    Subgroup.mem_inf.mpr ⟨hk, CFSG.LieType.BorelTits.pCoreOf_le 2 L2 hk2⟩
  rwa [hinf, Subgroup.mem_bot] at hk'

end CFSG.Quasithin.F112R.St84

end
