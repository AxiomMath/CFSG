module

import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RowsProof

open CFSG CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

theorem commutatorElement_mul_central_left {X : Type*} [Group X] {z x y : X}
    (hz : z ∈ Subgroup.center X) : ⁅z * x, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have h := Subgroup.mem_center_iff.mp hz (x * y * x⁻¹)
  calc z * x * y * (x⁻¹ * z⁻¹) * y⁻¹ = z * (x * y * x⁻¹) * z⁻¹ * y⁻¹ := by group
    _ = (x * y * x⁻¹) * z * z⁻¹ * y⁻¹ := by rw [← h]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem commutatorElement_mul_central_right {X : Type*} [Group X] {z x y : X}
    (hz : z ∈ Subgroup.center X) : ⁅x, z * y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have h1 := Subgroup.mem_center_iff.mp hz x
  have h2 := Subgroup.mem_center_iff.mp hz (x * y * x⁻¹ * y⁻¹)
  calc x * (z * y) * x⁻¹ * (y⁻¹ * z⁻¹) = (x * z) * y * x⁻¹ * y⁻¹ * z⁻¹ := by group
    _ = z * x * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [h1]
    _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * z * z⁻¹ := by rw [← h2]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem center_eq_bot_of_coprime_quotient {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X))
    (hcop : ¬ 3 ∣ Nat.card (X ⧸ Subgroup.center X)) : Subgroup.center X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect X := hq.1
  obtain ⟨k, hk⟩ := hZ3.exists_card_eq
  have hco : Nat.Coprime (Nat.card (Subgroup.center X)) (Subgroup.center X).index := by
    rw [hk, Subgroup.index]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hcop)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hco
  have hsup := hH.sup_eq_top
  have hzh : ∀ x : X, ∃ z ∈ Subgroup.center X, ∃ h ∈ H, z * h = x := by
    intro x
    have hx : x ∈ Subgroup.center X ⊔ H := hsup ▸ Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hx
    obtain ⟨z, hz, h, hh, rfl⟩ := hx
    exact ⟨z, hz, h, hh, rfl⟩
  have hcomm : commutator X ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨z₁, hz₁, h₁, hh₁, rfl⟩ := hzh x
    obtain ⟨z₂, hz₂, h₂, hh₂, rfl⟩ := hzh y
    rw [commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂,
      commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  have hHtop : H = ⊤ := by
    rw [eq_top_iff, ← hperf.commutator_eq_top]
    exact hcomm
  have hdis := hH.disjoint
  rw [hHtop, disjoint_top] at hdis
  exact hdis

theorem card_le_three_of_suzuki {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {E : Subgroup (MulAut (suzukiGroup a K))} (hE : ∀ α ∈ E, α ^ 3 = 1) : Nat.card E ≤ 3 := by
  have h3 := CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK
  obtain ⟨-, -, -, -, hcyc, -, -⟩ :=
    CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha K hK
  set q : MulAut (suzukiGroup a K) →* Outer (suzukiGroup a K) :=
    QuotientGroup.mk' (inner (suzukiGroup a K)) with hq
  have : Finite (MulAut (suzukiGroup a K)) := MulEquiv.finite_left
  have hdisj : ∀ α ∈ E, α ∈ inner (suzukiGroup a K) → α = 1 := by
    intro α hαE hαI
    have hdvd : orderOf (⟨α, hαI⟩ : inner (suzukiGroup a K)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE α hαE))
    have hdvd' : Nat.card (inner (suzukiGroup a K)) ∣ Nat.card (suzukiGroup a K) :=
      Subgroup.card_range_dvd _
    have hord : orderOf (⟨α, hαI⟩ : inner (suzukiGroup a K)) ∣
        Nat.card (inner (suzukiGroup a K)) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime 3 (Nat.card (suzukiGroup a K)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have h1 : orderOf (⟨α, hαI⟩ : inner (suzukiGroup a K)) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hdvd (hord.trans hdvd')
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  have hinj : Function.Injective (q.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [MonoidHom.comp_apply, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact Subtype.ext (hdisj x x.2 hx)
  have : IsCyclic E := isCyclic_of_injective _ hinj
  have hexp : Monoid.exponent E ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hE x x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem false_of_suzuki {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hZ3 : IsPGroup 3 (Subgroup.center X)) {m : ℕ}
    {hm : (TauCeti.LieTypeIndex.suzuki m).Valid}
    (hL : Nonempty (X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hm⟩).Group))
    {E : Subgroup (MulAut X)} (hE : CFSG.Assembly.IsElemAbelian 3 E) (h9 : 9 ≤ Nat.card E) :
    False := by
  obtain ⟨θ₀⟩ := hL
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ₁⟩⟩ := Census.suzukiModel_of_index m hm
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  set θ : X ⧸ Subgroup.center X ≃* suzukiGroup a K := θ₀.trans θ₁ with hθ
  have h3 := CFSG.RankThree.PartTwo.KFacts.not_three_dvd_card_suzukiGroup hK
  have hZ : Subgroup.center X = ⊥ := center_eq_bot_of_coprime_quotient hq hZ3 (by
    rw [Nat.card_congr θ.toEquiv]
    exact h3)
  set ι : X ≃* suzukiGroup a K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ
  have hle := card_le_three_of_suzuki ha hK (E := E.map (MulAut.congr ι).toMonoidHom) (by
    rintro _ ⟨α, hα, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hE.2 α hα, map_one])
  rw [Subgroup.card_map_of_injective (MulAut.congr ι).injective] at hle
  omega

end CFSG.RankThree.PartTwo.Sec4.Item434RowsProof
