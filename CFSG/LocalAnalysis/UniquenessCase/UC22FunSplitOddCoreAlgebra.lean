module

public import CFSG.Milestones.ASVolI.A3L3.StepsBase
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreFrame
public import CFSG.Quasithin.EmptyFaithful.S152N2Grp
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem odd_card_classicalInvolutionOddCore_map (H : Subgroup X) :
    Odd (Nat.card ↥((classicalInvolutionOddCore ↥H).map H.subtype)) := by
  have hcard : Nat.card ↥((classicalInvolutionOddCore ↥H).map H.subtype) =
      Nat.card ↥(classicalInvolutionOddCore ↥H) :=
    Subgroup.card_map_of_injective (K := classicalInvolutionOddCore ↥H)
      (f := H.subtype) H.subtype_injective
  rw [hcard]
  change Odd (Nat.card ↥(CFSG.oddCore ↥H))
  exact CFSG.Quasithin.A38.odd_card_oddCore ↥H

omit [Finite X] in
theorem normalizer_classicalInvolutionOddCore_map (H : Subgroup X) :
    H ≤ Subgroup.normalizer
      (((classicalInvolutionOddCore ↥H).map H.subtype : Subgroup X) : Set X) :=
  CFSG.ASVolI.burnsideA315y_le_normalizer_map (H := H)
    (R := classicalInvolutionOddCore ↥H)

theorem oddCore_map_le_of_permuting {B P H : Subgroup X}
    (hBo : Odd (Nat.card ↥B)) (hP : IsPGroup 2 P) (hH : H = B ⊔ P)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X)) :
    (classicalInvolutionOddCore ↥H).map H.subtype ≤ B := by
  let O : Subgroup X := (classicalInvolutionOddCore ↥H).map H.subtype
  have hOH : O ≤ H := Subgroup.map_subtype_le _
  have hOodd : Odd (Nat.card ↥O) := odd_card_classicalInvolutionOddCore_map H
  have hHnorm : H ≤ Subgroup.normalizer (O : Set X) :=
    normalizer_classicalInvolutionOddCore_map H
  have hBH : B ≤ H := hH.symm ▸ le_sup_left
  have hBN : B ≤ Subgroup.normalizer (O : Set X) := hBH.trans hHnorm
  have hNH : O ≤ B ⊔ P := hH ▸ hOH
  exact CFSG.ASVolI.burnsideA315y_le_of_odd hBo hP hperm hNH hBN hOodd

theorem isSolvable_of_eq_sup {B P H : Subgroup X}
    (hBab : IsMulCommutative ↥B) (hBo : Odd (Nat.card ↥B)) (hP : IsPGroup 2 P)
    (hH : H = B ⊔ P)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X)) :
    Group.IsSolvable ↥H := by
  rw [hH]
  exact CFSG.ASVolI.burnsideA315y_sup_solvable hBab hBo hP hperm

theorem not_three_dvd_card_of_eq_sup {B P H : Subgroup X}
    (hBo : Odd (Nat.card ↥B)) (hP : IsPGroup 2 P) (hH : H = B ⊔ P)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    (hB3 : ¬ 3 ∣ Nat.card ↥B) : ¬ 3 ∣ Nat.card ↥H := by
  have hcard : Nat.card ↥(B ⊔ P) = Nat.card ↥B * Nat.card ↥P :=
    CFSG.ASVolI.burnsideA315x_card_sup hperm
      (CFSG.ASVolI.burnsideA315y_inf_eq_bot_of_odd hBo hP)
  rw [hH, hcard]
  intro h3
  rcases Nat.prime_three.dvd_mul.mp h3 with h3B | h3P
  · exact hB3 h3B
  · obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hk] at h3P
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3P) (by norm_num)

theorem oddCore_commutator_involution {B P H : Subgroup X}
    (hBab : IsMulCommutative ↥B) (hBo : Odd (Nat.card ↥B)) (hP : IsPGroup 2 P)
    (hH : H = B ⊔ P)
    (hperm : (B : Set X) * (P : Set X) = (P : Set X) * (B : Set X))
    {z : X} (hzH : z ∈ H) (hz2 : z * z = 1) :
    let O : Subgroup X := (classicalInvolutionOddCore ↥H).map H.subtype
    let E : Subgroup X := ⁅O, Subgroup.zpowers z⁆
    E ≤ O ∧ (∀ e ∈ E, z * e * z⁻¹ = e⁻¹) ∧ E = ⁅E, Subgroup.zpowers z⁆ := by
  let O : Subgroup X := (classicalInvolutionOddCore ↥H).map H.subtype
  let E : Subgroup X := ⁅O, Subgroup.zpowers z⁆
  have hOleB : O ≤ B := oddCore_map_le_of_permuting hBo hP hH hperm
  have hOodd : Odd (Nat.card ↥O) := odd_card_classicalInvolutionOddCore_map H
  have hzN : z ∈ Subgroup.normalizer (O : Set X) :=
    normalizer_classicalInvolutionOddCore_map H hzH
  have hE_le_O : E ≤ O := by
    exact (Subgroup.le_normalizer_iff_commutator_le_left
      (H := Subgroup.zpowers z) (K := O)).mp (Subgroup.zpowers_le.mpr hzN)
  have hOcomm : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a := by
    intro a ha b hb
    have h := (IsMulCommutative.is_comm (M := ↥B)).comm
      ⟨a, hOleB ha⟩ ⟨b, hOleB hb⟩
    simpa using congrArg (fun x : ↥B => (x : X)) h
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    fun a ha b hb => hOcomm a (hE_le_O ha) b (hE_le_O hb)
  have hinvE : ∀ e ∈ E, z * e * z⁻¹ = e⁻¹ :=
    CFSG.LocalAnalysis.WeakClosure81.conj_eq_inv_of_mem_commutator_zpowers
      (Xb := O) (a := z) hz2 hEcomm
  have hzE : z ∈ Subgroup.normalizer (E : Set X) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := O) (H₂ := Subgroup.zpowers z)
      (Subgroup.mem_zpowers z)
  have hEodd : Odd (Nat.card ↥E) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hE_le_O)
  have hEeq : E = ⁅E, Subgroup.zpowers z⁆ :=
    CFSG.Quasithin.S152N2.comm_eq_of_inverts hEodd hzE hinvE
  exact ⟨hE_le_O, hinvE, hEeq⟩

omit [Finite X] in
theorem mem_normalizer_oddCore_commutator_of_mem_of_centralizes {H : Subgroup X}
    {z g : X} (hgH : g ∈ H) (hgz : g * z = z * g) :
    g ∈ Subgroup.normalizer
      (⁅(classicalInvolutionOddCore ↥H).map H.subtype, Subgroup.zpowers z⁆ : Subgroup X) := by
  have hgO : g ∈ Subgroup.normalizer
      (((classicalInvolutionOddCore ↥H).map H.subtype : Subgroup X) : Set X) :=
    normalizer_classicalInvolutionOddCore_map H hgH
  have hgzN : g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set X) := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.normalizer_le_normalizer_closure ({z} : Set X)
      (Subgroup.centralizer_le_normalizer ({z} : Set X)
        (Subgroup.mem_centralizer_singleton_iff.mpr hgz))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgO hgzN ⊢
  rw [Subgroup.map_commutator, hgO, hgzN]

end CFSG.LocalAnalysis.UniquenessCase.UC22

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open scoped commutatorElement

theorem le_centralizingLayer_of_commutator_eq {G : Type} [Group G]
    {Λ : Set (Subgroup G)} (hΛ : ConjInvariant Λ) {A : Set G}
    {E : Subgroup G} {z : G} (hE : E ≤ Subgroup.centralizer A)
    (hz : z ∈ centralizingLayer Λ A)
    (hEq : E = ⁅E, Subgroup.zpowers z⁆) :
    E ≤ centralizingLayer Λ A := by
  let Y : Subgroup G := centralizingLayer Λ A
  have hzY : z ∈ Y := hz
  have hEN : E ≤ Subgroup.normalizer (Y : Set G) := by
    intro e he
    exact mem_normalizer_centralizingLayer hΛ (hE he)
  have hcomm : ⁅E, Subgroup.zpowers z⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro e he t ht
    have htY : t ∈ Y := (Subgroup.zpowers_le.mpr hzY) ht
    have het : e * t * e⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hEN he) t).mp htY
    have hcommut : ⁅e, t⁆ = (e * t * e⁻¹) * t⁻¹ := by
      rw [commutatorElement_def]
    rw [hcommut]
    exact Y.mul_mem het (Y.inv_mem htY)
  rw [hEq]
  exact hcomm

end CFSG.ClassicalInvolution.Generic.DeltaClosure

end
