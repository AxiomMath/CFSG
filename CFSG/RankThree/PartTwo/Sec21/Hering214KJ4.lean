module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KSyl27
public import CFSG.RankThree.PartTwo.Sec21.Hering214KGen
public import CFSG.RankThree.PartOne.S11c.OuterInner
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint CFSG.Sporadic.J4Schreier
open CFSG.LocalAnalysis.ComponentInitial (pointwiseFixingAut)
open CFSG.Assembly (IsElemAbelian)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

section J4

theorem eInvNine_J4mat
    (hOut : ¬ 3 ∣ Nat.card (Outer ↥J)) : EInvNine ↥J := by
  have hF : J4Facts := j4Facts
  have hM : MatFacts := hF.mat
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  haveI : Finite ↥Hj := Nat.finite_of_card_ne_zero (by rw [card_Hj hF]; norm_num)
  have hZ : Subgroup.center ↥J = ⊥ :=
    center_eq_bot_of_simple_of_not_prime (isSimpleGroup_J hF) (by rw [card_J hF]; norm_num)
  have hout : ∀ α : MulAut ↥J, α ^ 3 = 1 → ∃ y : ↥J, α = MulAut.conj y := fun α hα => by
    obtain ⟨b, hb⟩ := CFSG.RankThree.PartOne.exists_inner_of_pow_eq_one_of_not_dvd_card_outer
      Nat.prime_three hOut α hα
    exact ⟨b, hb.symm⟩
  have hJ3 : (Nat.card ↥J).factorization 3 = 3 := by
    rw [card_J hF, Nat.factorization_def _ Nat.prime_three]
    decide +kernel
  have hHj3 : (Nat.card ↥Hj).factorization 3 = 3 := by
    rw [card_Hj hF, Nat.factorization_def _ Nat.prime_three]
    decide +kernel
  obtain ⟨P'⟩ : Nonempty (Sylow 3 ↥Hj) := inferInstance
  set P'' : Subgroup ↥J := (P' : Subgroup ↥Hj).map Hj.subtype with hP''
  have hP''card : Nat.card P'' = 3 ^ (Nat.card ↥J).factorization 3 := by
    rw [hP'', Subgroup.card_map_of_injective Hj.subtype_injective, P'.card_eq_multiplicity, hHj3,
      hJ3]
  let P₀ : Sylow 3 ↥J := Sylow.ofCard P'' hP''card
  have hP₀ : (P₀ : Subgroup ↥J) = P'' := Sylow.coe_ofCard P'' hP''card
  have hP₀Hj : (P₀ : Subgroup ↥J) ≤ Hj := by
    rw [hP₀]
    exact Subgroup.map_subtype_le _
  have hElem := elem_uJ hM
  have hRab : IsElemAbelian 2 (Eg uJ 11) := by
    refine isElemAbelian_closure_of_comm_sq (S := {g | ∃ j < 11, g = uJ j}) ?_ ?_
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      exact hElem.comm i hi j hj
    · rintro _ ⟨j, hj, rfl⟩
      exact hElem.sq j hj
  have hnorm : ∀ g ∈ Hj, ∀ x ∈ Eg uJ 11, g * x * g⁻¹ ∈ Eg uJ 11 :=
    eg_normalizes hElem Hj XJ act letters (fun ℓ hℓ c => hX_all hM hℓ c)
      (fun ℓ hℓ => XJ_inv hℓ) Hj_le_closure
  refine eInvNine_of_sylow_stable hZ hout P₀ hRab
    (fun p hp r hr => hnorm p (hP₀Hj hp) r hr) ?_
  intro B hBle hBexp hB9
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : B = ⊥ := (Subgroup.eq_bot_iff_forall B).2 hcon
    rw [this, Subgroup.card_bot] at hB9
    omega
  refine ⟨b, hbB, ?_⟩
  by_contra hcon
  push Not at hcon
  have hbE : b ∈ Eg uJ 11 := by
    refine centralizer_Hj hM hF b (hP₀Hj (hBle hbB)) (fun y hy => ?_)
    have := hcon y hy
    calc b * y = b * y * b⁻¹ * b := by group
      _ = y * b := by rw [this]
  have h2 := isPGroup_Eg hElem ⟨b, hbE⟩
  obtain ⟨k, hk⟩ := h2
  have hb3 : (⟨b, hbE⟩ : ↥(Eg uJ 11)) ^ 3 = 1 := Subtype.ext (hBexp b hbB)
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hdvd1 : orderOf (⟨b, hbE⟩ : ↥(Eg uJ 11)) ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  have hdvd2 : orderOf (⟨b, hbE⟩ : ↥(Eg uJ 11)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hone : orderOf (⟨b, hbE⟩ : ↥(Eg uJ 11)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : (⟨b, hbE⟩ : ↥(Eg uJ 11)) = 1 := orderOf_eq_one_iff.1 hone
  exact hb1 (congrArg Subtype.val this)

theorem eInvNine_j4_of_outer
    (hOut : ¬ 3 ∣ Nat.card (Outer NativeSporadic.J4)) : EInvNine NativeSporadic.J4 := by
  have hM : MatFacts := j4Facts.mat
  have e : NativeSporadic.J4 ≃* ↥J := seedEquiv hM
  have hOutJ : ¬ 3 ∣ Nat.card (Outer ↥J) := by
    have h : Nat.card (Outer NativeSporadic.J4) = Nat.card (Outer ↥J) :=
      Nat.card_congr
        (@equivalence NativeSporadic.J4 ↥J Units.instGroup (Subgroup.toGroup J) e).toEquiv
    rwa [h] at hOut
  exact @EInvNine.of_mulEquiv NativeSporadic.J4 ↥J _ _ e (eInvNine_J4mat hOutJ)

theorem not_dvd_three_card_outer_J :
    ¬ 3 ∣ Nat.card (Outer ↥J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (pointwiseFixingAut H) :=
    (CTU_J4_pointwise_local_binary_subgroup_automorphism_kernel_is_two_group).2
  have hCp : ¬ 3 ∣ Nat.card (pointwiseFixingAut H) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP2
    rw [hk]
    intro h
    have h32 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  exact not_dvd_card_outer_of_sylow_bound (by omega : 3 ≠ 2) S0Sylow N H
    (by rw [S0Sylow_coe]; exact N_le_S0) (by rw [S0Sylow_coe]; exact S0_le_H) isPGroup_N
    normalizer_N QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2.le hCp
    (R3E_J4_Sylow_two_automorphism_group_is_two_group S0Sylow).2

theorem eInvNine_j4 :
    EInvNine NativeSporadic.J4 := by
  refine eInvNine_j4_of_outer ?_
  have hM : MatFacts := j4Facts.mat
  have e : NativeSporadic.J4 ≃* ↥J := seedEquiv hM
  have h : Nat.card (Outer NativeSporadic.J4) = Nat.card (Outer ↥J) :=
    Nat.card_congr
      (@equivalence NativeSporadic.J4 ↥J Units.instGroup (Subgroup.toGroup J) e).toEquiv
  rw [h]
  exact not_dvd_three_card_outer_J

end J4

end CFSG.RankThree.PartTwo.Sec21.Hering214
