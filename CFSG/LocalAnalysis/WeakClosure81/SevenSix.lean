module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem omegaSet_conjSubgroup (V H E : Subgroup G) (g : G) :
    omegaSet (conjSubgroup V g) H E = omegaSet V H E := by
  ext U
  simp only [mem_omegaSet]
  constructor
  · rintro ⟨h, rfl, hEU, hUO⟩
    exact ⟨g * h, by rw [CFSG.Quasithin.conjSubgroup_conjSubgroup], hEU, hUO⟩
  · rintro ⟨h, rfl, hEU, hUO⟩
    refine ⟨g⁻¹ * h, ?_, hEU, hUO⟩
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, show g * (g⁻¹ * h) = h by group]

theorem kSub_conjSubgroup (V H E : Subgroup G) (g : G) :
    kSub (conjSubgroup V g) H E = kSub V H E := by
  simp only [kSub, omegaSet_conjSubgroup]

theorem iSub_conjSubgroup (V H E : Subgroup G) (g : G) :
    iSub (conjSubgroup V g) H E = iSub V H E := by
  simp only [iSub, omegaSet_conjSubgroup]

theorem omegaSet_eq_of_mem {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    omegaSet U H E = omegaSet V H E := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  exact omegaSet_conjSubgroup V H E g

theorem kSub_eq_of_mem {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    kSub U H E = kSub V H E := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  exact kSub_conjSubgroup V H E g

theorem iSub_eq_of_mem {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    iSub U H E = iSub V H E := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  exact iSub_conjSubgroup V H E g

theorem isTI_of_mem_omegaSet {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) (hTI : IsTI V) :
    IsTI U := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  exact isTI_conj hTI g

theorem seven_six_one_relIndex_eq_two {V H E J A X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E) (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    (hJX : J ≤ X) (hXH : X ≤ H)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hXodd : Odd (J.relIndex X))
    (hfaith : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J) :
    ∀ U ∈ omegaSet V H E, U ≤ A → J.relIndex U = 2 ∧ (U ⊓ iSub V H E).relIndex U = 2 := by
  intro U hU hUleA
  obtain ⟨_, -, -, hUnotO⟩ := mem_omegaSet.mp hU
  have hUnotJ : ¬ U ≤ J := fun hUJ => hUnotO (hUJ.trans hJ)
  have hne1 : J.relIndex U ≠ 1 := fun h => hUnotJ (Subgroup.relIndex_eq_one.mp h)
  have hne0 : J.relIndex U ≠ 0 := by
    haveI : Finite (↥U ⧸ (J.subgroupOf U)) := inferInstance
    exact Subgroup.index_ne_zero_of_finite
  have hnotbig : ¬ 2 < J.relIndex U := by
    intro hbig
    have hcomm : ⁅U, X⁆ ≤ J :=
      seven_three_five (V := U) (H := H) (E := E) (J := J) (R := X)
        (isElemAbelian_of_mem_omegaSet hV hU) (isTI_of_mem_omegaSet hU hTI) hE hEH hEnorm
        (by rw [omegaSet_eq_of_mem hU]; exact hU)
        (by rw [omegaSet_eq_of_mem hU]; exact hOmH)
        hJ hJnorm (by rw [iSub_eq_of_mem hU]; exact hIJ)
        hbig hJX hXH (hUleA.trans hAX) hXodd
    exact hUnotJ fun u hu => hfaith u (hUleA hu) fun x hx =>
      hcomm (Subgroup.commutator_mem_commutator hu hx)
  have hEq : J.relIndex U = 2 := by
    have hle : J.relIndex U ≤ 2 := le_of_not_gt hnotbig
    omega
  refine ⟨hEq, ?_⟩
  rw [inf_iSub_eq_inf_J hU hIJ hJ, Subgroup.inf_relIndex_left, hEq]

end CFSG.LocalAnalysis.WeakClosure81
