module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L511.KRadical
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.CentralizerK

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.CentralizerK

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f

variable {Γ : Type*} [Group Γ]

theorem isSubnormal_subgroupOf_trans {D M X : Subgroup Γ} (hDM : D ≤ M) (hMX : M ≤ X)
    (hD : (D.subgroupOf M).IsSubnormal) (hM : (M.subgroupOf X).IsSubnormal) :
    (D.subgroupOf X).IsSubnormal := by
  have hDX : D.subgroupOf X ≤ M.subgroupOf X := fun x hx => hDM hx
  refine Subgroup.IsSubnormal.trans hDX ?_ hM
  let e := Subgroup.subgroupOfEquivOfLe hMX
  have heq : (D.subgroupOf X).subgroupOf (M.subgroupOf X) =
      (D.subgroupOf M).comap e.toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact hD.comap e.toMonoidHom

theorem isComponent_of_mem_lcal {Y J : Subgroup Γ} (hJ : J ∈ lcal Y) :
    CFSG.IsComponent (J.subgroupOf Y) := by
  obtain ⟨hJY, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have hnc' : ∃ a b : J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hnc (isMulCommutative_iff.mpr hcon)
  obtain ⟨hq, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc'
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJY).symm hq,
    hsub⟩

theorem le_or_le_centralizer_of_mem_lcal [Finite Γ] {X F N : Subgroup Γ} (hF : F ∈ lcal X)
    (hNX : N ≤ X) (hN : (N.subgroupOf X).Normal) :
    F ≤ N ∨ F ≤ Subgroup.centralizer (N : Set Γ) := by
  rcases CFSG.LocalCores.component_normal_subgroup (isComponent_of_mem_lcal hF) hN with h | h
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le (lcal_le hF) h)
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf (lcal_le hF) h
    rw [inf_eq_left.mpr hNX] at this
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this

theorem lcal_eq_singleton_of_isSimpleGroup [Finite Γ] {C : Subgroup Γ}
    (hs : IsSimpleGroup ↥(CFSG.inSubgroup CFSG.generalizedFitting C))
    (hnc : ¬ IsMulCommutative ↥(CFSG.inSubgroup CFSG.generalizedFitting C)) :
    lcal C = {CFSG.inSubgroup CFSG.generalizedFitting C} := by
  set N := CFSG.inSubgroup CFSG.generalizedFitting C with hN
  have hNC : N ≤ C := Subgroup.map_subtype_le _
  have hNn : (N.subgroupOf C).Normal := normal_inSubgroup_generalizedFitting C
  ext F
  rw [Set.mem_singleton_iff]
  constructor
  · intro hF
    have hFN : F ≤ N := by
      rcases le_or_le_centralizer_of_mem_lcal hF hNC hNn with h | h
      · exact h
      · exact fun x hx => inf_centralizer_generalizedFitting_le C
          (Subgroup.mem_inf.mpr ⟨lcal_le hF hx, h hx⟩)
    have hFN' : F ∈ lcal N := L511.mem_lcal_of_le hF hFN hNC
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs
        (mem_lcal_iff.mp hFN').2.1 with h | h
    · exfalso
      refine ne_bot_of_not_isMulCommutative (mem_lcal_iff.mp hF).2.2.2 ?_
      refine (Subgroup.eq_bot_iff_forall F).mpr fun x hx => ?_
      have hmem : (⟨x, hFN hx⟩ : N) ∈ F.subgroupOf N := hx
      rw [h, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exact le_antisymm hFN (Subgroup.subgroupOf_eq_top.mp h)
  · rintro rfl
    exact mem_lcal_iff.mpr ⟨hNC, hNn.isSubnormal, hs, hnc⟩

theorem kSetting_of_le [Finite Γ] {p : ℕ} {A B G : Subgroup Γ} (h : KSetting p A G) (hBA : B ≤ A) :
    KSetting p B G where
  prime := h.prime
  elemAbelian := CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le p h.elemAbelian hBA
  normalizes := hBA.trans h.normalizes
  hypB := h.hypB

theorem mem_lcalA_of_le [Finite Γ] {p : ℕ} {A B G J : Subgroup Γ} (h : KSetting p A G)
    (hBA : B ≤ A) (hJ : J ∈ lcalA G A) : J ∈ lcalA G B := by
  refine ⟨hJ.1, fun hB => hJ.2 ?_⟩
  have hle : J ⊓ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) ≤
      J ⊓ Subgroup.centralizer ((B ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) :=
    inf_le_inf_left J (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
      (inf_le_inf_right _ hBA)))
  exact (isSolvable_inf_centralizer_iff_smear h.normalizes hJ.1).mp (isSolvable_of_le hle
    ((isSolvable_inf_centralizer_iff_smear (hBA.trans h.normalizes) hJ.1).mpr hB))

theorem fitting_smear_isSimple
    [Finite Γ] {p : ℕ} {A B G J : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) (hJ : J ∈ lcal G) :
    IsSimpleGroup ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)) ∧
      ¬ IsMulCommutative ↥(CFSG.inSubgroup CFSG.generalizedFitting (smear J B)) :=
  smear_fitting_isSimple (kSetting_of_le h hBA)
    (mem_lcalA_of_le h hBA ((lcalA_eq_lcal_of_kDown_eq_bot h hKA).symm ▸ hJ))

theorem lcal_smear_eq
    [Finite Γ] {p : ℕ} {A B G J : Subgroup Γ} (h : KSetting p A G)
    (hKA : kDown G A = ⊥) (hBA : B ≤ A) (hJ : J ∈ lcal G) :
    lcal (smear J B) = {CFSG.inSubgroup CFSG.generalizedFitting (smear J B)} :=
  lcal_eq_singleton_of_isSimpleGroup (fitting_smear_isSimple h hKA hBA hJ).1
    (fitting_smear_isSimple h hKA hBA hJ).2

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515f
