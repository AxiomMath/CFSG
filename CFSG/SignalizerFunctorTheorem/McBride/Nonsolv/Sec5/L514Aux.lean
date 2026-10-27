module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Fixed
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.SmearEquiv
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem smear_fitting_isSimple
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G)
    (hJ : J ∈ lcalA G A) :
    IsSimpleGroup (CFSG.inSubgroup CFSG.generalizedFitting (smear J A)) ∧
      ¬ IsMulCommutative (CFSG.inSubgroup CFSG.generalizedFitting (smear J A)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_smear h.normalizes hJ.1
  exact (isFStarSimple_iff_inSubgroup _).mp ((isFStarSimple_congr e).mpr (hypA_fixed h hJ).2.1)

theorem fitting_smear_le_of_normal
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G)
    (hJ : J ∈ lcalA G A) {N : Subgroup Γ} (hN : N ≤ smear J A)
    (hNn : (N.subgroupOf (smear J A)).Normal) (hN1 : N ≠ ⊥) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ N := by
  obtain ⟨hFs, hFnc⟩ := smear_fitting_isSimple h hJ
  have hFn := normal_inSubgroup_generalizedFitting (smear J A)
  have hcent54 := inf_centralizer_generalizedFitting_le (smear J A)
  set F := CFSG.inSubgroup CFSG.generalizedFitting (smear J A) with hF
  have hFC : F ≤ smear J A := Subgroup.map_subtype_le _
  have hNF : ((N ⊓ F).subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_right]
    intro n f hn hf
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hN).mp hNn n f hn.1 (hFC hf),
        mul_mem (mul_mem hf hn.2) (inv_mem hf)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ F).subgroupOf F) with hbot | htop
  · exfalso
    apply hN1
    rw [eq_bot_iff]
    intro n hn
    have hcent : n ∈ Subgroup.centralizer (F : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 : ⁅n, f⁆ ∈ N ⊓ F := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have := (Subgroup.normal_subgroupOf_iff hN).mp hNn n⁻¹ f (inv_mem hn) (hFC hf)
          have e : ⁅n, f⁆ = n * (f * n⁻¹ * f⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [e]
          exact mul_mem hn this
        · have := (Subgroup.normal_subgroupOf_iff hFC).mp hFn f n hf (hN hn)
          exact mul_mem this (inv_mem hf)
      have h2 : (⟨⁅n, f⁆, (Subgroup.mem_inf.mp h1).2⟩ : ↥F) ∈ (N ⊓ F).subgroupOf F := h1
      rw [hbot, Subgroup.mem_bot] at h2
      exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val h2)).symm
    have hnF : n ∈ F := hcent54 (Subgroup.mem_inf.mpr ⟨hN hn, hcent⟩)
    have h4 : (⟨n, hnF⟩ : ↥F) ∈ (N ⊓ F).subgroupOf F := Subgroup.mem_inf.mpr ⟨hn, hnF⟩
    rw [hbot, Subgroup.mem_bot] at h4
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h4)
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left

theorem eq_bot_of_isSolvable_of_normalized
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G)
    (hJ : J ∈ lcalA G A) {Y : Subgroup Γ} (hYJ : Y ≤ J) (hY : Group.IsSolvable Y)
    (hnorm : J ⊓ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) ≤
      Subgroup.normalizer (Y : Set Γ)) : Y = ⊥ :=
  (hypA_fixed h hJ).1 Y hYJ hY hnorm

theorem centralizes_of_centralizes_fixed
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G)
    (hJ : J ∈ lcalA G A) {x : Γ} (hx : x ∈ Subgroup.normalizer (J : Set Γ))
    (hxp : Nat.Coprime p (orderOf x))
    (hfix : ∀ y ∈ J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ), x * y * x⁻¹ = y) :
    ∀ j ∈ J, x * j * x⁻¹ = j :=
  (hypA_fixed h hJ).2.2 x hx hxp hfix

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
