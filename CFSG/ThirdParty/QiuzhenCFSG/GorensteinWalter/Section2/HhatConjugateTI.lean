module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerEqOfNontrivialNormalInCoatom
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugate-TI control for subgroups of `F(Ĥ)`

The core of the first-case `F(U) ∩ F(U)^g = ⊥` argument, stated directly
for `CentralizerSetup`: a nontrivial subgroup of `F(Ĥ)` whose ambient
normalizer lies in the conjugate `Ĥ^g` must have `g ∈ Ĥ`.  The proof is the
Lemma 2.5 pattern: such an `X` witnesses `NormalizerControlledBy Ĥ Ĥ^g`,
Lemma 2.5 forces `Ĥ = Ĥ^g`, and self-normalization of the maximal subgroup
`Ĥ` puts `g` in `Ĥ`.

The second theorem is the paper's "normal in both `Ĥ` and `Ĥ^g`" corollary:
if `X` is nontrivial, lies in `F(Ĥ)`, and is normal in both `Ĥ` and `Ĥ^g`,
then `g ∈ Ĥ`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem mem_Hhat_of_mem_normalizer
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    {g : G} (hg : g ∈ Subgroup.normalizer (c.Hhat : Set G)) :
    g ∈ c.Hhat := by
  have hHhatne : c.Hhat ≠ ⊥ := by
    intro hbot
    have htH : c.t ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact (Subgroup.mem_centralizer_singleton_iff).mpr rfl
    have htHhat : c.t ∈ c.Hhat := c.H_le_Hhat htH
    rw [hbot] at htHhat
    exact c.t_involution.1 (Subgroup.mem_bot.mp htHhat)
  have hN : Subgroup.normalizer (c.Hhat : Set G) = c.Hhat :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) c.Hhat_maximal le_rfl hHhatne
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (H := c.Hhat) (N := c.Hhat) Subgroup.le_normalizer)
  rw [← hN]
  exact hg

/-- A nontrivial subgroup of `F(Ĥ)` whose normalizer lies in `Ĥ^g` forces
`g ∈ Ĥ`. -/
public theorem hhat_conjugate_TI_of_normalizer_control
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (X : Subgroup G) (hXne : X ≠ ⊥)
    (hXleF : X ≤ fittingSubgroupOf c.Hhat)
    (g : G)
    (hNX : Subgroup.normalizer (X : Set G) ≤
      conjugateSubgroup c.Hhat g) :
    g ∈ c.Hhat := by
  classical
  have hcontrol : NormalizerControlledBy c.Hhat
      (conjugateSubgroup c.Hhat g) :=
    ⟨X, hXne, hXleF, hNX⟩
  have hodd : oddCoreOf c.Hhat ≠ ⊥ := by
    rw [← (theorem_2_6 hmin c).1]
    exact (lemma_2_2 hmin c).2
  have hEq : c.Hhat = conjugateSubgroup c.Hhat g :=
    lemma_2_5 hmin c g hcontrol hodd
  have hgNorm : g ∈ Subgroup.normalizer (c.Hhat : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEq.symm
  exact mem_Hhat_of_mem_normalizer hmin c hgNorm

/-- If a nontrivial subgroup of `F(Ĥ)` is normal in both `Ĥ` and `Ĥ^g`,
then `g ∈ Ĥ`. -/
public theorem hhat_conjugate_TI_of_normal_in_both
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (X : Subgroup G) (hXne : X ≠ ⊥)
    (hXleF : X ≤ fittingSubgroupOf c.Hhat)
    (g : G)
    (hXnH : IsNormalIn X c.Hhat)
    (hXnHg : IsNormalIn X (conjugateSubgroup c.Hhat g)) :
    g ∈ c.Hhat := by
  classical
  let Hg : Subgroup G := conjugateSubgroup c.Hhat g
  have hHhat_le_N : c.Hhat ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_isNormalIn hXnH
  have hHg_le_N : Hg ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_isNormalIn hXnHg
  have hXleHhat : X ≤ c.Hhat :=
    hXleF.trans (fittingSubgroupOf_isNormalIn c.Hhat).1
  have hNne : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro hNtop
    have hXnormalG : X.Normal := (Subgroup.normalizer_eq_top_iff).mp hNtop
    rcases (haveI := hXnormalG; (minimalCounterexample_isSimple hmin).eq_bot_or_eq_top_of_normal X) with hbot | htop
    · exact hXne hbot
    · have hHhatTop : c.Hhat = ⊤ := top_unique (htop ▸ hXleHhat)
      exact c.Hhat_maximal.1 hHhatTop
  have hXnH_normal : (X.subgroupOf c.Hhat).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := c.Hhat) (N := X) hHhat_le_N
  have hN_eq_Hhat : Subgroup.normalizer (X : Set G) = c.Hhat :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) c.Hhat_maximal
      hXleHhat hXne hXnH_normal
  have hHg_coatom : IsCoatom Hg := by
    exact (OrderIso.isCoatom_iff ((MulAut.conj g).mapSubgroup) c.Hhat).mpr
      c.Hhat_maximal
  have hXleHg : X ≤ Hg := hXnHg.1
  have hXnHg_normal : (X.subgroupOf Hg).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := Hg) (N := X) hHg_le_N
  have hN_eq_Hg : Subgroup.normalizer (X : Set G) = Hg :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) hHg_coatom
      hXleHg hXne hXnHg_normal
  have hEq : c.Hhat = Hg := by
    rw [← hN_eq_Hhat, hN_eq_Hg]
  have hgNorm : g ∈ Subgroup.normalizer (c.Hhat : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEq.symm
  exact mem_Hhat_of_mem_normalizer hmin c hgNorm

end CFSG.GorensteinWalter
