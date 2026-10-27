module

public import CFSG.RankThree.PartTwo.Sec21.HeringHullChain1

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringHull

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

theorem llRel_of_mem_thetaQuotCentralizer (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hG : TheoremFourHyp G) {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {a a' : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (ha'A : a' ∈ A) (ha'1 : a' ≠ 1) {Z K : Subgroup G} (hZ : Z ∈ thetaComponentsAt 3 a)
    (hK : K ∈ thetaComponentsAt 3 a') (hZK : llRel Z K) (ha : a ∈ thetaQuotCentralizer K) :
    llRel K Z := by
  obtain ⟨ha'Z, hYK⟩ := residual_le_of_llRel h45 h48 hG hAe hAn haA ha1 ha'A ha'1 hZ hK hZK
  have hZ' : Z ∈ thetaComponentsIn (Subgroup.centralizer ({a} : Set G)) := by
    rw [← thetaComponentsAt_eq_thetaComponentsIn]
    exact hZ
  have hZC : Z ≤ Subgroup.centralizer ({a} : Set G) := le_of_mem_thetaComponentsIn hZ'
  have hZp : Group.IsPerfect Z := CFSG.RankThree.PartTwo.Sec6.isPerfect_of_mem_thetaComponentsAt hZ
  have hZq : IsQuasisimple (Z ⧸ aschbacherSolvableCore 3 Z) :=
    CFSG.RankThree.PartTwo.Sec6.isQuasisimple_of_mem_thetaComponentsAt hZ
  have hKp : Group.IsPerfect K := CFSG.RankThree.PartTwo.Sec6.isPerfect_of_mem_thetaComponentsAt hK
  have hD3 : IsPGroup 3 (Subgroup.zpowers a) :=
    CFSG.RankThree.PartTwo.Sec6.isPGroup_zpowers_of_pow_three (hAe.2 a haA)
  have hD'3 : IsPGroup 3 (Subgroup.zpowers a') :=
    CFSG.RankThree.PartTwo.Sec6.isPGroup_zpowers_of_pow_three (hAe.2 a' ha'A)
  have hDC : Subgroup.zpowers a ≤ thetaQuotCentralizer K := Subgroup.zpowers_le.mpr ha
  have hY1M : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ∈
      thetaComponentsIn (Subgroup.centralizer ({a} : Set G) ⊓
        Subgroup.centralizer ({a'} : Set G)) := by
    have h := CFSG.RankThree.PartTwo.Sec6.residual_inf_centralizer_mem_thetaComponentsIn hK hD3 hDC
    rw [CFSG.RankThree.PartTwo.Sec6.centralizer_zpowers_eq] at h
    exact h
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩))
  have hM : SectionFourHyp (Subgroup.centralizer ({a} : Set G)) :=
    hG.sectionFourHyp (CFSG.RankThree.PartTwo.Sec6.centralizer_ne_top_of_ne_one hG ha1)
  obtain ⟨M', hM', hY1M'⟩ :=
    CFSG.RankThree.PartTwo.Sec6.exists_le_mem_thetaComponentsIn h48 hM hAC hAe hAn ha'A ha'1
      hY1M
  have hYp : Group.IsPerfect
      (inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G))) :=
    CFSG.RankThree.PartTwo.Sec6.isPerfect_inSubgroup_perfectResidual _
  have hYne : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G)) ≠ ⊥ := by
    have h := CFSG.RankThree.PartTwo.Sec6.residual_inf_centralizer_ne_bot hZp hZq hD'3
      (Subgroup.zpowers_le.mpr ha'Z)
    rw [CFSG.RankThree.PartTwo.Sec6.centralizer_zpowers_eq] at h
    exact h
  have hYZ : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G)) ≤ Z :=
    (CFSG.RankThree.PartTwo.Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hYKC : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G)) ≤
      K ⊓ Subgroup.centralizer ({a} : Set G) :=
    le_inf hYK (hYZ.trans hZC)
  have hYM' : inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G)) ≤ M' :=
    (CFSG.RankThree.PartTwo.Sec6.le_inSubgroup_perfectResidual_of_isPerfect hYp hYKC).trans hY1M'
  have hMZ : M' = Z :=
    CFSG.RankThree.PartTwo.Sec6.eq_of_mem_thetaComponentsIn_of_le hM' hZ' hYp hYne hYM' hYZ
  have hY1KZ : inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K ⊓ Z :=
    le_inf ((CFSG.RankThree.PartTwo.Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left)
      (hY1M'.trans hMZ.le)
  have hKY1 : K ≤ inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K := by
    have h := CFSG.RankThree.PartTwo.Sec6.le_residual_inf_centralizer_sup_theta hKp hD3 hDC
    rw [CFSG.RankThree.PartTwo.Sec6.centralizer_zpowers_eq] at h
    exact h
  show K = inSubgroup perfectResidual (K ⊓ Z) ⊔ inSubgroup (aschbacherSolvableCore 3) K
  refine le_antisymm (hKY1.trans (sup_le_sup_right
    (CFSG.RankThree.PartTwo.Sec6.le_inSubgroup_perfectResidual_of_isPerfect
      (CFSG.RankThree.PartTwo.Sec6.isPerfect_inSubgroup_perfectResidual _) hY1KZ) _)) ?_
  exact sup_le ((CFSG.RankThree.PartTwo.Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left)
    (CFSG.RankThree.PartTwo.Sec6.theta_le K)

end CFSG.RankThree.PartTwo.Sec21.HeringHull
