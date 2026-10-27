module

public import CFSG.RankThree.PartTwo.Sec21.HeringHullStep
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringHull

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_mem_thetaComponentsAt (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    {Z : Subgroup G} (hZ : Z ∈ thetaComponentsAt 3 a) :
    A ≤ Subgroup.normalizer (Z : Set G) :=
  Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 Z hZ

theorem residual_le_of_llRel (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (hG : TheoremFourHyp G)
    {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {a a' : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (ha'A : a' ∈ A) (ha'1 : a' ≠ 1) {Z K : Subgroup G} (hZ : Z ∈ thetaComponentsAt 3 a)
    (hK : K ∈ thetaComponentsAt 3 a') (hZK : llRel Z K) :
    a' ∈ thetaQuotCentralizer Z ∧
      inSubgroup perfectResidual (Z ⊓ Subgroup.centralizer ({a'} : Set G)) ≤ K := by
  have ha'N : a' ∈ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hAn haA ha1 hZ ha'A
  have hKC : K ≤ Subgroup.centralizer ({a'} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hK
  have ha'Q : a' ∈ thetaQuotCentralizer Z :=
    Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨ha'N, trivial_mod_theta_of_llRel hZK hKC ha'N⟩
  refine ⟨ha'Q, ?_⟩
  have ha'3 : a' ^ 3 = 1 := hAe.2 a' ha'A
  have hD3 : IsPGroup 3 (Subgroup.zpowers a') := Sec6.isPGroup_zpowers_of_pow_three ha'3
  have hDC : Subgroup.zpowers a' ≤ thetaQuotCentralizer Z := Subgroup.zpowers_le.mpr ha'Q
  have hY := Sec6.residual_inf_centralizer_mem_thetaComponentsIn hZ hD3 hDC
  rw [Sec6.centralizer_zpowers_eq] at hY
  have hM : SectionFourHyp (Subgroup.centralizer ({a'} : Set G)) :=
    hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG ha'1)
  have hAC : A ≤ Subgroup.centralizer ({a'} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨a', ha'A⟩))
  obtain ⟨M, hM', hYM⟩ := Sec6.exists_le_mem_thetaComponentsIn h48 hM hAC hAe hAn haA ha1 hY
  have hK' : K ∈ thetaComponentsIn (Subgroup.centralizer ({a'} : Set G)) := by
    rw [← thetaComponentsAt_eq_thetaComponentsIn a']
    exact hK
  have hJZK : inSubgroup perfectResidual (Z ⊓ K) ≤ Z ⊓ K :=
    Sec6.inSubgroup_perfectResidual_le _
  have hJp : Group.IsPerfect (inSubgroup perfectResidual (Z ⊓ K)) :=
    Sec6.isPerfect_inSubgroup_perfectResidual _
  have hJ1 : inSubgroup perfectResidual (Z ⊓ K) ≠ ⊥ := by
    intro hJ
    have h : Z = inSubgroup perfectResidual (Z ⊓ K) ⊔ inSubgroup (aschbacherSolvableCore 3) Z :=
      hZK
    rw [hJ, bot_sup_eq] at h
    exact Sec6.theta_ne_of_mem_thetaComponentsAt hZ h.symm
  have hJZC : inSubgroup perfectResidual (Z ⊓ K) ≤ Z ⊓ Subgroup.centralizer ({a'} : Set G) :=
    le_inf (hJZK.trans inf_le_left) ((hJZK.trans inf_le_right).trans hKC)
  have hJM : inSubgroup perfectResidual (Z ⊓ K) ≤ M :=
    (Sec6.le_inSubgroup_perfectResidual_of_isPerfect hJp hJZC).trans hYM
  have hMK : M = K :=
    Sec6.eq_of_mem_thetaComponentsIn_of_le hM' hK' hJp hJ1 hJM (hJZK.trans inf_le_right)
  exact hYM.trans hMK.le

theorem le_of_llRel_of_isQuasisimple (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hG : TheoremFourHyp G) {A : Subgroup G} (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n) {a a' : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (ha'A : a' ∈ A) (ha'1 : a' ≠ 1) {Z K : Subgroup G} (hZ : Z ∈ thetaComponentsAt 3 a)
    (hK : K ∈ thetaComponentsAt 3 a') (hZK : llRel Z K) {P : Subgroup G}
    (hP : IsQuasisimple P) (hPZ : P ≤ Z) (hPA : A ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ K := by
  obtain ⟨ha'Q, hY⟩ := residual_le_of_llRel h45 h48 hG hAe hAn haA ha1 ha'A ha'1 hZ hK hZK
  have htriv : ∀ z ∈ Z, z⁻¹ * (a' * z * a'⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Z :=
    (Sec6.mem_thetaQuotCentralizer_iff.mp ha'Q).2
  have hPC : P ≤ Subgroup.centralizer ({a'} : Set G) :=
    le_centralizer_of_isQuasisimple hP hPZ (hPA ha'A) htriv
  exact (Sec6.le_inSubgroup_perfectResidual_of_isPerfect hP.1 (le_inf hPZ hPC)).trans hY

end CFSG.RankThree.PartTwo.Sec21.HeringHull
