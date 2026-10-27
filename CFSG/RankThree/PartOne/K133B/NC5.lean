module

public import CFSG.RankThree.PartOne.K133B.NC5A
public import CFSG.RankThree.PartOne.K133B.NC5Census
public import CFSG.RankThree.PartOne.K133B.NC5Quot
public import CFSG.RankThree.PartOne.K133B.Pair2
public import CFSG.RankThree.PartOne.Q1327T.GlueDatum
public import CFSG.RankThree.PartOne.Q1327T.ItemBasic

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320X
  CFSG.RankThree.PartOne.Q1327T CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

section Main

theorem row8NotCentral5_holds (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection) : Row8NotCentral5 := by
  classical
  intro G _ _ A c L E h hF13 hEA t ht K hK ⟨g, hmod, hpg⟩ e hetE he1 I hI hKI heI
  have hp : Nat.Prime 5 := h.prime
  have hcard : Nat.card E = 5 ^ 3 := by rw [hEA]; exact h.A_card
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp (by norm_num) h.E_elem
  obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 hetE
  have hvt : t v = v := hv
  have hveE : (v : G) = e := hve
  have hv1 : v ≠ 1 := fun h1 => he1 (by rw [← hveE, h1]; rfl)
  obtain ⟨c₀', x', hc₀1, hc₀fix, hx, hx1, hcardP, hFixgen, hvP, hEtop⟩ :=
    single_geometry hd hcard ht.1 hv1 hvt
  have hxK : (x' : G) ∈ K := hK.2.2.2.1 ⟨x', hx, rfl⟩
  by_cases hfI : (c₀' : G) ∈ I
  ·
    have hEI : E ≤ I := by
      have h1 : (⊤ : Subgroup E) ≤ I.comap E.subtype := by
        rw [← hEtop]
        refine sup_le (Subgroup.zpowers_le.2 ?_) (sup_le (Subgroup.zpowers_le.2 hfI)
          (Subgroup.zpowers_le.2 (hKI hxK)))
        show (v : G) ∈ I
        rw [hveE]
        exact heI
      intro y hy
      exact h1 (Subgroup.mem_top (⟨y, hy⟩ : E))
    exact false_of_E_le hSLB hInsp h hEA ht hK hmod hpg he1 hetE hI hKI hEI
  ·
    set f : G := (c₀' : G) with hfdef
    have hfE : f ∈ E := c₀'.2
    have hf5 : f ^ 5 = 1 := Sec12Three.pow_eq_one_of_mem_E h hfE
    have hf1 : f ≠ 1 := fun h1 => hc₀1 (Subtype.ext h1)
    obtain ⟨hsimp, hnonab, hKP, -, he3, -⟩ := h.setup
    have := hsimp
    have hfe : f ∈ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hveE]
      exact congrArg Subtype.val (hd.comm c₀' v)
    have hrank : evenRank G ≤ 3 :=
      (CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).le.trans he3.le
    have hfN : f ∈ Subgroup.normalizer (I : Set G) :=
      pElement_normalizes_thetaComponentsAt hrank hp (by norm_num) hfe
        ⟨1, by rw [pow_one]; exact orderOf_eq_prime hf5 hf1⟩ hI
    have hfK : ∀ k ∈ K, f * k = k * f := fun k hk =>
      Subgroup.mem_centralizer_iff.1 (isKt_le_centralizer_fixed hK.1 hk) f ⟨c₀', hc₀fix, rfl⟩
    have hItop : I ≠ ⊤ := by
      intro htop
      exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1
        (eq_top_iff.2 (htop ▸ (mem_thetaComponentsAt_iff.1 hI).1))
    have hq : IsQuasisimple (↥I ⧸ aschbacherSolvableCore 5 ↥I) :=
      isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
    have hList := (N143.theoremThreeListHyp_simpleQuot_of_mem_thetaComponentsAt hSLB hKP he3.le
      hp hI hItop).onList
    have hZ5 : IsPGroup 5 (Subgroup.center (↥I ⧸ aschbacherSolvableCore 5 ↥I)) :=
      isPGroup_center_quotient hp
    have hep : e ^ 5 = 1 := Sec12Three.pow_eq_one_of_mem_E h (Subgroup.map_subtype_le _ hetE)
    have hIcent : ∀ n ∈ I, e * n = n * e := fun n hn =>
      Subgroup.mem_centralizer_iff.1 ((mem_thetaComponentsAt_iff.1 hI).1 hn) e rfl
    have hdvd := dvd_card_center_of_mem hp he1 hep hIcent heI
    obtain ⟨n₀, hn₀, hmod5, hcen5⟩ := five_dvd_center_cases hGA hq hZ5 hdvd hList
    obtain ⟨-, F, _, _, hFcard, ⟨emod⟩⟩ := hmod5
    have : Group.IsPerfect (↥I ⧸ aschbacherSolvableCore 5 ↥I) := hq.1
    obtain ⟨h5, ⟨ψ0⟩⟩ := KFSU5.exists_su5_iso hcen5 hn₀ hFcard emod
    have hU : UnitaryFieldData 2 n₀ F :=
      ⟨Nat.prime_two, hn₀, by rw [hFcard, ← pow_mul, mul_comm]⟩
    have heq : unitarySU 2 n₀ F 5 = gamma5 hU := unitarySU_eq_gramSU hU 5
    let ψ : gamma5 hU ≃* (↥I ⧸ aschbacherSolvableCore 5 ↥I) :=
      (MulEquiv.subgroupCongr heq.symm).trans ψ0
    obtain ⟨u, hu⟩ := exists_involution_of_model_PSL hmod
    have hu' : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have hS₀K : Subgroup.zpowers (u : G) ≤ K := Subgroup.zpowers_le.2 u.2
    have hS₀2 : IsPGroup 2 (Subgroup.zpowers (u : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu']; norm_num)
    have hfS : ∀ s ∈ Subgroup.zpowers (u : G), f * s = s * f := fun s hs => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
      exact (Commute.zpow_right (show Commute f (u : G) from hfK u u.2) k).eq
    have hS₀θ : ¬ Subgroup.zpowers (u : G) ≤ inSubgroup (aschbacherSolvableCore 5) I := by
      intro hle
      have huΘ : (u : G) ∈ inSubgroup (aschbacherSolvableCore 5) I :=
        hle (Subgroup.mem_zpowers _)
      obtain ⟨hΘI, hΘn⟩ := theta_le_and_normal (G := G) 5 I
      have hIN := (Subgroup.normal_subgroupOf_iff_le_normalizer hΘI).1 hΘn
      have hnorm : ((inSubgroup (aschbacherSolvableCore 5) I).subgroupOf K).Normal :=
        ⟨fun n hn k => by
          rw [Subgroup.mem_subgroupOf] at hn ⊢
          exact (Subgroup.mem_normalizer_iff.1 (hIN (hKI k.2)) n).1 hn⟩
      obtain ⟨hKs, a, b, hab⟩ := simple_nonab_of_model hmod
      have := hnorm
      rcases hKs.eq_bot_or_eq_top_of_normal
        ((inSubgroup (aschbacherSolvableCore 5) I).subgroupOf K) with hbot | htop
      · have h1 : u ∈ (inSubgroup (aschbacherSolvableCore 5) I).subgroupOf K := huΘ
        rw [hbot, Subgroup.mem_bot] at h1
        rw [h1, orderOf_one] at hu
        omega
      · have hKΘ : K ≤ inSubgroup (aschbacherSolvableCore 5) I := Subgroup.subgroupOf_eq_top.1 htop
        have hsolΘ := (theta_solvable_and_not_dvd hp I).1
        have hsolK : Group.IsSolvable ↥K := Group.isSolvable_of_isSolvable_injective
          (f := Subgroup.inclusion hKΘ) (Subgroup.inclusion_injective hKΘ)
        exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolK a b)
    have h4 := four_le_twoLocalOddRank_of_outer hfN hf5 hfI hU h5 ψ hcen5 (hS₀K.trans hKI) hS₀2
      hS₀θ hfS
    have h1 := CFSG.RankThree.PartTwo.evenRank_subgroup_le (I ⊔ Subgroup.zpowers f)
    have h2 := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G
    have h3 := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank ↥(I ⊔ Subgroup.zpowers f)
    omega

end Main

end CFSG.RankThree.PartOne.K133B
