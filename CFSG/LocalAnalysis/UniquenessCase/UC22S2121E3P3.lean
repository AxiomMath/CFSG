module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78p3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xo
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s2121e3_false_p3 (hThin : PartTwo.ThinList13)
    {D : Data G} (hS : PartTwo.Setting13 D) (hSig : UC6S846.SigmaStd D) (h78 : R7_8R3p3 D)
    (h3 : 3 ∈ D.sig) {B : Subgroup G} (hB : F13.Case136b D 3 B) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (sL : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n))
    (sK : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 K) n ∨ IsU3 (Bar2 K) n))
    {y : G} (hyM : y ∈ D.M) (hyN : y ∈ normalizer (B : Set G)) (hy : orderOf y = 3)
    (hyL : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, hyM⟩ : Bar2 D.M) ∈
      centralizer (barImage D.M L : Set (Bar2 D.M)))
    (hyK : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨y, hyM⟩ : Bar2 D.M) ∈
      centralizer (barImage D.M K : Set (Bar2 D.M))) : False := by
  obtain ⟨hB1, hBM, hBo, hBT, hN, -⟩ := hB
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    hSig.sig1_sp 3 (hS.sig_eq ▸ h3)
  have hex : ∀ X : Subgroup G, X ∈ calC D.M →
      (∃ n, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) →
      ∃ x ∈ X, x ∈ centralizer (B : Set G) ∧ orderOf x = 3 := by
    rintro X hX ⟨n, hn, hXs⟩
    exact uc22s13xm_exists_elem (PartTwo.s13_le_of_mem_calC hX) (hS.hyp131.normal X hX)
      D.sylowM hBM hBo hBT hn hXs Nat.prime_three
      (Or.inl (uc22s13xo_three_dvd_sub_one (uc22s13xg_even_center_outer hn hXs).1))
  obtain ⟨xL, hxLL, hxLB, hxL⟩ := hex L hL sL
  obtain ⟨xK, hxKK, hxKB, hxK⟩ := hex K hK sK
  have hxLM := PartTwo.s13_le_of_mem_calC hL hxLL
  have hxKM := PartTwo.s13_le_of_mem_calC hK hxKK
  have hH : ∀ {x : G}, x ∈ centralizer (B : Set G) → x ∈ D.M →
      x ∈ normalizer (B : Set G) ⊓ D.M :=
    fun hxB hxM => Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ hxB, hxM⟩
  have hbar : ∀ {X : Subgroup G} {x : G} (_ : x ∈ X) (hxM : x ∈ D.M),
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈ barImage D.M X :=
    fun hxX _ => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxX)
  have hns := PartTwo.s13_normalSimple hThin D hS
  have hCL := PartTwo.s13_barImage_isComponent hL
  have hCK := PartTwo.s13_barImage_isComponent hK
  have cKL := PartTwo.s13_components_commute hns hCK hCL hne.symm
  have r1 := uc22s13xm_one_le_pRank_zpowers Nat.prime_three
    (uc22s13xm_orderOf_bar Nat.prime_three (by norm_num) hyM hy)
  have r2 := uc22s13xm_one_le_pRank_zpowers Nat.prime_three
    (uc22s13xm_orderOf_bar Nat.prime_three (by norm_num) hxKM hxK)
  have r12 := uc22s13xm_pRank_sup Nat.prime_three
    (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hCK)
    (zpowers_le.mpr hyK) (zpowers_le.mpr (hbar hxKK hxKM))
  have r3 := uc22s13xm_succ_le_pRank (M := D.M) (K := normalizer (B : Set G) ⊓ D.M)
    Nat.prime_three (by norm_num) inf_le_right
    (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hCL)
    (sup_le (zpowers_le.mpr hyL) (zpowers_le.mpr (cKL (hbar hxKK hxKM))))
    (sup_le (zpowers_le.mpr (hbar (Subgroup.mem_inf.mpr ⟨hyN, hyM⟩) hyM))
      (zpowers_le.mpr (hbar (hH hxKB hxKM) hxKM)))
    (hH hxLB hxLM) hxL (hbar hxLL _)
  have hr : 3 ≤ CFSG.Open.pRank 3 (normalizer (B : Set G) ⊓ D.M) := by omega
  have hHyp := uc22s13xm_sec7Hyp Nat.prime_three (by norm_num) hsp hB1 hBM hN (by omega)
  obtain ⟨P, hP, -, hxLD⟩ := uc22s13xm_exists_sylow Nat.prime_three (hH hxLB hxLM) hxL
  obtain ⟨hexp, h1, h2, h3'⟩ := h78 _ _ _ hHyp hP rfl hr
  have hxKL := uc22s13xm_not_mem Nat.prime_three (by norm_num)
    (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hCL) hxKM hxK (cKL (hbar hxKK hxKM))
  have hxL1 : xL ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxL
    omega
  obtain ⟨nL, hnL, hXL⟩ := sL
  exact uc22s13xm_false_of_alt1 Nat.prime_three (by norm_num) (PartTwo.s13_le_of_mem_calC hL)
    (hS.hyp131.normal L hL) hnL hXL hP hexp h1 h2 h3' hxLD hxLL hxL1 (hH hxKB hxKM) hxK hxKL

end CFSG.LocalAnalysis.UniquenessCase.UC22
