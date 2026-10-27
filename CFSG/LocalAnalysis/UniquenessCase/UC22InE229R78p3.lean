module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xo
import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)

variable {G : Type} [Group G] [Finite G]

@[expose] def R7_8R3p3 (D : Data G) : Prop :=
  ∀ H P D₀ : Subgroup G, Sec7Hyp D 3 H → CFSG.ABGLocalTools.IsSylowOf 3 P (H ⊓ D.M) →
    D₀ = CFSG.RankThree.PartOne.omegaOne 3 P → 3 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) →
      (∀ x ∈ D₀, x ^ 3 = 1) ∧
        (H ⊓ D.M = H ⊓ normalizer (P : Set G) ∧
          IrrOnMod (rankThreeLayer H ⊓ normalizer (P : Set G)) D₀ (inSubgroup frattini D₀) ∧
          P = D₀)

theorem uc22ine229_s13xo_false_p3 (hThin : PartTwo.ThinList13)
    {D : Data G} (hS : PartTwo.Setting13 D) (h78 : R7_8R3p3 D) (h82 : F08.R82 D) {p : ℕ}
    {B : Subgroup G} (hB : F13.Case136b D p B) {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ calC D.M)
    (h₂ : L₂ ∈ calC D.M) (h₃ : L₃ ∈ calC D.M) (h12 : barImage D.M L₁ ≠ barImage D.M L₂)
    (h13 : barImage D.M L₁ ≠ barImage D.M L₃) (h23 : barImage D.M L₂ ≠ barImage D.M L₃)
    (s₁ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₁) n ∨ IsU3 (Bar2 L₁) n))
    (s₂ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₂) n ∨ IsU3 (Bar2 L₂) n))
    (s₃ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₃) n ∨ IsU3 (Bar2 L₃) n)) : False := by
  obtain ⟨hB1, hBM, hBo, hBT, hN, -⟩ := hB
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    h82 _ (uc22s13xo_hyp81 h₁ h₂ h₃ (fun h => h12 (congrArg (barImage D.M) h))
      (fun h => h13 (congrArg (barImage D.M) h)) (fun h => h23 (congrArg (barImage D.M) h))
      s₁ s₂ s₃)
  have hex : ∀ L : Subgroup G, L ∈ calC D.M →
      (∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n)) →
      ∃ x ∈ L, x ∈ centralizer (B : Set G) ∧ orderOf x = 3 := by
    rintro L hL ⟨n, hn, hX⟩
    exact uc22s13xm_exists_elem (PartTwo.s13_le_of_mem_calC hL) (hS.hyp131.normal L hL)
      D.sylowM hBM hBo hBT hn hX Nat.prime_three
      (Or.inl (uc22s13xo_three_dvd_sub_one (uc22s13xg_even_center_outer hn hX).1))
  obtain ⟨x₁, hx₁L, hx₁B, hx₁⟩ := hex L₁ h₁ s₁
  obtain ⟨x₂, hx₂L, hx₂B, hx₂⟩ := hex L₂ h₂ s₂
  obtain ⟨x₃, hx₃L, hx₃B, hx₃⟩ := hex L₃ h₃ s₃
  have hx₁M := PartTwo.s13_le_of_mem_calC h₁ hx₁L
  have hx₂M := PartTwo.s13_le_of_mem_calC h₂ hx₂L
  have hx₃M := PartTwo.s13_le_of_mem_calC h₃ hx₃L
  have hK : ∀ {x : G}, x ∈ centralizer (B : Set G) → x ∈ D.M →
      x ∈ normalizer (B : Set G) ⊓ D.M :=
    fun hxB hxM => Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ hxB, hxM⟩
  have hbar : ∀ {L : Subgroup G} {x : G} (_ : x ∈ L) (hxM : x ∈ D.M),
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨x, hxM⟩ : Bar2 D.M) ∈ barImage D.M L :=
    fun hxL _ => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL)
  have hns := PartTwo.s13_normalSimple hThin D hS
  have hC₁ := PartTwo.s13_barImage_isComponent h₁
  have hC₂ := PartTwo.s13_barImage_isComponent h₂
  have hC₃ := PartTwo.s13_barImage_isComponent h₃
  have c12 := PartTwo.s13_components_commute hns hC₁ hC₂ h12
  have c21 := PartTwo.s13_components_commute hns hC₂ hC₁ h12.symm
  have c13 := PartTwo.s13_components_commute hns hC₁ hC₃ h13
  have c23 := PartTwo.s13_components_commute hns hC₂ hC₃ h23
  have r1 := uc22s13xm_one_le_pRank_zpowers Nat.prime_three
    (uc22s13xm_orderOf_bar Nat.prime_three (by norm_num) hx₁M hx₁)
  have r2 := uc22s13xm_one_le_pRank_zpowers Nat.prime_three
    (uc22s13xm_orderOf_bar Nat.prime_three (by norm_num) hx₂M hx₂)
  have r12 := uc22s13xm_pRank_sup Nat.prime_three
    (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hC₂)
    (zpowers_le.mpr (c12 (hbar hx₁L hx₁M))) (zpowers_le.mpr (hbar hx₂L hx₂M))
  have r3 := uc22s13xm_succ_le_pRank (M := D.M) (K := normalizer (B : Set G) ⊓ D.M)
    Nat.prime_three (by norm_num) inf_le_right
    (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hC₃)
    (sup_le (zpowers_le.mpr (c13 (hbar hx₁L hx₁M))) (zpowers_le.mpr (c23 (hbar hx₂L hx₂M))))
    (sup_le (zpowers_le.mpr (hbar (hK hx₁B hx₁M) hx₁M))
      (zpowers_le.mpr (hbar (hK hx₂B hx₂M) hx₂M)))
    (hK hx₃B hx₃M) hx₃ (hbar hx₃L _)
  have hr : 3 ≤ CFSG.Open.pRank 3 (normalizer (B : Set G) ⊓ D.M) := by omega
  have hH := uc22s13xm_sec7Hyp Nat.prime_three (by norm_num) hsp hB1 hBM hN (by omega)
  obtain ⟨P, hP, -, hx₁D⟩ := uc22s13xm_exists_sylow Nat.prime_three (hK hx₁B hx₁M) hx₁
  obtain ⟨hexp, h1, h2, h3⟩ := h78 _ _ _ hH hP rfl hr
  have hx₂L₁ := uc22s13xm_not_mem Nat.prime_three (by norm_num)
    (PartTwo.s13_Layer13_inf_centralizer_eq_bot hns hC₁) hx₂M hx₂ (c21 (hbar hx₂L hx₂M))
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx₁
    omega
  obtain ⟨n₁, hn₁, hX₁⟩ := s₁
  exact uc22s13xm_false_of_alt1 Nat.prime_three (by norm_num) (PartTwo.s13_le_of_mem_calC h₁)
    (hS.hyp131.normal L₁ h₁) hn₁ hX₁ hP hexp h1 h2 h3 hx₁D hx₁L hx₁1 (hK hx₂B hx₂M) hx₂ hx₂L₁

end CFSG.LocalAnalysis.UniquenessCase.UC22
