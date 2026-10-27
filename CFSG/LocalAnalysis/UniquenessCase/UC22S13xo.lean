module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
public import CFSG.LocalAnalysis.UniquenessCase.UC22S13xi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07

variable {G : Type} [Group G] [Finite G]

theorem uc22s13xo_three_dvd_sub_one {n : ℕ} (hn : Even n) : 3 ∣ 2 ^ n - 1 := by
  have h : 2 ^ n % 3 = 1 := by
    obtain ⟨j, rfl⟩ := hn
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  omega

theorem uc22s13xo_center_pRank {L : Subgroup G} {n : ℕ} (hn : IsPowTwo n)
    (hX : IsL2 (Bar2 L) n ∨ IsU3 (Bar2 L) n) :
    center (Bar2 L) = ⊥ ∧ CFSG.Open.pRank 3 L = 1 := by
  refine ⟨(uc22s13xg_even_center_outer hn hX).2.1, ?_⟩
  rcases hX with h | h
  · exact PartTwo.S17.pRank_three_eq_one_of_isL2 h
  · exact PartTwo.S17.pRank_three_eq_one_of_isU3FourPow h hn (PartTwo.s13_two_le_of_isU3 h)

theorem uc22s13xo_three_dvd_card {L : Subgroup G} (h : CFSG.Open.pRank 3 L = 1) :
    3 ∣ Nat.card L := by
  obtain ⟨E, hEL, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  rw [h, pow_one] at hE
  rw [← hE]
  exact Subgroup.card_dvd_of_le hEL

theorem uc22s13xo_hyp81 {M L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M)
    (h₃ : L₃ ∈ calC M) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (s₁ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₁) n ∨ IsU3 (Bar2 L₁) n))
    (s₂ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₂) n ∨ IsU3 (Bar2 L₂) n))
    (s₃ : ∃ n, IsPowTwo n ∧ (IsL2 (Bar2 L₃) n ∨ IsU3 (Bar2 L₃) n)) :
    F08.Hyp81 M (L₁ ⊔ L₂ ⊔ L₃) := by
  classical
  obtain ⟨n₁, hn₁, hX₁⟩ := s₁
  obtain ⟨n₂, hn₂, hX₂⟩ := s₂
  obtain ⟨n₃, hn₃, hX₃⟩ := s₃
  have c₁ := uc22s13xo_center_pRank hn₁ hX₁
  have c₂ := uc22s13xo_center_pRank hn₂ hX₂
  have c₃ := uc22s13xo_center_pRank hn₃ hX₃
  have hle₁ : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hle₂ : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hle₃ : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have hN : ∀ {A B : Subgroup G}, A ∈ calC M → B ∈ calC M → B ≤ normalizer (A : Set G) := by
    intro A B hA hB
    by_cases hAB : A = B
    · subst hAB
      exact Subgroup.le_normalizer
    · exact PartTwo.calC_le_normalizer_of_ne hA hB hAB
  have hS : ∀ L ∈ ({L₁, L₂, L₃} : Finset (Subgroup G)),
      L ∈ calC M ∧ L ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ center (Bar2 L) = ⊥ ∧ CFSG.Open.pRank 3 L = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro L (rfl | rfl | rfl)
    exacts [⟨h₁, hle₁, c₁⟩, ⟨h₂, hle₂, c₂⟩, ⟨h₃, hle₃, c₃⟩]
  have h3 := P22fin3.card_le_pRank_of_finset (X := L₁ ⊔ L₂ ⊔ L₃) Nat.prime_three (by norm_num)
    (fun L hL => P22fin3.mem_calC_of_le_normalizer (hS L hL).1 (hS L hL).2.1
      (sup_le (sup_le (hN (hS L hL).1 h₁) (hN (hS L hL).1 h₂)) (hN (hS L hL).1 h₃)))
    (fun L hL => by
      rw [(hS L hL).2.2.1, Subgroup.card_bot]
      norm_num)
    (fun L hL => uc22s13xo_three_dvd_card (hS L hL).2.2.2)
  rw [Finset.card_eq_three.2 ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩] at h3
  exact ⟨PartTwo.isSubnormal_sup_sup h₁ h₂ h₃, PartTwo.commutator_sup_sup h₁ h₂ h₃, by omega,
    Or.inr ⟨L₁, L₂, L₃, h₁, h₂, h₃, c₁.2, c₂.2, c₃.2, hle₁, hle₂, hle₃,
      PartTwo.coe_sup_sup_eq_mul h₁ h₂ h₃ h12 h13 h23⟩⟩

theorem uc22s13xo_false (hThin : PartTwo.ThinList13) {D : Data G}
    (hS : PartTwo.Setting13 D) (h78 : R7_8R3 D) (h82 : F08.R82 D) {p : ℕ} {B : Subgroup G}
    (hB : F13.Case136b D p B) {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ calC D.M)
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
  obtain ⟨hexp, -, h1, h2, h3⟩ := uc22s13xi_alt1_of_r7_8R3 h78 hH hP rfl
    (hr.trans (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left))
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
