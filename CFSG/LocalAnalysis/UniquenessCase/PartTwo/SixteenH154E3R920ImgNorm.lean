module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Cfg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920ImgFrat
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_img9_of_pGroup {D : Data G} {L D₃ A H : Subgroup G}
    (c : R920Cfg D L D₃ A) (hLH : L ≤ H) {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 7)
    {Pb : Subgroup (F09.Hbar9 H)} (hPb : IsPGroup p Pb)
    (hB : ∃ B : Subgroup G, B ≤ L ∧ Nat.card B = p ∧ F09.img9 H B ≤ Pb) :
    normalizer (Pb : Set (F09.Hbar9 H)) ≤ F09.img9 H (H ⊓ D.M) := by
  classical
  obtain ⟨B, hBL, hBcard, hBimg⟩ := hB
  have hBH : B ≤ H := hBL.trans hLH
  let Γ := ↥H
  let N : Subgroup Γ := CFSG.pPrimeCore 3 Γ
  haveI hNnorm : N.Normal := CFSG.pPrimeCore_normal
  let π : Γ →* Γ ⧸ N := QuotientGroup.mk' N
  let H₁ : Subgroup Γ := Pb.comap π
  have hB'card : Nat.card (B.subgroupOf H) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv, hBcard]
  have hB'pg : IsPGroup p (B.subgroupOf H) :=
    IsPGroup.of_card (n := 1) (by rw [hB'card, pow_one])
  have hB'le : B.subgroupOf H ≤ H₁ := by
    intro x hx
    exact hBimg (Subgroup.mem_map_of_mem π hx)
  obtain ⟨Q, hQle⟩ := (hB'pg.comap_subtype (K := H₁)).exists_le_sylow
  let P₁ : Subgroup Γ := (Q : Subgroup H₁).map H₁.subtype
  have hP₁syl : IsSylowOf p P₁ H₁ := ⟨Q, rfl⟩
  have hB'le_P₁ : B.subgroupOf H ≤ P₁ := by
    intro x hx
    exact ⟨⟨x, hB'le hx⟩, hQle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hNle : N ≤ H₁ := by
    intro x hx
    show π x ∈ Pb
    have hx1 : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hx1]
    exact Pb.one_mem
  have hH₁map : H₁.map π = Pb :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Pb
  have hrel : (P₁.map π).relIndex Pb = (P₁ ⊔ N).relIndex H₁ := by
    have h := Subgroup.relIndex_map_map π P₁ H₁
    rw [hH₁map, QuotientGroup.ker_mk', sup_eq_left.mpr hNle] at h
    exact h
  have hP₁dvd : ¬ p ∣ P₁.relIndex H₁ := (isSylowOf_iff.mp hP₁syl).2.2
  have hsup_le : P₁ ⊔ N ≤ H₁ := sup_le hP₁syl.le hNle
  have hnotdvd : ¬ p ∣ (P₁ ⊔ N).relIndex H₁ := by
    intro hdvd
    apply hP₁dvd
    rw [← Subgroup.relIndex_mul_relIndex (H := P₁) (K := P₁ ⊔ N) (L := H₁)
      le_sup_left hsup_le]
    exact dvd_mul_of_dvd_right hdvd _
  have hmap_le : P₁.map π ≤ Pb := by
    rw [← hH₁map]
    exact Subgroup.map_mono hP₁syl.le
  have hmap_pg : IsPGroup p (P₁.map π) := hP₁syl.isPGroup.map π
  have himg_syl : IsSylowOf p (P₁.map π) Pb := by
    rw [isSylowOf_iff]
    exact ⟨hmap_le, hmap_pg, by rw [hrel]; exact hnotdvd⟩
  have hPmap : P₁.map π = Pb := (himg_syl.eq_of_le hmap_le le_rfl hPb).symm
  have hBuniq : B ∈ uniqueSet D.M := by
    rcases hp with h3 | h7
    · have h := hBcard
      rw [h3] at h
      exact c.mem_uniqueSet_of_card_three hBL h
    · have h := hBcard
      rw [h7] at h
      exact c.mem_uniqueSet_of_card_seven hBL h
  let P₁G : Subgroup G := P₁.map H.subtype
  have hP₁Gpg : IsPGroup p P₁G := hP₁syl.isPGroup.map H.subtype
  have hBmap : (B.subgroupOf H).map H.subtype = B := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hBH]
  have hBP₁G : B ≤ P₁G := by
    rw [← hBmap]
    exact Subgroup.map_mono hB'le_P₁
  have hP₁GM : P₁G ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      D.maxLocal hBuniq hBP₁G hP₁Gpg
  have hP₁Guniq : P₁G ∈ uniqueSet D.M :=
    CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hBuniq hBP₁G hP₁GM
  have hNormP₁G : normalizer (P₁G : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hP₁Guniq
  have hNormLe : normalizer (P₁ : Set Γ) ≤ (H ⊓ D.M).subgroupOf H := by
    intro n hn
    have hn' : (n : G) ∈ normalizer (P₁G : Set G) :=
      Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem H.subtype hn)
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨n.2, hNormP₁G hn'⟩)
  have hmap_le_img : (normalizer (P₁ : Set Γ)).map π ≤ F09.img9 H (H ⊓ D.M) := by
    show (normalizer (P₁ : Set Γ)).map π ≤ ((H ⊓ D.M).subgroupOf H).map π
    exact Subgroup.map_mono hNormLe
  have hfrat : normalizer (Pb : Set (Γ ⧸ N)) ≤
      (normalizer (P₁ : Set Γ)).map (QuotientGroup.mk' N) :=
    normalizer_le_map_normalizer_of_sylow N hPmap hP₁syl
  exact hfrat.trans hmap_le_img

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
