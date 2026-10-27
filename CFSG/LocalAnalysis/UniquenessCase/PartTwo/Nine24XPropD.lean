module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropDImg
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_I9_sup_of_hyp97_L2_4n (D : Data G) (hR92 : F09.R92 D) (hKD : KFact913L2Even)
    {Y H D₃ S X : Subgroup G} {n : ℕ} (hyp : F09.Hyp97 D Y H D₃ S) (hYX : Opp 3 Y = X)
    (hn : 1 < n) (hL2 : IsL2 (Bar2 X) (2 * n)) (hXp : ⁅X, X⁆ = X)
    (hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H) (hXY : (X.subgroupOf Y).Normal)
    (hHt : H ≠ ⊤) : H = F09.I9 H ⊔ (H ⊓ D.M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYH : Y ≤ H := hyp.1.2.1.1
  have hYM : Y ≤ D.M := hyp.1.1.1
  have hXYle : X ≤ Y := hYX ▸ F09.opp_le_self 3 Y
  have hXH : X ≤ H := hXYle.trans hYH
  have hXL : X ≤ F09.L9 Y H := hYX ▸ F09.opp_le_L9 Y H
  obtain ⟨hHsup, hShape⟩ := hR92 Y H D₃ hyp.1 hHt
  have hLH : F09.L9 Y H ≤ H := le_sup_left.trans (le_of_eq hHsup.symm)
  have hLbNormal : (F09.img9 H (F09.L9 Y H)).Normal := F09.img9_L9_normal hYH
  have hSodd : ¬ 2 ∣ (S.subgroupOf H).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hSH).2.2
  have hSbSyl : CFSG.ABGLocalTools.IsSylowOf 2 (F09.img9 H S) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, ?_, ?_⟩
    · exact (hSH.isPGroup.comap_subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))
    · rw [Subgroup.relIndex_top_right]
      exact fun h2 => hSodd (h2.trans (Subgroup.index_map_dvd (S.subgroupOf H)
        (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))
        (QuotientGroup.mk'_surjective _)))
  have hXbLb : F09.img9 H X ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hXL)
  have hXbPerfect : ⁅F09.img9 H X, F09.img9 H X⁆ = F09.img9 H X := by
    have h1 : X.subgroupOf H = ⁅X.subgroupOf H, X.subgroupOf H⁆ := by
      apply (Subgroup.map_subtype_inj (H := H)).mp
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hXH, hXp]
    change ⁅(X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)),
        (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))⁆ =
      (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))
    rw [← Subgroup.map_commutator, ← h1]
  have hYnorm : Y ≤ normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXYle).mp hXY
  have hSnorm : S ≤ normalizer (X : Set G) := hyp.2.2.2.le.trans hYnorm
  have hSbNorm : F09.img9 H S ≤ normalizer (F09.img9 H X : Set (F09.Hbar9 H)) := by
    have h1 : S.subgroupOf H ≤ normalizer (X.subgroupOf H : Set ↥H) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hXH]
      exact Subgroup.subgroupOf_mono H hSnorm
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map
      (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)))
  have hImgL2 : IsL2 (Bar2 (F09.img9 H X)) (2 * n) := isL2_bar2_img9 hXH hL2
  have hXbEqLb : F09.img9 H X = F09.img9 H (F09.L9 Y H) :=
    hKD (F09.Hbar9 H) (F09.img9 H (F09.L9 Y H)) (F09.img9 H S) (F09.img9 H X) n
      hLbNormal hShape hSbSyl hXbLb hXbPerfect hSbNorm hn hImgL2
  have hLsupI : F09.L9 Y H ≤ F09.I9 H ⊔ X := by
    intro l hl
    have hlH : l ∈ H := hLH hl
    have hmemLb : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ⟨l, hlH⟩ ∈
        F09.img9 H (F09.L9 Y H) :=
      Subgroup.mem_map.mpr ⟨⟨l, hlH⟩, mem_subgroupOf.mpr hl, rfl⟩
    have hmemXb : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ⟨l, hlH⟩ ∈ F09.img9 H X := by
      rw [hXbEqLb]; exact hmemLb
    obtain ⟨x, hxmem, hxeq⟩ := Subgroup.mem_map.mp hmemXb
    have hxG : (x : G) ∈ X := mem_subgroupOf.mp hxmem
    have hu : x * (⟨l, hlH⟩ : ↥H)⁻¹ ∈ CFSG.pPrimeCore 3 ↥H := by
      rw [← QuotientGroup.ker_mk' (N := CFSG.pPrimeCore 3 ↥H)]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxeq, mul_inv_cancel])
    have huI : (((x * (⟨l, hlH⟩ : ↥H)⁻¹ : ↥H)) : G) ∈ F09.I9 H :=
      Subgroup.mem_map.mpr ⟨x * (⟨l, hlH⟩ : ↥H)⁻¹, hu, rfl⟩
    have hux : (x * (⟨l, hlH⟩ : ↥H)⁻¹) * ⟨l, hlH⟩ = x := by group
    have h1 : (((x * (⟨l, hlH⟩ : ↥H)⁻¹ : ↥H)) : G) * l = (x : G) := by
      simpa using congrArg (Subgroup.subtype H) hux
    have hl_eq : l = (((x * (⟨l, hlH⟩ : ↥H)⁻¹ : ↥H)) : G)⁻¹ * (x : G) := by
      rw [← h1, inv_mul_cancel_left]
    rw [hl_eq]
    exact (F09.I9 H ⊔ X).mul_mem (Subgroup.mem_sup_left ((F09.I9 H).inv_mem huI))
      (Subgroup.mem_sup_right hxG)
  have hXsub : X ≤ H ⊓ D.M := le_inf hXH (hXYle.trans hYM)
  apply le_antisymm
  · calc H = F09.L9 Y H ⊔ (H ⊓ D.M) := hHsup
      _ ≤ (F09.I9 H ⊔ X) ⊔ (H ⊓ D.M) := sup_le_sup_right hLsupI _
      _ = F09.I9 H ⊔ (H ⊓ D.M) := by rw [sup_assoc, sup_eq_right.mpr hXsub]
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
