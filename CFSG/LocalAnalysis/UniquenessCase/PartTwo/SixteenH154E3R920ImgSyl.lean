module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XPropDImg
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92b
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (xbar9 wbar9)

variable {G : Type} [Group G] [Finite G]

theorem isL2_bar2_xbar9 {Y H L : Subgroup G} {m : ℕ} (hY : Opp 3 Y = L) (hLH : L ≤ H)
    (hL2 : IsL2 (Bar2 L) m) : IsL2 (Bar2 (xbar9 Y H)) m := by
  subst hY
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono fun _ hy => F09.opp_le_L9 Y H hy
  have key : IsL2 (Bar2 ((F09.img9 H (Opp 3 Y)).subgroupOf (F09.img9 H (F09.L9 Y H)))) m :=
    CFSG.Blueprint.LieModel.of_mulEquiv
      (UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hle)).symm (isL2_bar2_img9 hLH hL2)
  exact key

theorem isSylowOf_two_img9_subgroupOf {Y H S : Subgroup G} (hYH : Y ≤ H)
    (hSH : CFSG.ABGLocalTools.IsSylowOf 2 S H) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((F09.img9 H S).subgroupOf (F09.img9 H (F09.L9 Y H))) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
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
  haveI hLbNormal : (F09.img9 H (F09.L9 Y H)).Normal := F09.img9_L9_normal hYH
  have hP : CFSG.ABGLocalTools.IsSylowOf 2
      (F09.img9 H S ⊓ F09.img9 H (F09.L9 Y H)) (F09.img9 H (F09.L9 Y H)) :=
    hSbSyl.inf_of_le_normalizer le_top
      (Subgroup.le_normalizer_of_normal (H := F09.img9 H (F09.L9 Y H)))
  have h1 : CFSG.ABGLocalTools.IsSylowOf 2
      ((F09.img9 H S ⊓ F09.img9 H (F09.L9 Y H)).subgroupOf (F09.img9 H (F09.L9 Y H)))
      ((F09.img9 H (F09.L9 Y H)).subgroupOf (F09.img9 H (F09.L9 Y H))) := by
    obtain ⟨hle, hPp, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨fun _ hx => hle hx, hPp.comap_subtype, ?_⟩
    rwa [Subgroup.relIndex_subgroupOf le_rfl]
  simpa using h1

theorem L9_le_sup_of_wbar9_eq_top (D : Data G) {Y H : Subgroup G} (hYH : Y ≤ H)
    (hW : wbar9 D Y H = ⊤) : F09.L9 Y H ≤ F09.I9 H ⊔ (H ⊓ D.M) := by
  have hle : F09.img9 H (F09.L9 Y H) ≤ F09.img9 H (H ⊓ D.M) := by
    have hW' := hW
    rw [wbar9] at hW'
    exact Subgroup.subgroupOf_eq_top.mp hW'
  have hLH : F09.L9 Y H ≤ H :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.L9_le_of_le hYH
  intro l hl
  have hlH : l ∈ H := hLH hl
  have hxmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) (⟨l, hlH⟩ : ↥H) ∈
      F09.img9 H (H ⊓ D.M) :=
    hle (Subgroup.mem_map.mpr ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩)
  obtain ⟨mH, hmH, hmx⟩ := Subgroup.mem_map.mp hxmem
  have hmG : (mH : G) ∈ H ⊓ D.M := Subgroup.mem_subgroupOf.mp hmH
  have hker : mH⁻¹ * (⟨l, hlH⟩ : ↥H) ∈ CFSG.pPrimeCore 3 ↥H := by
    rw [← QuotientGroup.ker_mk' (N := CFSG.pPrimeCore 3 ↥H)]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hmx, inv_mul_cancel])
  have hI : ((mH⁻¹ * (⟨l, hlH⟩ : ↥H) : ↥H) : G) ∈ F09.I9 H :=
    Subgroup.mem_map.mpr ⟨mH⁻¹ * (⟨l, hlH⟩ : ↥H), hker, rfl⟩
  have hprod : (mH : G) * ((mH⁻¹ * (⟨l, hlH⟩ : ↥H) : ↥H) : G) = l := by
    have h1 : mH * (mH⁻¹ * (⟨l, hlH⟩ : ↥H)) = (⟨l, hlH⟩ : ↥H) := by group
    simpa using congrArg (Subgroup.subtype H) h1
  rw [← hprod]
  exact (F09.I9 H ⊔ (H ⊓ D.M)).mul_mem (Subgroup.mem_sup_right hmG) (Subgroup.mem_sup_left hI)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
