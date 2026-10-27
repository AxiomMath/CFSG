module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.Dich
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22sn
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20m

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem barImage_normal_of_calC {L L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L) (h₂ : L₂ ∈ calC L)
    (hsup : L = L₁ ⊔ L₂) : (barImage L L₁).Normal := by
  have hle : L₁ ≤ L := h₁.1.le
  have hN : (L₁.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
      (P22s.le_normalizer_of_mem_calC h₁ h₂ hsup)
  exact Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)

theorem barImage_sup_eq_top {L L₁ L₂ : Subgroup G} (hsup : L = L₁ ⊔ L₂) :
    barImage L L₁ ⊔ barImage L L₂ = ⊤ := by
  have h1 : L₁ ≤ L := hsup ▸ le_sup_left
  have h2 : L₂ ≤ L := hsup ▸ le_sup_right
  rw [barImage, barImage, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup h1 h2, hsup,
    Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem barImage_perfect {L L₁ : Subgroup G} (h₁ : L₁ ∈ calC L) :
    ⁅barImage L L₁, barImage L L₁⁆ = barImage L L₁ := by
  have hle : L₁ ≤ L := h₁.1.le
  have hA : ⁅L₁.subgroupOf L, L₁.subgroupOf L⁆ = L₁.subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle, h₁.2.1]
  rw [barImage, ← Subgroup.map_commutator, hA]

private theorem isComponent_barImage {L L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L)
    (h₂ : L₂ ∈ calC L) (hsup : L = L₁ ⊔ L₂) : CFSG.IsComponent (barImage L L₁) := by
  refine ⟨?_, (barImage_normal_of_calC h₁ h₂ hsup).isSubnormal⟩
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv h₁.1.le h₁.1
  exact CFSG.IsQuasisimple.of_mulEquiv e.symm
    (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr h₁.2.2)

private theorem le_of_barImage_eq {L L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L)
    (h₂ : L₂ ∈ calC L) (hsup : L = L₁ ⊔ L₂) (h : barImage L L₁ = barImage L L₂) :
    L₁ ≤ L₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hPn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  set π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hL : L ≤ normalizer (L₂ : Set G) :=
    P22s.le_normalizer_of_mem_calC h₂ h₁ (by rw [hsup, sup_comm])
  have hOn : CFSG.Open.pCoreOf 2 L ≤ normalizer (L₂ : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hL
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  refine uc22p20m_le_of_perfect_sup (X := L₁) (N := L₂) (O := CFSG.Open.pCoreOf 2 L)
    h₁.2.1 ?_ hOn hO2
  intro l hl
  have hmem : π ⟨l, h₁.1.le hl⟩ ∈ barImage L L₁ :=
    ⟨⟨l, h₁.1.le hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
  rw [h] at hmem
  rw [barImage] at hmem
  obtain ⟨y, hy, hyπ⟩ := hmem
  obtain ⟨z, hz, hzy⟩ := (QuotientGroup.mk'_eq_mk' (N := CFSG.pCore 2 ↥L)).1 hyπ
  have hzy' : (y : G) * (z : G) = l := by
    have := congrArg (fun w : ↥L => (w : G)) hzy
    simpa using this
  rw [← hzy']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hy) ⟨z, hz, rfl⟩

theorem barImage_commutator_eq_bot {L L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ calC L) (h₂ : L₂ ∈ calC L)
    (hsup : L = L₁ ⊔ L₂) (hne : L₁ ≠ L₂) : ⁅barImage L L₁, barImage L L₂⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_barImage h₁ h₂ hsup)
    (isComponent_barImage h₂ h₁ (by rw [hsup, sup_comm])) with heq | hbot
  · exfalso
    have h12 : L₁ ≤ L₂ := le_of_barImage_eq h₁ h₂ hsup heq
    have h21 : L₂ ≤ L₁ := le_of_barImage_eq h₂ h₁ (by rw [hsup, sup_comm]) heq.symm
    exact hne (le_antisymm h12 h21)
  · exact hbot

theorem rankOneOver_barImage {L L₁ : Subgroup G} (h₁ : L₁ ∈ calC L)
    (h : RankOneOver (Bar2 L₁)) : RankOneOver ↥(barImage L L₁) := by
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv h₁.1.le h₁.1
  exact RankOneOver.of_mulEquiv e h

end CFSG.LocalAnalysis.UniquenessCase.UC22.RankOneBorel
