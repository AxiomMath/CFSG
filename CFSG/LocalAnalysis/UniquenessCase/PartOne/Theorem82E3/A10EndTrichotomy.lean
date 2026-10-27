module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDichotomy
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem le_M_of_two_altOff (F : A10Frame c) {H : Subgroup G}
    (hH : CFSG.Open.IsTwoLocal H) {a b : G} (haA : a ∈ F.A) (hbA : b ∈ F.A)
    (ha3 : F.deg (Subgroup.zpowers a) = 3) (hb3 : F.deg (Subgroup.zpowers b) = 3)
    (haltA : A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
      ((H ⊓ D.M).subgroupOf D.M).map F.phiA)
    (haltB : A10Perm.altOff (F.phiA ⟨b, F.A_le_M hbA⟩).support ≤
      ((H ⊓ D.M).subgroupOf D.M).map F.phiA)
    (hba : b ∉ Subgroup.zpowers a) : H ≤ D.M := by
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have hbL : b ∈ c.L := F.P_le_L (F.A_le hbA)
  have hφa_at : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  have hφb_at : F.phiA ⟨b, F.A_le_M hbA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr hbA)
  have hsuppa : (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 3 := by
    rw [← F.deg_zpowers_eq haL, ha3]
  have hsuppb : (F.phiA ⟨b, F.A_le_M hbA⟩).support.card = 3 := by
    rw [← F.deg_zpowers_eq hbL, hb3]
  have hsuppne : (F.phiA ⟨a, F.A_le_M haA⟩).support ≠
      (F.phiA ⟨b, F.A_le_M hbA⟩).support := by
    intro heq
    have hmem : F.phiA ⟨b, F.A_le_M hbA⟩ ∈
        Subgroup.zpowers (F.phiA ⟨a, F.A_le_M haA⟩) :=
      A10Perm.mem_zpowers_of_support_eq hφa_at hφb_at hsuppa heq.symm
    exact hba (mem_zpowers_of_phiA_mem_zpowers F haA hbA hmem)
  obtain ⟨E, hE_le, hE5, hEnc⟩ :=
    A10Perm.exists_noncyclic_five hφa_at hφb_at hsuppa hsuppb hsuppne
  have hE : E ≤ ((H ⊓ D.M).subgroupOf D.M).map F.phiA :=
    le_trans hE_le (sup_le haltA haltB)
  exact c.u2 5 (by rw [F.sig]; simp) H hH
    (two_le_pRank_inf_of_noncyclic_five F hE5 hEnc hE)

theorem trichotomy (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H) (hAH : F.A ≤ H) :
    (∀ a ∈ F.A, a ≠ 1 → ∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
        F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
        W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G))) ∨
      H ≤ D.M ∨
      (CFSG.ABGLocalTools.IsSylowOf 3 F.A H ∧
        ∃ (a : G) (haA : a ∈ F.A), F.deg (Subgroup.zpowers a) = 3 ∧
          H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M ∧
          A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
            ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA ∧
          (∀ h ∈ H, h * a * h⁻¹ ∈ F.A → h * a * h⁻¹ ∈ Subgroup.zpowers a) ∧
          ∀ b ∈ F.A, b ∉ Subgroup.zpowers a →
            ∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({b} : Set G) →
              F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
              W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({b} : Set G))) := by
  classical
  by_cases hM : H ≤ D.M
  · exact Or.inr (Or.inl hM)
  by_cases h1 : (∀ a ∈ F.A, a ≠ 1 → ∀ W : Subgroup G,
      W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
      F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
      W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G)))
  · exact Or.inl h1
  push Not at h1
  obtain ⟨a, haA, ha1, W, hW_le, hW_norm, hW_cop, hW_core⟩ := h1
  have ha_data : F.deg (Subgroup.zpowers a) = 3 ∧
      H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M ∧
      A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
        ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA := by
    rcases dichotomy_centralizer F hF hC hAH haA ha1 with hcore | hdata
    · exact absurd (hcore W hW_le hW_norm hW_cop) hW_core
    · exact hdata
  obtain ⟨ha3, hXM, haltA⟩ := ha_data
  by_cases hwc : ∀ h ∈ H, h * a * h⁻¹ ∈ F.A → h * a * h⁻¹ ∈ Subgroup.zpowers a
  · refine Or.inr (Or.inr ⟨isSylowOf_A_of_weaklyClosed F hF hAH haA ha3 hwc,
      a, haA, ha3, hXM, haltA, hwc, ?_⟩)
    intro b hbA hbza
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hbza (Subgroup.one_mem _)
    rcases dichotomy_centralizer F hF hC hAH hbA hb1 with hb_core | ⟨hb3, hbM, hbalt⟩
    · exact hb_core
    · refine absurd (le_M_of_two_altOff F hH haA hbA ha3 hb3 ?_ ?_ hbza) hM
      · exact haltA.trans (Subgroup.map_mono (f := F.phiA)
          (Subgroup.subgroupOf_mono D.M (le_inf inf_le_left hXM)))
      · exact hbalt.trans (Subgroup.map_mono (f := F.phiA)
          (Subgroup.subgroupOf_mono D.M (le_inf inf_le_left hbM)))
  · push Not at hwc
    obtain ⟨h, hhH, hhA, hhza⟩ := hwc
    exact Or.inr (Or.inl
      (le_M_of_not_weaklyClosed F hF hH hAH haA ha3 haltA hhH hhA hhza))

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
