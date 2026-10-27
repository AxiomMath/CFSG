module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellN
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TrivNorm
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TrivEForm
public import CFSG.LocalAnalysis.StandardType.GGQ2S08ReflBasics

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_cellT_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) {g : G} {φ : MulAut ↥Bs}
    (hInd : GGQ2Ind Bs g φ) (hR : GGIsReflection p φ) (hM : GGQ2MovesX Bs x φ) {u : ↥Bs}
    (hu : (u : G) ∈ D) (hu1 : u ≠ 1) (htr : GGTrivialLine p B x D J u) (hφu : φ u = u) :
    GGQ2EForm Bs J φ := by
  obtain ⟨Z, hZB, hxZ, hZJ, hgZ⟩ :=
    ggQ2s08_triv_normalizes hLB hP hS hp hCav hInd hR hu hu1 htr hφu
  exact ggQ2s08_eform_of_normalized hS hp hInd hR hM hZB hxZ hZJ hgZ

theorem ggQ2s08_reflRestOut_holds (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓ : GGQ2GammaXOffI1Input) : GGQ2ReflRestOutInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hCav g φ hInd hR hM hC hcase
  obtain ⟨hEF, hnn⟩ := hcase
  obtain ⟨u, huD, hu1, hφu⟩ := ggQ2s08_exists_fixed_in_D hS hR
  by_cases hux : Subgroup.zpowers (u : G) = Subgroup.zpowers x
  · exfalso
    obtain ⟨b, hbx, hb⟩ := hM
    have hxmem : x ∈ Subgroup.zpowers (u : G) := hux ▸ Subgroup.mem_zpowers x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    have hbu : b = u ^ k := Subtype.ext (by rw [hbx, Subgroup.coe_zpow]; exact hk.symm)
    apply hb
    rw [hbu, map_zpow, hφu]
  · by_cases hnl : GGNbrLine p B x D J u
    · obtain ⟨y, K, hnb, hyu⟩ := hnl
      have hfix : ∀ c : ↥Bs, (c : G) = y → φ c = c := by
        intro c hc
        have hymem : y ∈ Subgroup.zpowers (u : G) := hyu ▸ Subgroup.mem_zpowers y
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hymem
        have hcu : c = u ^ k := Subtype.ext (by rw [hc, Subgroup.coe_zpow]; exact hk.symm)
        rw [hcu, map_zpow, hφu]
      have hor : (∃ k ∈ K, GGQ2Ind Bs k φ) ∨
          ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹ := by
        by_contra hneg
        rw [not_or] at hneg
        exact hnn ⟨y, K, hnb, hfix, hneg.1, hneg.2⟩
      exact ggQ2s08_cellN_normalizes hLB hP hΓ hS hp hI1 hCav hInd hnb hor
    · exact absurd (ggQ2s08_cellT_holds hLB hP hS hp hCav hInd hR hM huD hu1 ⟨hux, hnl⟩ hφu) hEF

end CFSG.StandardType

end
