module

public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue
public import CFSG.LocalAnalysis.StandardType.GGQTwoCor123

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_cellN_normalizes (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓ : GGQ2GammaXOffI1Input)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hI1 : ¬ GGQTwoI1 Bs D J)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (h : (∃ k ∈ K, GGQ2Ind Bs k φ) ∨
      ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧ k * x * k⁻¹ = g * x * g⁻¹) :
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hHyp := hS.1
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hKG0 : K ≤ ggG0 p B x L D J := le_ggG0_of_ggNbr hnb
  rcases h with ⟨k, hk, hkInd⟩ | ⟨k, hk, hkN, hkx⟩
  · have hkG : k ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
      Subgroup.le_normalizer (hKG0 hk)
    have hN : k⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hkInd.1) hInd.1
    have hcent : k⁻¹ * g ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hInd.2 ⟨b, hb⟩
      have h2 := hkInd.2 ⟨b, hb⟩
      have h3 : g * b * g⁻¹ = k * b * k⁻¹ := h1.symm.trans h2
      calc b * (k⁻¹ * g) = k⁻¹ * (k * b * k⁻¹) * g := by group
        _ = k⁻¹ * (g * b * g⁻¹) * g := by rw [h3]
        _ = (k⁻¹ * g) * b := by group
    have hD : k⁻¹ * g ∈ Subgroup.normalizer (D : Set G) :=
      (Subgroup.centralizer_le_normalizer (D : Set G)) (Subgroup.centralizer_le hDBs hcent)
    have hh := ggQ2n_normalizer_inf_le hLB hP hHyp hp hCav ⟨hN, hD⟩
    have hgk : g = k * (k⁻¹ * g) := by group
    rw [hgk]
    exact Subgroup.mul_mem _ hkG hh
  · have hkG : k ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
      Subgroup.le_normalizer (hKG0 hk)
    have hN : k⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hkN) hInd.1
    have hfix : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ ∈ Subgroup.zpowers x := by
      have : (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = x := by
        calc (k⁻¹ * g) * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k := by group
          _ = x := by rw [← hkx]; group
      rw [this]
      exact Subgroup.mem_zpowers x
    have hh := hΓ hS hp hI1 hCav (k⁻¹ * g) hN hfix
    have hgk : g = k * (k⁻¹ * g) := by group
    rw [hgk]
    exact Subgroup.mul_mem _ hkG hh

end CFSG.StandardType

end
