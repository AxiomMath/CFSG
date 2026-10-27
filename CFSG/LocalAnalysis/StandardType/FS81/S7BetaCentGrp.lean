module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7RootCentQuot
import CFSG.LocalAnalysis.StandardType.FS81.S7CentralOdd
import CFSG.LocalAnalysis.StandardType.FS81.S7BetaPCore
import CFSG.LocalAnalysis.StandardType.FS81.S7BetaCentralizer

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.QuasithinUnique

instance normal_subgroupOf_zpowers_centralizer {G : Type} [Group G] (β : G) :
    ((Subgroup.zpowers β).subgroupOf (Subgroup.centralizer ({β} : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute (g : G) β := (Subgroup.mem_centralizer_iff.mp g.2 β rfl).symm
  have h2 : (g : G) * (n : G) * (g : G)⁻¹ = (n : G) := by
    rw [← hk]
    exact (hc.zpow_right k).mul_inv_cancel
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ Subgroup.zpowers β
  rw [h2, ← hk]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers β) k

theorem charTwoMod_of_betaData {G : Type} [Group G] [Finite G] {Y L A : Subgroup G}
    {b₀ β σ : G} (h : BetaData Y L A b₀ β σ)
    (hσ : σ ∈ Subgroup.centralizer ({β} : Set G)) :
    CharTwoMod (Subgroup.centralizer ({β} : Set G)) (Subgroup.zpowers β) ⟨σ, hσ⟩ := by
  have hβ : Nat.card (Subgroup.zpowers β) = 3 := by
    rw [Nat.card_zpowers, h.β_ord]
  refine charTwoMod_of_central_odd (Subgroup.centralizer ({β} : Set G)) (Subgroup.zpowers β)
    ?_ ?_ ?_ hσ h.σ_ord (pCoreOf_centralizer_inf_eq h) (centralizer_le_of_betaData h)
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Set.mem_singleton_iff] at hg; rw [hg]
  · intro n hn g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute (g : G) β := (Subgroup.mem_centralizer_iff.mp hg β rfl).symm
    exact hc.zpow_right k
  · rw [hβ]
    omega

theorem mem_sup_of_conj_of_betaData {G : Type} [Group G] {Y L : Subgroup G} {b₀ β ℓ g : G}
    (hC : Subgroup.centralizer ({b₀} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b₀ * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b₀ * g⁻¹ = y * b₀ * y⁻¹)
    (hβY : β ∈ Y) (hLY : L ≤ Y)
    (hY : ∀ y ∈ Y, y * β = β * y → y ∈ L ⊔ Subgroup.zpowers β)
    (hℓ : β * ℓ = b₀⁻¹) (hgβ : g * β = β * g)
    (hg : g * ℓ * g⁻¹ ∈ L ⊔ Subgroup.zpowers β) : g ∈ L ⊔ Subgroup.zpowers β := by
  have hsup : L ⊔ Subgroup.zpowers β ≤ Y := sup_le hLY (Subgroup.zpowers_le.mpr hβY)
  have hgY : g * ℓ * g⁻¹ ∈ Y := hsup hg
  have hc : Commute g β⁻¹ := (show Commute g β from hgβ).inv_right
  have hgβ' : g * β⁻¹ * g⁻¹ = β⁻¹ := hc.mul_inv_cancel
  have hb₀ : b₀ = ℓ⁻¹ * β⁻¹ := by
    rw [← mul_inv_rev, hℓ, inv_inv]
  have hb : g * b₀ * g⁻¹ ∈ Y := by
    have h2 : g * b₀ * g⁻¹ = (g * ℓ * g⁻¹)⁻¹ * β⁻¹ := by
      calc g * b₀ * g⁻¹ = (g * ℓ⁻¹ * g⁻¹) * (g * β⁻¹ * g⁻¹) := by rw [hb₀]; group
        _ = (g * ℓ * g⁻¹)⁻¹ * β⁻¹ := by rw [hgβ']; group
    rw [h2]
    exact Y.mul_mem (Y.inv_mem hgY) (Y.inv_mem hβY)
  have hgYY : g ∈ Y :=
    mem_of_conj_mem_of_centralizer_le hC hfus ⟨1, Y.one_mem, by simp⟩ hb
  exact hY g hgYY hgβ

end CFSG.StandardType.FrameRoute.FS81

end
