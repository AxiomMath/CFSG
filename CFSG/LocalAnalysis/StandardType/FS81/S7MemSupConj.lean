module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "sθ" => rootThree Tag.E8 (GaloisField 2 1) (highRoot Tag.E8)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "Dθ" => EPilot.perpLevi Tag.E8 (GaloisField 2 1)

private theorem mem_of_conj_mem_of_centralizer_le_aux {G : Type} [Group G] {Y : Subgroup G}
    {b z g : G} (hC : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    (hz : ∃ y ∈ Y, z = y * b * y⁻¹) (hg : g * z * g⁻¹ ∈ Y) : g ∈ Y := by
  obtain ⟨y, hy, rfl⟩ := hz
  have h1 : (g * y) * b * (g * y)⁻¹ ∈ Y := by
    have h : (g * y) * b * (g * y)⁻¹ = g * (y * b * y⁻¹) * g⁻¹ := by group
    rw [h]
    exact hg
  obtain ⟨y₁, hy₁, h2⟩ := hfus (g * y) h1
  have h3 : y₁⁻¹ * (g * y) ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (y₁⁻¹ * (g * y)) = y₁⁻¹ * (y₁ * h * y₁⁻¹) * (g * y) := by group
      _ = y₁⁻¹ * ((g * y) * h * (g * y)⁻¹) * (g * y) := by rw [h2]
      _ = (y₁⁻¹ * (g * y)) * h := by group
  have h4 : y₁ * (y₁⁻¹ * (g * y)) * y⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem hy₁ (hC h3)) (Y.inv_mem hy)
  simpa using h4

section E7Model


theorem mem_sup_of_conj_mem_embedding {G : Type} [Group G] {Y : Subgroup G} {b : G}
    (ι : adjointGroup .E8 GF₂ →* G) (hι : Function.Injective ι) (hrange : ι.range = Y)
    (hb : ι sθ = b) (hCb : Subgroup.centralizer ({b} : Set G) ≤ Y)
    (hfus : ∀ g : G, g * b * g⁻¹ ∈ Y → ∃ y ∈ Y, g * b * g⁻¹ = y * b * y⁻¹)
    {z : ↥(adjointGroup .E7 (ZMod 2))} (hz : ∃ m : ↥(adjointGroup .E8 GF₂), m * e7Incl z * m⁻¹ = sθ)
    {g : G} (hg : g ∈ Subgroup.centralizer ({ι tθ} : Set G))
    (hgz : g * ι (e7Incl z) * g⁻¹ ∈ (Dθ).map ι ⊔ (Qθ).map ι) : g ∈ (Dθ).map ι ⊔ (Qθ).map ι := by
  obtain ⟨m, hm⟩ := hz
  have hz' : ∃ y ∈ Y, ι (e7Incl z) = y * b * y⁻¹ := by
    refine ⟨ι m⁻¹, ?_, ?_⟩
    · rw [← hrange]
      exact ⟨m⁻¹, rfl⟩
    · have hconj : ι (e7Incl z) = ι m⁻¹ * b * (ι m⁻¹)⁻¹ := by
        have hz'' : e7Incl z = m⁻¹ * sθ * m := by
          calc e7Incl z = m⁻¹ * (m * e7Incl z * m⁻¹) * m := by group
            _ = m⁻¹ * sθ * m := by rw [hm]
        rw [hz'']
        simp only [map_mul, map_inv, hb]
        group
      exact hconj
  have hDY : (Dθ).map ι ≤ Y := by
    rw [← hrange]
    exact Subgroup.map_le_range ι Dθ
  have hQY : (Qθ).map ι ≤ Y := by
    rw [← hrange]
    exact Subgroup.map_le_range ι Qθ
  have hsupY : (Dθ).map ι ⊔ (Qθ).map ι ≤ Y := sup_le hDY hQY
  have hgY : g ∈ Y :=
    mem_of_conj_mem_of_centralizer_le_aux hCb hfus hz' (hsupY hgz)
  have hgmap : g ∈ (Subgroup.centralizer ({tθ} : Set ↥(adjointGroup .E8 GF₂))).map ι := by
    rw [← centralizer_singleton_inf_range_eq_map ι hι tθ]
    exact ⟨hg, by rw [hrange]; exact hgY⟩
  rw [(centralizer_pinnedElt_highRoot_E8 (K := GF₂)).1, Subgroup.map_sup] at hgmap
  simpa [sup_comm] using hgmap

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
