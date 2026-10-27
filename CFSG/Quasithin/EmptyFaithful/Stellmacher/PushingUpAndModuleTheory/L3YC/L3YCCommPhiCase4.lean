module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCCommPhi
public import CFSG.Quasithin.EmptyFaithful.SBd7Case3
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7

namespace Stellmacher.PU.L3YC

variable {G : Type} [Group G] [Finite G]

theorem comm_frattini_eq_CQ {G₀ R L : Subgroup G} (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) :
    ⁅c134Q G₀ L, frattiniIn (c134Q G₀ L)⁆ = c134CQ G₀ L := by
  obtain ⟨⟨n, F, iF, fF, α, hFc, hα, hE2, hZ, hCU, hnatU, hnatΦ, -, hnatQ⟩, -⟩ := h
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  obtain ⟨hC4', -⟩ := isE2_card_sq hE2
  have hQO : c134Q G₀ L ≤ pCoreOf 2 L := MS93.commutator_le_pCoreOf hLG hGL
  have hΦQ : frattiniIn (c134Q G₀ L) ≤ c134Q G₀ L := Subgroup.map_subtype_le _
  have hZQ : centerOf (c134Q G₀ L) ≤ c134Q G₀ L := inf_le_left
  have hZc : ∀ z ∈ centerOf (c134Q G₀ L), ∀ q ∈ c134Q G₀ L, z * q = q * z := fun z hz q hq =>
    (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm
  have hKdef : ∀ k ∈ c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G),
      ∀ φ ∈ frattiniIn (c134Q G₀ L), k * φ = φ * k := fun k hk φ hφ =>
    (Subgroup.mem_centralizer_iff.mp hk.2 φ hφ).symm
  have hKdef' : ∀ q ∈ c134Q G₀ L, (∀ φ ∈ frattiniIn (c134Q G₀ L), q * φ = φ * q) →
      q ∈ c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G) := fun q hq hc =>
    ⟨hq, Subgroup.mem_centralizer_iff.mpr fun φ hφ => (hc φ hφ).symm⟩
  have hQtriv : ∀ q ∈ c134Q G₀ L, ∃ l : ↥L, (l : G) = q ∧ α l = 1 := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp (hQO hq)
    refine ⟨x, hxq, ?_⟩
    have : x ∈ α.ker := by rw [hα.2]; exact hx
    exact this
  have hCL : ∀ l ∈ L, ∀ c ∈ c134CQ G₀ L, l * c * l⁻¹ = c := fun l hl c hc => by
    have := Subgroup.mem_centralizer_iff.mp hc.2 l hl
    rw [this]; group
  have hC4 : Nat.card ↥(c134CQ G₀ L) = 4 := by
    rw [hC4']; norm_num
  exact comm_frattini_eq hF α hα.1 hΦQ hZQ hZc inf_le_left hKdef hKdef' hQtriv hnatQ hnatΦ hnatU hZ
    hCU hCL hC4

end Stellmacher.PU.L3YC

end CFSG.Quasithin
