module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingFusion
public import CFSG.RankThree.PartOne.SEITZRF.Defs
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers

public section

namespace CFSG.RankThree.PartOne.SEITZRF

open CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem centralizer_le_of_conj {R : Subgroup G} {s x r : G} (hr : r ∈ R)
    (hrx : r * x * r⁻¹ = s) (hs : Subgroup.centralizer {s} ≤ R) :
    Subgroup.centralizer {x} ≤ R := by
  intro c hc
  have hc' : r * c * r⁻¹ ∈ Subgroup.centralizer {s} := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [← hrx, show r * c * r⁻¹ * (r * x * r⁻¹) = r * (c * x) * r⁻¹ by group,
      show r * x * r⁻¹ * (r * c * r⁻¹) = r * (x * c) * r⁻¹ by group]
    rw [hc]
  have h := R.mul_mem (R.mul_mem (R.inv_mem hr) (hs hc')) hr
  simpa [mul_assoc] using h

theorem exists_conj_mem_of_conj {R : Subgroup G} {z t : G}
    (hzt : ∀ g : G, g * z * g⁻¹ ≠ t)
    (hfus : ∀ x ∈ R, orderOf x = 2 → ∃ r ∈ R, r * x * r⁻¹ = z ∨ r * x * r⁻¹ = t)
    {x y g : G} (hx : x ∈ R) (hy : y ∈ R) (hx2 : orderOf x = 2) (hgy : g * x * g⁻¹ = y) :
    ∃ r ∈ R, r * x * r⁻¹ = y := by
  have hy2 : orderOf y = 2 := by
    rw [← hgy, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx2
  obtain ⟨r₁, hr₁, h₁⟩ := hfus x hx hx2
  obtain ⟨r₂, hr₂, h₂⟩ := hfus y hy hy2
  have hconj : (r₂ * g * r₁⁻¹) * (r₁ * x * r₁⁻¹) * (r₂ * g * r₁⁻¹)⁻¹ = r₂ * y * r₂⁻¹ := by
    rw [← hgy]
    group
  have hsame : r₁ * x * r₁⁻¹ = r₂ * y * r₂⁻¹ := by
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · rw [h₁, h₂]
    · exact absurd (by rw [← h₁, ← h₂]; exact hconj) (hzt (r₂ * g * r₁⁻¹))
    · refine absurd ?_ (hzt (r₂ * g * r₁⁻¹)⁻¹)
      rw [← h₁, ← h₂, ← hconj]
      group
    · rw [h₁, h₂]
  refine ⟨r₂⁻¹ * r₁, R.mul_mem (R.inv_mem hr₂) hr₁, ?_⟩
  calc r₂⁻¹ * r₁ * x * (r₂⁻¹ * r₁)⁻¹ = r₂⁻¹ * (r₁ * x * r₁⁻¹) * r₂ := by group
    _ = r₂⁻¹ * (r₂ * y * r₂⁻¹) * r₂ := by rw [hsame]
    _ = y := by group

theorem isStronglyEmbedded_of_two_classes [Finite G] {R : Subgroup G} (hRG : R ≠ ⊤) {z t : G}
    (hz : z ∈ R) (hz2 : orderOf z = 2) (hzt : ∀ g : G, g * z * g⁻¹ ≠ t)
    (hfus : ∀ x ∈ R, orderOf x = 2 → ∃ r ∈ R, r * x * r⁻¹ = z ∨ r * x * r⁻¹ = t)
    (hcz : Subgroup.centralizer {z} ≤ R) (hct : Subgroup.centralizer {t} ≤ R) :
    CFSG.DisconnectedInvolutionGraph.Helpers.IsStronglyEmbedded R := by
  classical
  refine ⟨hRG, ?_, fun g hg => ?_⟩
  · have h := Subgroup.orderOf_dvd_natCard R hz
    rw [hz2] at h
    exact even_iff_two_dvd.2 h
  · apply Nat.not_even_iff_odd.1
    intro heven
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup R g)) 2
      (even_iff_two_dvd.1 heven)
    have hx2 : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have hxR : (x : G) ∈ R := x.2.1
    have hxg : g⁻¹ * (x : G) * g ∈ R := by
      have h := x.2.2
      simpa [CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup, MulAut.conj_apply] using h
    obtain ⟨r, hr, hrx⟩ := exists_conj_mem_of_conj hzt hfus hxR hxg hx2 (g := g⁻¹)
      (by group)
    obtain ⟨r₀, hr₀, h₀⟩ := hfus _ hxR hx2
    have hcx : Subgroup.centralizer {(x : G)} ≤ R := by
      rcases h₀ with h₀ | h₀
      · exact centralizer_le_of_conj hr₀ h₀ hcz
      · exact centralizer_le_of_conj hr₀ h₀ hct
    have hc : g * r ∈ Subgroup.centralizer {(x : G)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : r * (x : G) * r⁻¹ = g⁻¹ * x * g := hrx
      have e2 : (x : G) * (g * r) = g * r * x := by
        calc (x : G) * (g * r) = g * (g⁻¹ * x * g) * r := by group
          _ = g * (r * x * r⁻¹) * r := by rw [e]
          _ = g * r * x := by group
      first | exact e2 | exact e2.symm
    have := R.mul_mem (hcx hc) (R.inv_mem hr)
    exact hg (by simpa using this)

theorem false_of_two_involution_classes [Finite G] {R : Subgroup G} (hRG : R ≠ ⊤) {z t : G}
    (hz : z ∈ R) (hz2 : orderOf z = 2) (ht2 : orderOf t = 2)
    (hzt : ∀ g : G, g * z * g⁻¹ ≠ t)
    (hfus : ∀ x ∈ R, orderOf x = 2 → ∃ r ∈ R, r * x * r⁻¹ = z ∨ r * x * r⁻¹ = t)
    (hcz : Subgroup.centralizer {z} ≤ R) (hct : Subgroup.centralizer {t} ≤ R) : False := by
  have hse := isStronglyEmbedded_of_two_classes hRG hz hz2 hzt hfus hcz hct
  obtain ⟨g, hg⟩ := stronglyEmbedded_all_involutions_conjugate R hse ⟨z, hz2⟩ ⟨t, ht2⟩
  exact hzt g (congrArg Subtype.val hg)

section Centralizers

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem inf_centralizer_centralZ_le_Rf (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {H : Subgroup (ModGL F4.tag K)} (hHΓ : H ≤ F4.reeGamma K a)
    (hRH : Rf K a β ≤ H) (hY2 : Y2 K a hK H ≤ Rf K a β)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) :
    H ⊓ Subgroup.centralizer {centralZ K a 1} ≤ Rf K a β := by
  rintro x ⟨hxH, hxc⟩
  have hxΓ : x ∈ F4.reeGamma K a ⊓ Subgroup.centralizer {centralZ K a 1} := ⟨hHΓ hxH, hxc⟩
  rw [(large_Ree_two_involution_centralizers a ha K hK).1] at hxΓ
  have hmem : x ∈ ((F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ⊔
      rankOneGroupTwo K a : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := hxΓ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rankOneGroupTwo_le_normalizer K a hK)]
    at hmem
  obtain ⟨v, hv, r, hr, rfl⟩ := hmem
  have hrR : r ∈ Rf K a β := hY2 ⟨hr, v, hv, hxH⟩
  have hvH : v ∈ H := by
    have := H.mul_mem hxH (H.inv_mem (hRH hrR))
    simpa using this
  exact (Rf K a β).mul_mem (hU ⟨hvH, reeFixedOrbitComplementUnipotent_le _ hv⟩) hrR

theorem inf_centralizer_sylowL_le_Rf (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (β : K ≃+* K) {H : Subgroup (ModGL F4.tag K)} (hHΓ : H ≤ F4.reeGamma K a)
    (hRH : Rf K a β ≤ H) (hY1 : Y1 K a hK H ≤ Rf K a β)
    (hU : H ⊓ F4.reeFixedPosUnipotent K a ≤ Rf K a β) :
    H ⊓ Subgroup.centralizer {sylowL a K 1} ≤ Rf K a β := by
  rintro x ⟨hxH, hxc⟩
  have hxΓ : x ∈ F4.reeGamma K a ⊓ Subgroup.centralizer {sylowL a K 1} := ⟨hHΓ hxH, hxc⟩
  rw [(large_Ree_two_involution_centralizers a ha K hK).2.2.2.2.2.1] at hxΓ
  have hmem : x ∈ ((tKernel K a ⊔ rankOneGroupOne K a : Subgroup (ModGL F4.tag K)) :
      Set (ModGL F4.tag K)) := hxΓ
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (rankOneGroupOne_le_normalizer_tKernel hK)]
    at hmem
  obtain ⟨v, hv, r, hr, rfl⟩ := hmem
  have hv1 : v ∈ F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ := hv.1
  have hrR : r ∈ Rf K a β := hY1 ⟨hr, v, hv1, hxH⟩
  have hvH : v ∈ H := by
    have := H.mul_mem hxH (H.inv_mem (hRH hrR))
    simpa using this
  exact (Rf K a β).mul_mem (hU ⟨hvH, reeFixedOrbitComplementUnipotent_le _ hv1⟩) hrR

end Centralizers

end CFSG.RankThree.PartOne.SEITZRF
