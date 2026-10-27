module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSL
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFacts
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneRestCX

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggIsPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} {y : G} (hy : y ^ p = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  intro g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm,
    zpow_mul, zpow_natCast, hy, one_zpow]

section Tags

@[expose] def GGLayerPDivTag (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G)
    (G₀ : Subgroup G), GGPresentsG0 G₀ (ggU t n f).D t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) →
    ∀ y : G, y ^ p = 1 → y ∈ Subgroup.normalizer (G₀ : Set G) →
      GGPsiInnerDiag (ggU t n f).D ψ y →
      ∀ K : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {y}) → p ∣ Nat.card K

theorem ggLayerPDivInput_of_tags (h : ∀ t, GGLayerPDivTag t) : GGLayerPDivInput := by
  intro G _ _ t n f ψ G₀ hpres p hp hp2 hpq y hy hN hdiag K hK
  exact h t G n f ψ G₀ hpres p hp hp2 hpq y hy hN hdiag K hK

theorem ggLayerPDivTag_PSL : GGLayerPDivTag .PSL := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [← hrange, ← ggCentralizer_zpowers_eq] at hK
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin (m + 1)) (GaloisField 2 f),
      (y⁻¹, A) ∈ LinFusion.ggInducedPairs ψ :=
    LinFusion.exists_mem_ggInducedPairs (y := y⁻¹) hrk ψ hker (by rwa [inv_inv])
  have hA' : (y, A⁻¹) ∈ LinFusion.ggInducedPairs ψ := by
    have h := (LinFusion.ggInducedPairs ψ).inv_mem hA
    rwa [Prod.inv_mk, inv_inv] at h
  have hEA : ∀ e ∈ Subgroup.zpowers y, ∃ B, (e, B) ∈ LinFusion.ggInducedPairs ψ := by
    intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    have h := (LinFusion.ggInducedPairs ψ).zpow_mem hA' k
    have e : ((y, A⁻¹) : G × GL (Fin (m + 1)) (GaloisField 2 f)) ^ k = (y ^ k, A⁻¹ ^ k) :=
      rfl
    exact ⟨A⁻¹ ^ k, e ▸ h⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact LayerPDiv.dvd_card_of_isComponentOf_sl (F := GaloisField 2 f) hker hp hp2
    (by rw [hF]; exact LayerPDiv.dvd_sq_sub_one hpq) (ggIsPGroup_zpowers_of_pow_eq_one hy) hEA hK

theorem ggLayerPDivTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGLayerPDivTag t := by
  intro G _ _ n f ψ G₀ hpres
  have hrk := hpres.1.2
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd hrk (show ¬ 2 ≤ 0 by omega)

theorem ggLayerPDivTag_POmegaOdd : GGLayerPDivTag .POmegaOdd :=
  fun _ _ _ _ _ _ _ hpres => absurd rfl hpres.1.1.2.2.2

theorem ggLayerPDivInput_of_remaining (hPSU : GGLayerPDivTag .PSU) (hPSp : GGLayerPDivTag .PSp)
    (hPlus : GGLayerPDivTag .POmegaPlus) (hMinus : GGLayerPDivTag .POmegaMinus)
    (hF4 : GGLayerPDivTag .F4) (hE6 : GGLayerPDivTag .E6) (hE7 : GGLayerPDivTag .E7)
    (hE8 : GGLayerPDivTag .E8) (hTwE6 : GGLayerPDivTag .twistedE6) : GGLayerPDivInput := by
  refine ggLayerPDivInput_of_tags fun t => ?_
  cases t with
  | PSL => exact ggLayerPDivTag_PSL
  | PSU => exact hPSU
  | PSp => exact hPSp
  | POmegaOdd => exact ggLayerPDivTag_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact hMinus
  | F4 => exact hF4
  | E6 => exact hE6
  | E7 => exact hE7
  | E8 => exact hE8
  | twistedE6 => exact hTwE6
  | G2 => exact ggLayerPDivTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggLayerPDivTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggLayerPDivTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 => exact ggLayerPDivTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggLayerPDivTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggLayerPDivTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem ggSixLayerCXInput_of_pDivTags (hPSU : GGLayerPDivTag .PSU) (hPSp : GGLayerPDivTag .PSp)
    (hPlus : GGLayerPDivTag .POmegaPlus) (hMinus : GGLayerPDivTag .POmegaMinus)
    (hF4 : GGLayerPDivTag .F4) (hE6 : GGLayerPDivTag .E6) (hE7 : GGLayerPDivTag .E7)
    (hE8 : GGLayerPDivTag .E8) (hTwE6 : GGLayerPDivTag .twistedE6)
    (hNS : GGSixLayerCXNonsplitInput) : GGSixLayerCXInput :=
  ggSixLayerCXInput_of_split
    (ggLayerPDivInput_of_remaining hPSU hPSp hPlus hMinus hF4 hE6 hE7 hE8 hTwE6) hNS

end Tags

end CFSG.StandardType
