module

public import CFSG.Timmesfeld.ARS.CaseMF4Sp
public import CFSG.Timmesfeld.ARS.CaseMTwistedE6
public import CFSG.Timmesfeld.LieEmbed.CaseMInputs

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank

namespace CaseM

@[expose] def SUDictInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)) (A A₀ : Subgroup G), Sec12 R A A₀ →
    ∀ (E C : Subgroup G) (P Q : Fin 3 → Subgroup G), Sec12.IsSubframe R A A₀ E C P Q →
      ∀ (f : ℕ) (hf : 1 ≤ f)
        (Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G),
        Φ.ker ≤ Subgroup.center _ → Φ.range = levi R A A₀ →
        (∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
          ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) 6).rootGroup
            (Pi.single (2 : Fin 3) 1)) g).map Φ) →
        ∃ Φ' : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G,
          Φ'.ker ≤ Subgroup.center _ ∧ Φ'.range = levi R A A₀ ∧
          (∀ i, ((Unitary.rootDatum (card_galoisField_two_mul hf) 6).rootGroup
            (longC3 i)).map Φ' = P i) ∧
          (∀ i, ((Unitary.rootDatum (card_galoisField_two_mul hf) 6).rootGroup
            (-longC3 i)).map Φ' = Q i) ∧
          ∀ a b : Fin 3, a ≠ b → ∀ γ : Fin 3 → ℤ,
            Symplectic.toStd 3 γ = Pi.single a 1 - Pi.single b 1 →
              Commuting (((Unitary.rootDatum (card_galoisField_two_mul hf) 6).rootGroup
                γ).map Φ') E ∧
              Commuting (((Unitary.rootDatum (card_galoisField_two_mul hf) 6).rootGroup
                γ).map Φ') ⁅A₀, C⁆

end CaseM

theorem caseMFrameInput_of (hLevi : CaseMLeviInput) (hSU : CaseM.SUDictInput) :
    CaseMFrameInput := by
  intro G _ R h A hA hcoat hAne hmax A₀ hA₀ h1 hdeg
  have hS := Sec12.of_caseM h hA hcoat hAne hmax hA₀ hdeg
  have hconn := leviConnected_of_card_eq_one h hA hAne hA₀ h1
  have := h.finite
  obtain ⟨f, hf, hcard, -⟩ := hA₀.2.exists_mulEquiv_SL2' h.root hA
  refine ⟨f, hf, hcard, ?_⟩
  rcases hLevi G R A A₀ hS hconn f hf hcard with ⟨Φ, hΦ, hrange, hΔ⟩ | ⟨Φ, hker, hrange, hΔ⟩
  · obtain ⟨hF4, hN⟩ := hS.f4Frame_of_sp hf hcard Φ hΦ hrange hΔ LieEmbed.f4C3LeviInput
      LieEmbed.f4EdgeLeviInput
    exact ⟨Or.inl hF4, hN⟩
  · obtain ⟨E, C, P, Q, hfr⟩ := hS.exists_isSubframe
    obtain ⟨Φ', hker', hrange', hP, hQ, hdr⟩ := hSU G R A A₀ hS E C P Q hfr f hf Φ hker hrange hΔ
    obtain ⟨hE6, hN⟩ := hS.twistedE6Frame_of_aligned hfr hf hcard Φ' hker' hrange' hP hQ hdr
      LieEmbed.twistedE6C3LeviInput LieEmbed.twistedE6EdgeLeviInput
    exact ⟨Or.inr hE6, hN⟩

end CFSG.Timmesfeld.ARS
