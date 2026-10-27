module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup

theorem ggL48TB0Rk_pow_five_le_card_of_inn
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hmark : GGInnerDiagOnLab (fun p lab => GGL48TB0TwRow p lab ∧ GGL48TB0Rank lab = 5) p Bs L) :
    p ^ 5 ≤ Nat.card Bs := by
  have hp : p.Prime := hS.1.1.1.2.2.2.2.2.1.1
  refine Line63.H5.ggUnitDvd63BstarRankInput_holds G p B Bs x L D J hS.1.1 ?_
  refine largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ?_) hmark
  obtain ⟨⟨hrow, hrk⟩, hrest⟩ := hP
  have hp2 : p ≠ 2 := hS.1.1.1.2.2.2.2.2.1.2.1
  have hE : lab.tag ≠ .twE6 := by
    intro h
    simp [GGL48TB0Rank, h] at hrk
  rcases hrow with ⟨htag, hdr, hdq⟩ | ⟨htag, -, -⟩
  · have hr : lab.rank = 5 := by simpa [GGL48TB0Rank, hE] using hrk
    have h6 : p ∣ 2 * 3 := by simpa [hr] using hdr
    have h3 : p = 3 := by
      rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    exact ⟨⟨⟨htag, by omega, hdq, hdr⟩, hr, h3⟩, hrest⟩
  · exact absurd htag hE

theorem ggL48TB0TwConfigInputInn_of_rest
    (h : GGL48TB0TwConfigInputRest) : GGL48TB0TwConfigInputInn := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hJD r hr hmark
  by_cases h5 : r = 5
  · subst h5
    exact ggL48TB0Rk_pow_five_le_card_of_inn hS hmark
  · exact h G p B Bs x L D J X B₂ d y K U U₁ hS hJD r (by omega) hmark

end CFSG.StandardType

end
