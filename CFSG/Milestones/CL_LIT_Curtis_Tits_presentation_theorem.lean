module

public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.CurtisTits.Exceptional
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.CurtisTits.Symplectic
public import CFSG.LieType.CurtisTits.Unitary

public section

universe w

namespace CFSG.Milestones

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits

theorem cl_lit_curtis_tits_presentation_theorem (t : StatedLieTag) (n p f : ℕ)
    (hadm : StatedLieAdmissible t n p f) (hrank : 3 ≤ bnRank t n) :
    CurtisTitsConclusion.{w} (lieUniversal t n p f hadm.1).D t n p f := by
  have : Fact p.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [bnRank] at hrank; omega⟩
    exact curtisTitsConclusion_specialLinear hadm hcard (by simp [bnRank] at hrank; omega)
  | PSU =>
    have e : lieUniversal .PSU n p f hadm.1 =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField p (2 * f)) p f) n,
          Unitary.rootDatum (card_galoisField_two_mul p f hf) n⟩ := by
      simp only [lieUniversal, hf, ↓reduceDIte]
    rw [e]
    exact curtisTitsConclusion_unitary hadm (card_galoisField_two_mul p f hf)
  | PSp => exact curtisTitsConclusion_symplectic hadm hcard (by simpa [bnRank] using hrank)
  | POmegaOdd => exact curtisTitsConclusion_spinOdd hadm hcard
  | POmegaPlus =>
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    have e : lieUniversal .POmegaPlus n p f hadm.1 =
        ⟨spinGroup (Spin.quadPlus n (GaloisField p f)), Spin.plusDatum n (GaloisField p f) hn⟩ := by
      simp only [lieUniversal, hn, ↓reduceDIte]
    rw [e]
    exact curtisTitsConclusion_spinPlus hadm hcard hn
  | POmegaMinus => exact curtisTitsConclusion_spinMinus (minusCoeffs_irr p f) hadm hcard
  | F4 =>
    obtain rfl : n = 0 := hadm.2.2
    exact curtisTitsConclusion_f4 p f hadm
  | E6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact curtisTitsConclusion_e6 p f hadm
  | E7 =>
    obtain rfl : n = 0 := hadm.2.2
    exact curtisTitsConclusion_e7 p f hadm
  | E8 =>
    obtain rfl : n = 0 := hadm.2.2
    exact curtisTitsConclusion_e8 p f hadm
  | twistedE6 =>
    obtain rfl : n = 0 := hadm.2.2
    exact curtisTitsConclusion_twistedE6 p f hadm
  | G2 => simp [bnRank] at hrank
  | trialityD4 => simp [bnRank] at hrank
  | twistedB2 => simp [bnRank] at hrank
  | twistedG2 => simp [bnRank] at hrank
  | twistedF4 => simp [bnRank] at hrank
  | Tits => simp [bnRank] at hrank

end CFSG.Milestones
