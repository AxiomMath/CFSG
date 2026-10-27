module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IDefs
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.CurtisTits.Adjoint
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.CurtisTits.TwistedE6
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

theorem rckK1I_ggU_perfect
    {t : StatedLieTag} {n f : ℕ} (ht : GGPosTag t) (hadm : StatedLieAdmissible t n 2 f) :
    commutator (ggU t n f).K = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    by_cases h2 : n = 2
    · subst h2
      have hne : 2 ^ f ≠ 2 := fun h => hadm.2.2.2.1 (by rw [h])
      have hf2 : 2 ≤ f := by
        have hf1 : f ≠ 1 := fun hf1 => hne (by rw [hf1]; norm_num)
        omega
      have h4pow : 4 ≤ 2 ^ f := by
        have h := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mpr hf2
        norm_num at h
        exact h
      have hcard : 4 ≤ Nat.card (GaloisField 2 f) := by
        rw [GaloisField.card 2 f (by omega)]
        exact h4pow
      exact (CFSG.ClassicalInvolution.sl2_isPerfect hcard).commutator_eq_top
    · have hn1 : 1 ≤ n := by have := hadm.2.2.1; omega
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hm : 2 ≤ m := by
        have hle := hadm.2.2.1
        have hne : m + 1 ≠ 2 := h2
        omega
      exact (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m (GaloisField 2 f) hm).1.commutator_eq_top
  ·
    have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
      card_galoisField_two_mul 2 f hf
    have hn : 3 ≤ n := hadm.2.2.1
    have hnq : (n, 2 ^ f) ≠ (3, 2) := hadm.2.2.2
    have hSU := (CFSG.LieType.Universal.Unitary.isQuasisimple_SU
      (F := GaloisField 2 (2 * f)) (p := 2) (f := f) (n := n)
      hF hn hnq).1.commutator_eq_top
    change commutator (lieUniversal .PSU n 2 f Nat.prime_two).K = ⊤
    have e : lieUniversal .PSU n 2 f Nat.prime_two =
        ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [lieUniversal, hf, ↓reduceDIte]
    rw [e]
    exact hSU
  ·
    have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    exact (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible n (GaloisField 2 f)
      hadm hcard).1.commutator_eq_top
  ·
    have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have hn : 3 ≤ n := by have := hadm.2.2; omega
    have hCT := CFSG.LieType.CurtisTits.curtisTitsConclusion_spinPlus.{0} hadm hcard hn
    change commutator (lieUniversal .POmegaPlus n 2 f Nat.prime_two).K = ⊤
    have e : lieUniversal .POmegaPlus n 2 f Nat.prime_two =
        ⟨spinGroup (Spin.quadPlus n (GaloisField 2 f)),
          Spin.plusDatum n (GaloisField 2 f) hn⟩ := by
      simp only [lieUniversal, hn, ↓reduceDIte]
    rw [e]
    exact hCT.1.2.1.1.commutator_eq_top
  ·
    have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    exact (CFSG.LieType.CurtisTits.curtisTitsConclusion_spinMinus.{0}
      (minusCoeffs_irr 2 f) hadm hcard).1.2.1.1.commutator_eq_top
  ·
    obtain rfl : n = 0 := hadm.2.2
    exact (CFSG.LieType.CurtisTits.curtisTitsConclusion_f4.{0} 2 f hadm).1.2.1.1.commutator_eq_top
  ·
    obtain rfl : n = 0 := hadm.2.2
    exact (CFSG.LieType.CurtisTits.isQuasisimple_e6 (GaloisField 2 f)).1.commutator_eq_top
  ·
    obtain rfl : n = 0 := hadm.2.2
    exact (CFSG.LieType.CurtisTits.isQuasisimple_e7 (GaloisField 2 f)).1.commutator_eq_top
  ·
    obtain rfl : n = 0 := hadm.2.2
    exact (CFSG.LieType.CurtisTits.curtisTitsConclusion_e8.{0} 2 f hadm).1.2.1.1.commutator_eq_top
  ·
    obtain rfl : n = 0 := hadm.2.2
    exact (CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hadm.2.1).1.commutator_eq_top

end CFSG.StandardType.RCKK1I
