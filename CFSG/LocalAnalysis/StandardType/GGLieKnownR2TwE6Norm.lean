module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NThmA
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NPanel
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NTor

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem twE6_normalizer_le_normalizer_rad
    (f : ℕ) (hf : 2 ≤ f) :
    Subgroup.normalizer
        (((twistedE6Datum 2 f).rootGroup twE6Alpha : Subgroup (twistedE6Group 2 f)) :
          Set (twistedE6Group 2 f)) ≤
      Subgroup.normalizer ((twE6Rad (frobQ 2 f) : Subgroup (twistedE6Group 2 f)) :
        Set (twistedE6Group 2 f)) := by
  exact twE6_normalizer_alpha_le (frobQ 2 f) (frobQ_frobQ 2 f (by omega))

theorem twE6_pCoreOf_normalizer_le_rad
    (f : ℕ) (hf : 2 ≤ f) :
    pCoreOf 2 (Subgroup.normalizer
        (((twistedE6Datum 2 f).rootGroup twE6Alpha : Subgroup (twistedE6Group 2 f)) :
          Set (twistedE6Group 2 f))) ≤ twE6Rad (frobQ 2 f) := by
  classical
  haveI : Fintype (GaloisField 2 (2 * f)) := Fintype.ofFinite _
  have hk : 4 ≤ Fintype.card (GaloisField 2 (2 * f)) := by
    have h := GaloisField.card 2 (2 * f) (by omega)
    rw [Nat.card_eq_fintype_card] at h
    rw [h]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := by
        exact pow_le_pow_right' (show (1 : ℕ) ≤ 2 by norm_num) (by omega)
  have hcu : 1 < Fintype.card (GaloisField 2 (2 * f))ˣ := by
    rw [Fintype.card_units]
    omega
  obtain ⟨t, ht1⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := (GaloisField 2 (2 * f))ˣ) hcu 1
  have ht : (t : GaloisField 2 (2 * f)) ^ 2 ≠ 1 := by
    intro hsq
    have h1 : (t : GaloisField 2 (2 * f)) = 1 := by
      rcases (sq_eq_one_iff (R := GaloisField 2 (2 * f))).1 hsq with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    exact ht1 (Units.ext h1)
  exact (twE6_pCoreOf_normalizer_alpha_eq (frobQ 2 f) (frobQ_frobQ 2 f (by omega))
    (torusRegularAlpha3 (frobQ 2 f) (frobQ_frobQ 2 f (by omega)) (t := t) ht)).le

end CFSG.StandardType.LieKnownR2.Short
