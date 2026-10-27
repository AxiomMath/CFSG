module

public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.EmptyFaithful.S152WBase
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import Certificates.Certificate7143

public section

namespace CFSG.Quasithin.H13.KGSporLat

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (card_M22)
open CFSG.Open (pCoreOf)

theorem m22_overgroups
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M22))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m22Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 :=
  Certificates.certificate7143 hX hT hTY

end CFSG.Quasithin.H13.KGSporLat

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Blueprint.NativeSporadic in
theorem factAutSylowM22_holds :
    FactAutSylowM22 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  have : Finite (Carrier .M22) := Finite.of_equiv Q e.toEquiv
  have : IsSimpleGroup (Carrier .M22) := CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hcard : Nat.card (Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  have hf : (Nat.card (Carrier .M22)).factorization 2 = 7 := by
    rw [hcard, show (443520 : ℕ) = 2 ^ 7 * 3465 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3465)]
    simp
  obtain ⟨hex, hZ⟩ := exists_selfNormalizing_of_rows (Q := Carrier .M22) KGSporLat.m22Mems
    (by rw [hf]; norm_num) (by rw [hf, hcard]; norm_num) (by rw [hf]; decide)
    (fun T Y hT hTY => KGSporLat.m22_overgroups ⟨MulEquiv.refl _⟩ hT hTY)
  exact autSylowSelfNorm_of_equiv e hZ hex
    (CFSG.Quasithin.S152W.card_outer_le_two_of_card_aut hZ
      CFSG.Sporadic.Schreier.m22_mulAut_card)

end CFSG.Quasithin.H13.KGAutSyl
