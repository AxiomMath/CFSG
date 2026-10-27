module

public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu
public import Certificates.Certificate7141

public section

namespace CFSG.Quasithin.H13.KGSporLat

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Open (pCoreOf)

theorem m11_overgroups
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M11))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m11Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 :=
  Certificates.certificate7141 hX hT hTY

end CFSG.Quasithin.H13.KGSporLat

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Blueprint.NativeSporadic in
theorem factAutSylowM11_holds :
    FactAutSylowM11 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  have : Finite (Carrier .M11) := Finite.of_equiv Q e.toEquiv
  have : IsSimpleGroup (Carrier .M11) := CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  have hcard : Nat.card (Carrier .M11) = 7920 := CFSG.Sporadic.Mathieu.card_M11
  have hf : (Nat.card (Carrier .M11)).factorization 2 = 4 := by
    rw [hcard, show (7920 : ℕ) = 2 ^ 4 * 495 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 495)]
    simp
  obtain ⟨hex, hZ⟩ := exists_selfNormalizing_of_rows (Q := Carrier .M11) KGSporLat.m11Mems
    (by rw [hf]; norm_num) (by rw [hf, hcard]; norm_num) (by rw [hf]; decide)
    (fun T Y hT hTY => KGSporLat.m11_overgroups ⟨MulEquiv.refl _⟩ hT hTY)
  exact autSylowSelfNorm_of_equiv e hZ hex
    (card_outer_le_two_of_inner CFSG.QuasithinUnique.Ch1.m11_all_inner)

end CFSG.Quasithin.H13.KGAutSyl
