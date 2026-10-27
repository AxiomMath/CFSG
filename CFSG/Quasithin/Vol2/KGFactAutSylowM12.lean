module

public import CFSG.Quasithin.Vol2.KGFactSporLatInputs
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import Certificates.Certificate7142
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6Cat

public section

namespace CFSG.Quasithin.H13.KGSporLat

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H.MathieuLat
open CFSG.Sporadic.Mathieu (card_M12)
open CFSG.Open (pCoreOf)

theorem m12_overgroups
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* ↥CFSG.Blueprint.NativeSporadic.M12))
    {T Y : Subgroup X} (hT : IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m12Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 :=
  Certificates.certificate7142 hX hT hTY

end CFSG.Quasithin.H13.KGSporLat

namespace CFSG.Quasithin.H13.KGAutSyl

open CFSG.QuasithinUnique CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Blueprint.NativeSporadic in
theorem factAutSylowM12_holds :
    FactAutSylowM12 := by
  intro Q _ _ hQ
  obtain ⟨e⟩ := hQ
  have : IsSimpleGroup ↥M12 := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hcard : Nat.card ↥M12 = 95040 := CFSG.Sporadic.Mathieu.card_M12
  have hf : (Nat.card ↥M12).factorization 2 = 6 := by
    rw [hcard, show (95040 : ℕ) = 2 ^ 6 * 1485 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 1485)]
    simp
  obtain ⟨hex, hZ⟩ := exists_selfNormalizing_of_rows (Q := ↥M12) KGSporLat.m12Mems
    (by rw [hf]; norm_num) (by rw [hf, hcard]; norm_num) (by rw [hf]; decide)
    (fun T Y hT hTY => KGSporLat.m12_overgroups ⟨MulEquiv.refl _⟩ hT hTY)
  exact autSylowSelfNorm_of_equiv e hZ hex
    (by rw [CFSG.ComponentClassification.M12Cover.card_outer])

end CFSG.Quasithin.H13.KGAutSyl
