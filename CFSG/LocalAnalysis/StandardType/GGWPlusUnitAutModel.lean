module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdNbr
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

private theorem finite_largeEvenProj_PSU {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Finite K] (H : Subgroup (GL ι K)) : Finite (LargeEvenProj H) := by
  have : Finite H := Subtype.finite
  exact Finite.of_surjective _ (QuotientGroup.mk'_surjective _)

private theorem div_add_two_le_sub_two {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : 5 ≤ d)
    (hpd : p ∣ d) : d / p + 2 ≤ d - 2 := by
  obtain ⟨k, rfl⟩ := hpd
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hk1 : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact absurd hd (by norm_num)
  rw [Nat.mul_div_cancel_left k hp.pos]
  rcases lt_or_ge k 2 with hk2 | hk2
  · have hk : k = 1 := by omega
    subst hk
    simp at hd
    omega
  · have h4 : k + 4 ≤ p * k := by nlinarith [hp3, hk2]
    omega

theorem exists_diagModel_PSU
    {d n p : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d)
    (hperf : commutator (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊤)
    {Eb : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))}
    (hA : IsElemAbelian p Eb)
    (hI : (Eb : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))) ⊆
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n))) (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hr : p ^ (d - 2) ≤ Nat.card Eb) :
    ∃ φ : ↥(unitarySU 2 n K d) →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      UnitTB.Model φ ∧ ∀ a ∈ Eb, ∃ t : Fin d → K, ActsDiagU φ a t := by
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  by_cases h61 : (d, n) = (6, 1)
  · have hdn : d = 6 ∧ n = 1 := by simpa [Prod.mk.injEq] using h61
    obtain ⟨rfl, rfl⟩ := hdn
    have hp3 : p = 3 := by
      have h3 : p ∣ 3 := by simpa using hpq
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst hp3
    haveI : Finite (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
      finite_largeEvenProj_PSU (LargeEvenSUGroup (Fin 6) K (2 ^ 1))
    let ψ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →*
        LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) := MonoidHom.id _
    have hψ : Function.Surjective ψ := fun x => ⟨x, rfl⟩
    have hkerbot : ψ.ker = ⊥ := by rw [MonoidHom.ker_id]
    have hker : ψ.ker ≤ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
      rw [hkerbot]; exact bot_le
    have hAI : ∀ a ∈ Eb, ∃ x ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)), ∀ l, x (ψ l) = ψ (a l) :=
      fun a ha => ⟨a, hI ha, fun _ => rfl⟩
    have hcard : 3 ^ 4 ≤ Nat.card Eb := by simpa using hr
    have hodd : Odd (Nat.card ψ.ker) := by
      rw [hkerbot, Subgroup.card_bot]; decide
    exact USixTwo.exists_diagModel_odd hK hψ hker hperf hodd hA hAI hcard
  · haveI : Finite (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) :=
      finite_largeEvenProj_PSU (LargeEvenSUGroup (Fin d) K (2 ^ n))
    let ψ : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
        LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) := MonoidHom.id _
    have hψ : Function.Surjective ψ := fun x => ⟨x, rfl⟩
    have hker : ψ.ker ≤ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
      rw [MonoidHom.ker_id]; exact bot_le
    have hAI : ∀ a ∈ Eb, ∃ x ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n)), ∀ l, x (ψ l) = ψ (a l) :=
      fun a ha => ⟨a, hI ha, fun _ => rfl⟩
    have hcard : p ^ (d / p + 2) ≤ Nat.card Eb :=
      le_trans (Nat.pow_le_pow_right hp.pos (div_add_two_le_sub_two hp hp2 hd hpd)) hr
    obtain ⟨φ, hφs, hφker, hdiag⟩ :=
      LineU.exists_diagModel hK hn hd hp hpq hpd
        (LineU.unitaryUniversalCover_holds n d K hK hd h61) hψ hker hperf hA hAI hcard
    exact ⟨φ, ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩, hdiag⟩

end CFSG.StandardType
