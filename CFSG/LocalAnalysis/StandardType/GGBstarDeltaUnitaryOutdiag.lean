module

public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)

namespace InndiagSU

variable {K : Type} [Field K] {d n : ℕ} (h : UnitaryFieldData 2 n K)

@[expose] noncomputable def inndiagU (hd : 1 ≤ d) :
    Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) :=
  (primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)).comap
    (MulAut.congr (projEquiv h hd)).toMonoidHom

theorem mem_inndiagU {hd : 1 ≤ d}
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))} :
    φ ∈ inndiagU h hd ↔ MulAut.congr (projEquiv h hd) φ ∈
      primeFormD h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
  Iff.rfl

theorem range_conj_eq_comap_inner (hd : 1 ≤ d) :
    (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →* MulAut _).range =
      (inner (primeFormP h ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))).comap
        (MulAut.congr (projEquiv h hd)).toMonoidHom := by
  ext α
  rw [Subgroup.mem_comap, MonoidHom.mem_range]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨projEquiv h hd r, (congr_conj (projEquiv h hd) r).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨(projEquiv h hd).symm y, ?_⟩
    apply (MulAut.congr (projEquiv h hd)).injective
    rw [congr_conj, MulEquiv.apply_symm_apply]
    exact hy

theorem ggOutdiagOdd_unitary [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (p : ℕ) :
    GGOutdiagOdd p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hd1 : 1 ≤ d := by omega
  obtain ⟨-, -, -, -, -, -, -, -, hD, -, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (K := K) (n := d)) hd hq
  refine ⟨inndiagU h hd1, hD.comap _, fun φ hφ _ => congr_mem_primeFormD h hd1 hK hφ, ?_⟩
  rw [range_conj_eq_comap_inner h hd1, inndiagU, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (MulAut.congr (projEquiv h hd1)).surjective]
  have hodd : Odd (2 ^ n + 1) := by
    have : Even (2 ^ n) := (Nat.even_pow' (by have := h.one_le; omega)).mpr even_two
    exact this.add_one
  exact Odd.of_dvd_nat hodd hcard

theorem ggOutdiagPrime_unitary [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (hpd : ¬ p ∣ d) :
    GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) :=
  fun _ hφ hφp => TableBUE.mem_range_conj_of_pow_eq_one (TableBU.unitaryFieldData_of_card hK hn)
    hK hd hdq hp hpq hpd hφ hφp

end InndiagSU

end CFSG.StandardType
