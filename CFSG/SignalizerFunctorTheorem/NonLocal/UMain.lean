module

public import Mathlib
public import CFSG.SignalizerFunctorTheorem.NonLocal.UData
public import CFSG.SignalizerFunctorTheorem.NonLocal.LinearMain
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical
  CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {ℓ f e n : ℕ} {K : Type} [Field K]

theorem nonLocalized_unitarySubfield_of_system (h : UnitaryFieldData ℓ f K) {k : Subfield K}
    (h₀ : UnitaryFieldData ℓ e k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (hn : 3 ≤ n)
    (hq₀ : ¬(n = 3 ∧ ℓ ^ e = 2)) (hsys : UnitaryHeisenbergSystem h₀ n) :
    NonLocalized (subfieldPSU h h₀ hbar n).range := by
  classical
  have : Finite K := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hn1 : 1 ≤ n := by omega
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let P := unitaryProjData h n hn1
  let φH := subfieldSU h h₀ hbar n
  have hrange : (P.π.comp φH).range = (subfieldPSU h h₀ hbar n).range := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨(g : primeFormP h₀ ((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)), rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨g, rfl⟩
  have hsimple : IsSimpleGroup (P.π.comp φH).range := by
    rw [hrange]
    have := isSimpleGroup_primeFormP_one h₀ hn hq₀
    exact (MonoidHom.ofInjective (subfieldPSU_injective h h₀ hbar n hn1)).symm.isSimpleGroup
  rw [← hrange]
  obtain ⟨A, Z, ι', y, hAfin, hι'fin, hAcomm, hArp, hZA, hcard, hcomm, hnt, hdist⟩ := hsys
  have := hAfin
  have := hι'fin
  refine P.nonLocalized_of_heisenberg φH
    (fun W hW => unitary_irreducible h h₀ hbar hn W hW) hsimple
    (fun x hx => unitary_centralizer_eq_one h h₀ hbar hn hq₀ x hx) A Z hAcomm hArp hZA y hcomm
    ?_ hdist ?_
  · obtain ⟨z, hz, hz1⟩ := hnt
    refine ⟨z, hz, fun hπ => hz1 ?_⟩
    have h1 : φH z ∈
        normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n :=
      (QuotientGroup.eq_one_iff _).mp hπ
    rwa [← comap_subfieldSU_normOneScalars h h₀ hbar n hn1]
  · intro s hs hsr V hV0 hVcomm hVexp hVnorm hfaith hlow hup
    have : Fact s.Prime := ⟨hs⟩
    have : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      Finite.of_surjective P.π P.hπ
    have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hVcomm _ a.2 _ b.2)⟩⟩
    have hVp : IsPGroup s V := by
      refine IsPGroup.iff_orderOf.mpr (fun g => ?_)
      have h1 : orderOf g ∣ s := orderOf_dvd_of_pow_eq_one (Subtype.ext (hVexp g g.2))
      rcases (Nat.dvd_prime hs).mp h1 with h | h
      · exact ⟨0, by simpa using h⟩
      · exact ⟨1, by simpa using h⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hVp
    have hq0 : 2 ≤ ℓ ^ e := h₀.one_lt_pow
    have hLm : (ℓ ^ e) ^ (n - 2) ≤ m := by
      rw [hcard, pow_mul, hm] at hlow
      exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hlow
    have hq2 : ℓ ^ e = 2 → s ≠ 2 := by
      intro h2 hs2
      have := (Nat.Prime.pow_eq_iff Nat.prime_two).mp h2
      exact hsr (hs2.trans this.1.symm)
    have hfin : n = 3 ∧ ℓ ^ e = 2 ∧ m = 2 := by
      rcases hup with h | ⟨e', he, hdvd, hle⟩
      · rw [hm, Fintype.card_fin] at h
        exact linear_numerics (j := 0) hn hq0 hs.two_le hq2 rfl hLm
          (Or.inl ((Nat.pow_le_pow_iff_right hs.one_lt).mp h))
      · rw [hm] at hdvd hle
        obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hs).mp hdvd
        rw [Fintype.card_fin] at he
        have hmj : m ≤ 2 * j := by
          rw [← pow_mul, mul_comm] at hle
          exact (Nat.pow_le_pow_iff_right hs.one_lt).mp hle
        exact linear_numerics hn hq0 hs.two_le hq2 rfl hLm (Or.inr ⟨he, hmj⟩)
    exact hq₀ ⟨hfin.1, hfin.2.1⟩

end CFSG.SignalizerFunctorTheorem.NonLocal
