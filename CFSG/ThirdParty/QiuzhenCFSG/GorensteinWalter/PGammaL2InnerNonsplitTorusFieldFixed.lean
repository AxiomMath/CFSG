module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldSquare
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddPowerHalfDivisor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NonsplitTorusFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2ConcreteNonsplitTorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SubgroupCardDivHalfOfIndexTwo
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Inner nonsplit-torus subgroups fixed by a field automorphism

The full fixed nonsplit-torus bound is `|R| + 1`.  Intersecting the ambient
nonsplit torus with the derived index-two `PSL₂` layer also gives the bound
`(|K| + 1) / 2`.  Since `|K| = |R| ^ p` for odd `p`, the common-divisor
calculation sharpens these to `(|R| + 1) / 2`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- A subgroup of the standard nonsplit torus that lies in the derived
`PSL₂` layer and is centralized by a pure odd-prime coefficient automorphism
has order dividing half the nonsplit-torus order over the fixed subfield. -/
public theorem pGammaL2_pureField_innerNonsplitTorus_fixedSubfield
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p)
    (lam : K)
    (hlamFixed : lam ∈ FixedPoints.subfield (Subgroup.zpowers sigma) K)
    (hlamNS : ¬ IsSquare (⟨lam, hlamFixed⟩ :
      FixedPoints.subfield (Subgroup.zpowers sigma) K))
    (A : Subgroup (PGL2 K))
    (hAtorus : A ≤ pGammaL2NonsplitTorus K lam)
    (hAinner : A ≤ commutator (PGL2 K))
    (hcomm : ∀ x : PGL2 K, x ∈ A →
      Commute (SemidirectProduct.inr sigma : PGammaL2 K)
        (SemidirectProduct.inl x)) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    Nat.card A ∣ (Nat.card R + 1) / 2 := by
  classical
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  have hlamNSK : ¬ IsSquare lam := by
    intro hlamK
    apply hlamNS
    exact (fixedSubfield_isSquare_iff K sigma p hp hpodd hord
      (⟨lam, hlamFixed⟩ : R)).mp hlamK
  have hdivR : Nat.card A ∣ Nat.card R + 1 := by
    exact pGammaL2_pureField_nonsplitTorus_fixedSubfield
      K sigma p hp hpodd hord lam hlamFixed hlamNS A hAtorus hcomm
  have hfixedData := finiteField_primeOrder_fixedSubfield_data
    K hK sigma p hp hpodd hord
  have hcardpow : Nat.card K = Nat.card R ^ p := hfixedData.2.2
  let U : Subgroup (PGL2 K) := pGammaL2NonsplitTorus K lam
  obtain ⟨_s, _w, _hUcyclic, hUcard, _hsU, _hsInv, _hwSq,
      _hwNotU, _hweyl, _hcentralizer, _hjoinCard, _hUnotPSL,
      hUnotComm⟩ :=
    pgl2_concrete_nonsplit_torus_centralizer_data K hK lam hlamNSK
  have hUeq : pgl2ConcreteNonsplitTorus K lam = U := by
    simpa [U] using
      (pgl2ConcreteNonsplitTorus_eq_pGammaL2NonsplitTorus K lam)
  let J : Subgroup (PGL2 K) := commutator (PGL2 K)
  have hJindex : J.index = 2 := by
    rw [show J =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range by
      exact pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    exact pgl2_psl2Range_index_eq_two K hK
  have hAU : A ≤ U := by
    simpa [U] using hAtorus
  have hAJ : A ≤ J := by
    simpa [J] using hAinner
  have hUnotJ : ¬ U ≤ J := by
    rw [← hUeq]
    simpa [J] using hUnotComm
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hdivKhalf : Nat.card A ∣ (Nat.card K + 1) / 2 := by
    have hdiv := subgroup_card_dvd_half_of_le_index_two
      J U A hJindex hUnotJ hAU hAJ
    have hUcard' : Nat.card U = Nat.card K + 1 := by
      rw [← hUeq]
      exact hUcard
    rw [hUcard'] at hdiv
    exact hdiv
  have hKodd : Odd (Nat.card K) := by
    rcases hK with ⟨q, n, hq, hqodd, hn, hKcard⟩
    rw [hKcard]
    exact hqodd.pow
  have hRodd : Odd (Nat.card R) := by
    apply Odd.of_dvd_nat hKodd
    rw [hcardpow]
    exact dvd_pow_self (Nat.card R) hp.ne_zero
  rw [hcardpow] at hdivKhalf
  exact dvd_add_one_half_of_dvd_odd_power_half
    (Nat.card A) (Nat.card R) p hRodd hpodd hdivR hdivKhalf

end CFSG.GorensteinWalter
