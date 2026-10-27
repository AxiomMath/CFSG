module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed-point-free quotients of odd solvable groups

Coprime fixed-point transport lifts every fixed coset for an involution to
a fixed element.  If all fixed elements already lie in the quotient kernel,
the induced quotient automorphism is fixed-point-free.
-/

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- An involution is fixed-point-free modulo `D` when `K` is odd solvable and
all of its ambient fixed points in `K` lie in `D`. -/
public theorem fixedPointFree_quotient_of_odd_solvable_and_fixedPoints_le
    {X : Type u} [Group X] [Finite X]
    (K D : Subgroup X) {t : X}
    (hDK : D ≤ K)
    (hDnormalK : (D.subgroupOf K).Normal)
    (htnormK : t ∈ Subgroup.normalizer (K : Set X))
    (htnormD : t ∈ Subgroup.normalizer (D : Set X))
    (ht : IsInvolution t)
    (hKsolv : IsSolvable K)
    (hKodd : Odd (Nat.card K))
    (hfixed : K ⊓ Subgroup.centralizer ({t} : Set X) ≤ D) :
    ∀ k : K,
      t * (k : X) * t⁻¹ * (k : X)⁻¹ ∈ D → (k : X) ∈ D := by
  classical
  let A : Subgroup X := Subgroup.zpowers t
  have hAnormK : A ≤ Subgroup.normalizer (K : Set X) :=
    Subgroup.zpowers_le.mpr htnormK
  have hAnormD : A ≤ Subgroup.normalizer (D : Set X) :=
    Subgroup.zpowers_le.mpr htnormD
  let : Subgroup.Normalizes A K := ⟨hAnormK⟩
  let DK : Subgroup K := D.subgroupOf K
  have : DK.Normal := by
    simpa [DK] using hDnormalK
  have hDKinv : IsInvariant A K DK := by
    simpa [DK] using
      (isInvariant_subgroupOf_of_le_normalizer hAnormK hAnormD hDK)
  let : MulDistribMulAction A (K ⧸ DK) :=
    quotientMulDistribMulAction (A := A) (G := K) DK hDKinv
  have hAcard : Nat.card A = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht.2 ht.1]
  have hcoprime : Nat.Coprime (Nat.card A) (Nat.card K) := by
    rw [hAcard]
    exact hKodd.coprime_two_left
  have hfixEq :
      fixedPointSubgroup A (K ⧸ DK) =
        (fixedPointSubgroup A K).map (QuotientGroup.mk' DK) := by
    simpa using
      fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
        (G := K) (A := A) hKsolv hcoprime (∅ : Set Nat.Primes)
        DK hDKinv
  let a : A := ⟨t, Subgroup.mem_zpowers t⟩
  intro k hk
  have hdiv : (a • k) / k ∈ DK := by
    change ((((a • k : K) / k : K) : X) ∈ D)
    simpa [a, div_eq_mul_inv,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      hAnormK, mul_assoc] using hk
  have hqgen :
      a • QuotientGroup.mk' DK k = QuotientGroup.mk' DK k := by
    have hmk :
        QuotientGroup.mk' DK (a • k) = QuotientGroup.mk' DK k :=
      QuotientGroup.eq_iff_div_mem.mpr hdiv
    simpa using hmk
  have hqfix :
      QuotientGroup.mk' DK k ∈ fixedPointSubgroup A (K ⧸ DK) := by
    change ∀ b : A, b • QuotientGroup.mk' DK k = QuotientGroup.mk' DK k
    intro b
    have hb : b ∈ Subgroup.zpowers a := by
      rcases Subgroup.mem_zpowers_iff.mp b.property with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa [a] using hn⟩
    exact smul_eq_self_of_mem_zpowers (y := a) hb hqgen
  have hqmap :
      QuotientGroup.mk' DK k ∈
        (fixedPointSubgroup A K).map (QuotientGroup.mk' DK) := by
    rw [← hfixEq]
    exact hqfix
  rcases Subgroup.mem_map.mp hqmap with ⟨c, hcfix, hck⟩
  have hcgen : a • c = c := hcfix a
  have hcCent : (c : X) ∈ Subgroup.centralizer ({t} : Set X) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hcconj : t * (c : X) * t⁻¹ = c := by
      simpa [a,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        hAnormK] using congrArg Subtype.val hcgen
    have h := congrArg (fun z : X => z * t) hcconj
    simpa [mul_assoc] using h.symm
  have hcD : (c : X) ∈ D := hfixed ⟨c.property, hcCent⟩
  have hcOne : QuotientGroup.mk' DK c = 1 :=
    (QuotientGroup.eq_one_iff c).mpr hcD
  have hkOne : QuotientGroup.mk' DK k = 1 := by
    calc
      QuotientGroup.mk' DK k = QuotientGroup.mk' DK c := hck.symm
      _ = 1 := hcOne
  exact (QuotientGroup.eq_one_iff k).mp hkOne

end CFSG.GorensteinWalter
