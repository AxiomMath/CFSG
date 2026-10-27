module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.InvertingSelfCommutatorAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection7.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
import Mathlib.GroupTheory.FixedPointFree

namespace CFSG
end CFSG
open CFSG

/-!
# A fixed-point-free quotient action bounds the ambient commutator

Suppose an involution `t` and an operator subgroup `U` normalize `D ≤ K`.
If `t` is fixed-point-free on `K / D` and `[U, ⟨t⟩] = U`, then `U`
centralizes the quotient, so `[K, U] ≤ D`.  This is the quotient-action
bridge used in the solvable branch of Bender 1970, §2.4.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- If an involution is fixed-point-free modulo a normalized subgroup and
the operator subgroup is its own commutator with that involution, then the
ambient subgroup commutator lies in the quotient kernel. -/
public theorem commutator_le_of_selfCommutator_fixedPointFree_involution_quotient
    {G : Type u} [Group G] [Finite G]
    (K D U : Subgroup G) {t : G}
    (hDK : D ≤ K)
    (hDnormalK : (D.subgroupOf K).Normal)
    (hUnormK : U ≤ Subgroup.normalizer (K : Set G))
    (htnormK : t ∈ Subgroup.normalizer (K : Set G))
    (hUnormD : U ≤ Subgroup.normalizer (D : Set G))
    (htnormD : t ∈ Subgroup.normalizer (D : Set G))
    (ht : IsInvolution t)
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U)
    (hfixed : ∀ k : K,
      t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ D → (k : G) ∈ D) :
    ⁅K, U⁆ ≤ D := by
  classical
  let A : Subgroup G := U ⊔ Subgroup.zpowers t
  have htA : t ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hAnormK : A ≤ Subgroup.normalizer (K : Set G) := by
    exact sup_le hUnormK (Subgroup.zpowers_le.mpr htnormK)
  have hAnormD : A ≤ Subgroup.normalizer (D : Set G) := by
    exact sup_le hUnormD (Subgroup.zpowers_le.mpr htnormD)
  let : Subgroup.Normalizes A K := ⟨hAnormK⟩
  let DK : Subgroup K := D.subgroupOf K
  have : DK.Normal := by
    simpa [DK] using hDnormalK
  have hDKinv : IsInvariant A K DK := by
    simpa [DK] using
      (isInvariant_subgroupOf_of_le_normalizer hAnormK hAnormD hDK)
  let : MulDistribMulAction A (K ⧸ DK) :=
    quotientMulDistribMulAction (A := A) (G := K) DK hDKinv
  let tA : A := ⟨t, htA⟩
  let φ : MulAut (K ⧸ DK) :=
    MulDistribMulAction.toMulAut A (K ⧸ DK) tA
  have hφfp : MonoidHom.FixedPointFree φ := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro k hk
    have hqeq :
        QuotientGroup.mk' DK (tA • k) = QuotientGroup.mk' DK k := by
      simpa [φ, MulDistribMulAction.toMulAut_apply] using hk
    have hdiv : (tA • k) / k ∈ DK :=
      QuotientGroup.eq_iff_div_mem.mp hqeq
    have hamb : t * (k : G) * t⁻¹ * (k : G)⁻¹ ∈ D := by
      change ((((tA • k : K) / k : K) : G) ∈ D) at hdiv
      simpa [tA, div_eq_mul_inv,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        hAnormK, mul_assoc] using hdiv
    have hkD : (k : G) ∈ D := hfixed k hamb
    exact (QuotientGroup.eq_one_iff k).mpr hkD
  have hφinv : Function.Involutive φ := by
    intro q
    change tA • (tA • q) = q
    rw [← mul_smul]
    have htAsq : tA * tA = 1 := by
      apply Subtype.ext
      simpa [pow_two] using ht.2
    rw [htAsq, one_smul]
  let UA : Subgroup A := U.subgroupOf A
  have hzp :
      (Subgroup.zpowers t).subgroupOf A = Subgroup.zpowers tA := by
    ext x
    constructor
    · intro hx
      have hxz : (x : G) ∈ Subgroup.zpowers t := by
        simpa [Subgroup.mem_subgroupOf] using hx
      rcases Subgroup.mem_zpowers_iff.mp hxz with ⟨n, hn⟩
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
        apply Subtype.ext
        simpa [tA] using hn⟩
    · intro hx
      rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
      have hxz : (x : G) ∈ Subgroup.zpowers t := by
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by
          simpa [tA] using congrArg Subtype.val hn⟩
      simpa [Subgroup.mem_subgroupOf] using hxz
  have hUcommA : ⁅UA, Subgroup.zpowers tA⁆ = UA := by
    apply Subgroup.map_injective A.subtype_injective
    calc
      (⁅UA, Subgroup.zpowers tA⁆).map A.subtype =
          ⁅U, Subgroup.zpowers t⁆ := by
            rw [← hzp]
            simpa [UA] using
              (commutator_subgroupOf_map_eq
                (S := A) (H := Subgroup.zpowers t) (R := U)
                le_sup_right le_sup_left)
      _ = U := hUcomm
      _ = UA.map A.subtype := by
        symm
        change (U.subgroupOf A).map A.subtype = U
        exact Subgroup.map_subgroupOf_eq_of_le le_sup_left
  let : CommGroup (K ⧸ DK) :=
    hφfp.commGroupOfInvolutive hφinv
  let : MulDistribMulAction A (K ⧸ DK) :=
    quotientMulDistribMulAction (A := A) (G := K) DK hDKinv
  have hinverts : ∀ q : K ⧸ DK, tA • q = q⁻¹ := by
    intro q
    simpa [φ, MulDistribMulAction.toMulAut_apply] using
      congrFun (hφfp.coe_eq_inv_of_involutive hφinv) q
  have htriv : ∀ u : UA, ∀ q : K ⧸ DK, (u : A) • q = q :=
    selfCommutator_actsTrivially_of_inverts
      (A := A) (V := K ⧸ DK) UA tA hUcommA hinverts
  rw [Subgroup.commutator_comm, Subgroup.commutator_le]
  intro u hu k hk
  let uA : A := ⟨u, Subgroup.mem_sup_left hu⟩
  let uUA : UA := ⟨uA, hu⟩
  let kK : K := ⟨k, hk⟩
  have hqfix :
      uA • QuotientGroup.mk' DK kK = QuotientGroup.mk' DK kK := by
    simpa [uUA] using htriv uUA (QuotientGroup.mk' DK kK)
  have hqeq :
      QuotientGroup.mk' DK (uA • kK) = QuotientGroup.mk' DK kK := by
    simpa using hqfix
  have hdiv : (uA • kK) / kK ∈ DK :=
    QuotientGroup.eq_iff_div_mem.mp hqeq
  change ((((uA • kK : K) / kK : K) : G) ∈ D) at hdiv
  simpa [uA, kK, div_eq_mul_inv, commutatorElement_def,
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
    hAnormK, mul_assoc] using hdiv

end CFSG.GorensteinWalter
