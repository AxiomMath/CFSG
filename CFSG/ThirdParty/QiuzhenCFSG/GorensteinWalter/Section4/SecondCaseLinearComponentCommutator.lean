module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearKCommutator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The component-Sylow form of source equation (1)

The generic Fact 1.5 commutator identity uses the cyclic subgroup generated
by the chosen reflection.  In the aligned linear branch, the full component
Sylow has the same commutator with `U ∩ M`: its inverted factor is normal in
`U ∩ M`, the complementary fixed factor centralizes the component Sylow, and
the two factors generate `U ∩ M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped commutatorElement

/-- In the aligned linear branch, the inverted factor is the commutator with
the full component Sylow.  The statement is algebraic so that it can be
reused by both aligned omega-data producers and the later `K₀` endpoint. -/
public theorem secondCase_linear_K_eq_componentSylow_commutator
    {G : Type u} [Group G] [Finite G]
    {X K B A : Subgroup G} {s : G}
    (hsI : IsInvolution s)
    (hXodd : Odd (Nat.card (↥X)))
    (hsX : ∀ x : G, x ∈ X → s * x * s⁻¹ ∈ X)
    (hK_inverted : (K : Set G) = invertedElements X s)
    (hsA : s ∈ A)
    (hA_normalizes_K : A ≤ Subgroup.normalizer (K : Set G))
    (hB_centralizes_A : B ≤ Subgroup.centralizer (A : Set G))
    (hdecomp : K ⊔ B = X) :
    K = ⁅A, X⁆ := by
  classical
  have hKleX : K ≤ X := by
    intro x hx
    have hxI : x ∈ invertedElements X s := by
      rw [← hK_inverted]
      exact hx
    exact hxI.1
  have hBleX : B ≤ X := by
    rw [← hdecomp]
    exact le_sup_right
  have hKnormalX : IsNormalIn K X :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := X) (s := s) hsI (Nat.coprime_two_left.mpr hXodd) hsX
      (I := K) hK_inverted).2.1
  let KX : Subgroup X := K.subgroupOf X
  let BX : Subgroup X := B.subgroupOf X
  have hKXnormal : KX.Normal := by
    rw [show KX = K.subgroupOf X by rfl,
      Subgroup.normal_subgroupOf_iff hKleX]
    intro k x hk hx
    exact hKnormalX.2 (x : G) hx (k : G) hk
  let : KX.Normal := hKXnormal
  have hsupX : KX ⊔ BX = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    have hxG : (x : G) ∈ K ⊔ B := by
      rw [hdecomp]
      exact x.2
    have hmap : (KX ⊔ BX).map X.subtype = K ⊔ B := by
      rw [Subgroup.map_sup]
      simp [KX, BX, Subgroup.map_subgroupOf_eq_of_le hKleX,
        Subgroup.map_subgroupOf_eq_of_le hBleX]
    have hxmap : (x : G) ∈ (KX ⊔ BX).map X.subtype := by
      rw [hmap]
      exact hxG
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  have hfactor : ∀ x : G, x ∈ X →
      ∃ k : G, k ∈ K ∧ ∃ b : G, b ∈ B ∧ k * b = x := by
    intro x hx
    let xX : X := ⟨x, hx⟩
    have hxSup : xX ∈ KX ⊔ BX := by
      rw [hsupX]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left (s := KX) (t := BX)).mp hxSup with
      ⟨k, hk, b, hb, hkb⟩
    refine ⟨(k : G), Subgroup.mem_subgroupOf.mp hk,
      (b : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
    exact congrArg Subtype.val hkb
  have hcomm_le : ⁅A, X⁆ ≤ K := by
    apply Subgroup.commutator_le.mpr
    intro a ha x hx
    rcases hfactor x hx with ⟨k, hk, b, hb, rfl⟩
    have hak : a * k * a⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hA_normalizes_K ha) k).1 hk
    have hba : b * a⁻¹ = a⁻¹ * b := by
      exact ((Subgroup.mem_centralizer_iff.mp (hB_centralizes_A hb)
        a⁻¹ (A.inv_mem ha))).symm
    have hcomm : ⁅a, k * b⁆ = (a * k * a⁻¹) * k⁻¹ := by
      rw [commutatorElement_def, mul_inv_rev]
      calc
        a * (k * b) * a⁻¹ * (b⁻¹ * k⁻¹) =
            a * k * (b * a⁻¹) * b⁻¹ * k⁻¹ := by group
        _ = a * k * (a⁻¹ * b) * b⁻¹ * k⁻¹ := by rw [hba]
        _ = (a * k * a⁻¹) * k⁻¹ := by group
    rw [hcomm]
    exact K.mul_mem hak (K.inv_mem hk)
  have hKzp : K = ⁅Subgroup.zpowers s, X⁆ :=
    secondCase_linear_K_eq_zpowers_commutator
      hsI (Nat.coprime_two_left.mpr hXodd) hsX hK_inverted
  apply le_antisymm
  · rw [hKzp]
    apply Subgroup.commutator_mono
    · exact Subgroup.zpowers_le.mpr hsA
    · exact le_rfl
  · exact hcomm_le

end CFSG.GorensteinWalter
