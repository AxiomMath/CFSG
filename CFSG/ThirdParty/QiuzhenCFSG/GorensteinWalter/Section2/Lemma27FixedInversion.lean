module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# A Klein-four fixed involution on an inverted odd subgroup

If an odd normal subgroup `A` of `M` is inverted by an involution `t`, and
`t` lies in a Klein-four subgroup `V` of `M`, then `V` acts faithfully on
`A`.  The Klein-four fixed-point lemma supplies a nonidentity `s ∈ V` with
nontrivial fixed part on `A`; since `t` itself has trivial fixed part on
`A`, this `s` is an involution of `C_M(t)` with a nontrivial fixed subgroup
of `A`.  This is the fixed-point ingredient of the final
`[S,U] ≰ F(U)` step of Lemma 2.7.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- An odd normal subgroup inverted by a Klein-four involution admits another
involution in the Klein four with nontrivial fixed part. -/
public theorem exists_fixed_involution_centralizer_of_kleinFour_inverted
    {G : Type u} [Group G] [Finite G]
    (M A V : Subgroup G) (t : G)
    (hV : IsKleinFour V) (hVleM : V ≤ M)
    (htV : t ∈ V)
    (hAne : A ≠ ⊥) (hAodd : Nat.Coprime 2 (Nat.card (↥A)))
    (hAnorm : IsNormalIn A M)
    (hAinvt : ∀ x : G, x ∈ A → t * x * t⁻¹ = x⁻¹) :
    ∃ t' : G,
      t' ∈ M ∧ t' ∈ Subgroup.centralizer ({t} : Set G) ∧ t' ∈ V ∧
        t' ≠ 1 ∧ t' ≠ t ∧ A ⊓ Subgroup.centralizer ({t'} : Set G) ≠ ⊥ := by
  classical
  have hVA : V ≤ Subgroup.normalizer (A : Set G) := by
    intro v hv
    exact (le_normalizer_of_isNormalIn hAnorm) (hVleM hv)
  have hfaith : A ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxA : x ∈ A := hx.1
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := hx.2
    have htcomm : x * t = t * x := by
      exact ((Subgroup.mem_centralizer_iff (g := x) (s := (V : Set G))).1
        hxV t htV).symm
    have htinvt : t * x * t⁻¹ = x⁻¹ := hAinvt x hxA
    have htinvt' : t * x * t⁻¹ = x := by
      calc
        t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [htcomm]
        _ = x * (t * t⁻¹) := by rw [mul_assoc]
        _ = x := by simp
    have hxinv : x = x⁻¹ := by
      calc
        x = t * x * t⁻¹ := htinvt'.symm
        _ = x⁻¹ := htinvt
    have hx2 : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := by rw [pow_two]
        _ = x * x⁻¹ := by nth_rw 2 [hxinv]
        _ = 1 := mul_inv_cancel x
    have hxone : x = 1 := by
      have hx1 : (⟨x, hxA⟩ : ↥A) ^ 2 = 1 := by
        apply Subtype.ext
        exact hx2
      have hone := eq_one_of_sq_eq_one_of_coprime_two (G := ↥A) hAodd hx1
      exact congrArg Subtype.val hone
    exact hxone
  rcases exists_ne_one_fixedPoints_of_kleinFour_action
      (G := G) (V := V) (A := A) hV hVA hAodd hAne hfaith with
    ⟨s, hsV, hsne, hsA⟩
  have hsne_t : s ≠ t := by
    intro hst
    have hCt_bot : A ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxA : x ∈ A := hx.1
      have hxCent : x ∈ Subgroup.centralizer ({t} : Set G) := hx.2
      have htcomm : x * t = t * x :=
        (Subgroup.mem_centralizer_iff.mp hxCent t (by simp)).symm
      have htinvt : t * x * t⁻¹ = x⁻¹ := hAinvt x hxA
      have htinvt' : t * x * t⁻¹ = x := by
        calc
          t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [htcomm]
          _ = x * (t * t⁻¹) := by rw [mul_assoc]
          _ = x := by simp
      have hxinv : x = x⁻¹ := by
        calc
          x = t * x * t⁻¹ := htinvt'.symm
          _ = x⁻¹ := htinvt
      have hx2 : x ^ 2 = 1 := by
        calc
          x ^ 2 = x * x := by rw [pow_two]
          _ = x * x⁻¹ := by nth_rw 2 [hxinv]
          _ = 1 := mul_inv_cancel x
      have hx1 : (⟨x, hxA⟩ : ↥A) ^ 2 = 1 := by
        apply Subtype.ext
        exact hx2
      have hone := eq_one_of_sq_eq_one_of_coprime_two (G := ↥A) hAodd hx1
      exact congrArg Subtype.val hone
    have hsA_t : A ⊓ Subgroup.centralizer ({t} : Set G) ≠ ⊥ := by
      simpa [hst] using hsA
    exact hsA_t hCt_bot
  refine ⟨s, hVleM hsV, ?_, hsV, hsne, hsne_t, hsA⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]
  have hscomm : s * t = t * s := by
    let : IsKleinFour (↥V) := hV
    let : IsMulCommutative (↥V) := IsKleinFour.isMulCommutative
    let sv : ↥V := ⟨s, hsV⟩
    let tv : ↥V := ⟨t, htV⟩
    have h := congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := ↥V)).comm sv tv)
    exact h
  exact hscomm.symm

end CFSG.GorensteinWalter
