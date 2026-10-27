module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Inverted elements centralize normal inverted subgroups -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Let an element `s` normalize an odd-order subgroup `U`.  If `s` inverts
both `x ∈ U` and every element of a normal subgroup `D ◁ U`, then `x`
centralizes `D`. -/
public theorem inverted_element_centralizes_normal_inverted_subgroup
    {G : Type u} [Group G] [Finite G]
    (U D : Subgroup G) (s : G)
    (hUodd : Odd (Nat.card U))
    (hsU : ∀ u : G, u ∈ U → s * u * s⁻¹ ∈ U)
    (hDnormalU : IsNormalIn D U)
    (hDinv : ∀ d : G, d ∈ D → s * d * s⁻¹ = d⁻¹)
    {x : G} (hxInv : x ∈ invertedElements U s) :
    x ∈ Subgroup.centralizer (D : Set G) := by
  classical
  have hcopU : Nat.Coprime 2 (Nat.card U) :=
    Nat.coprime_two_left.mpr hUodd
  let xU : U := ⟨x, hxInv.1⟩
  obtain ⟨zU, hzsq⟩ :=
    (sq_bijective_of_coprime_two (G := U) hcopU).2 xU
  have hzval : (zU : G) ^ 2 = x := by
    simpa using congrArg (fun z : U => (z : G)) hzsq
  have hzInv : s * (zU : G) * s⁻¹ = (zU : G)⁻¹ := by
    have hszU : s * (zU : G) * s⁻¹ ∈ U := hsU zU zU.2
    have hsqSub :
        (⟨s * (zU : G) * s⁻¹, hszU⟩ : U) ^ 2 = zU⁻¹ ^ 2 := by
      apply Subtype.ext
      change (s * (zU : G) * s⁻¹) ^ 2 = ((zU : G)⁻¹) ^ 2
      calc
        (s * (zU : G) * s⁻¹) ^ 2 =
            s * ((zU : G) ^ 2) * s⁻¹ := by
              simp only [pow_two]
              group
        _ = s * x * s⁻¹ := by rw [hzval]
        _ = x⁻¹ := hxInv.2
        _ = ((zU : G)⁻¹) ^ 2 := by rw [← hzval]; group
    exact congrArg Subtype.val
      ((sq_bijective_of_coprime_two (G := U) hcopU).1 hsqSub)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hzConjD : (zU : G) * y * (zU : G)⁻¹ ∈ D :=
    hDnormalU.2 (zU : G) zU.2 y hy
  have hconjInv := hDinv ((zU : G) * y * (zU : G)⁻¹) hzConjD
  have hyInv := hDinv y hy
  have hzInvInv : s * (zU : G)⁻¹ * s⁻¹ = (zU : G) := by
    calc
      s * (zU : G)⁻¹ * s⁻¹ =
          (s * (zU : G) * s⁻¹)⁻¹ := by group
      _ = (zU : G) := by rw [hzInv]; simp
  have hcalc :
      s * ((zU : G) * y * (zU : G)⁻¹) * s⁻¹ =
        (zU : G)⁻¹ * y⁻¹ * (zU : G) := by
    calc
      s * ((zU : G) * y * (zU : G)⁻¹) * s⁻¹ =
          (s * (zU : G) * s⁻¹) * (s * y * s⁻¹) *
            (s * (zU : G)⁻¹ * s⁻¹) := by group
      _ = (zU : G)⁻¹ * y⁻¹ * (zU : G) := by
        rw [hzInv, hyInv, hzInvInv]
  have hrelInv : (zU : G)⁻¹ * y⁻¹ * (zU : G) =
      (zU : G) * y⁻¹ * (zU : G)⁻¹ := by
    calc
      (zU : G)⁻¹ * y⁻¹ * (zU : G) =
          s * ((zU : G) * y * (zU : G)⁻¹) * s⁻¹ := hcalc.symm
      _ = ((zU : G) * y * (zU : G)⁻¹)⁻¹ := hconjInv
      _ = (zU : G) * y⁻¹ * (zU : G)⁻¹ := by group
  have hrel : (zU : G)⁻¹ * y * (zU : G) =
      (zU : G) * y * (zU : G)⁻¹ := by
    have h := congrArg (fun z : G => z⁻¹) hrelInv
    simpa [mul_assoc] using h
  have hz2cent :
      (zU : G) ^ 2 * y * ((zU : G) ^ 2)⁻¹ = y := by
    rw [pow_two]
    calc
      (zU : G) * (zU : G) * y * ((zU : G) * (zU : G))⁻¹ =
          (zU : G) * ((zU : G) * y * (zU : G)⁻¹) *
            (zU : G)⁻¹ := by group
      _ = (zU : G) * ((zU : G)⁻¹ * y * (zU : G)) *
            (zU : G)⁻¹ := by rw [← hrel]
      _ = y := by group
  rw [hzval] at hz2cent
  have hxy : x * y = y * x := by
    calc
      x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hz2cent]
  exact hxy.symm

end CFSG.GorensteinWalter
