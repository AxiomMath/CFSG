module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseInvolutionDecomposition
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: inverted elements lie in the selected component

This is the reusable public form of the component-membership step used while
lifting the reflected torus.  Modulo the normal component `E`, conjugation by
the chosen involution is trivial; inversion then gives an element of order at
most two in the odd quotient, so the quotient image vanishes.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem secondCase_odd_order_of_mem_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : ∀ x : G, x ∈ c.U → Odd (orderOf x) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, hxy⟩
  have hdvd : orderOf y ∣ Nat.card (pPrimeCore 2 c.H) :=
    Subgroup.orderOf_dvd_natCard (pPrimeCore 2 c.H) hy
  have hoddcard : Odd (Nat.card (pPrimeCore 2 c.H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := c.H))
  have hoddY : Odd (orderOf y) := Odd.of_dvd_nat hoddcard hdvd
  have hordEq : orderOf (c.H.subtype y) = orderOf y :=
    orderOf_injective c.H.subtype c.H.subtype_injective y
  rw [← hxy, hordEq]
  exact hoddY

/-- Every element of `U ∩ M` inverted by the selected involution in `E` lies
in `E`. -/
public theorem secondCase_invertedElements_le_component
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMcent : ((SM : Subgroup w.M).map w.M.subtype) ≤
      Subgroup.centralizer ({c.t} : Set G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    {s : d.E} (hsSE : s ∈ (SE : Subgroup d.E))
    {y : G} (hyU : y ∈ c.U) (hyM : y ∈ w.M)
    (hyinv : (s : G) * y * (s : G)⁻¹ = y⁻¹) :
    y ∈ d.E := by
  classical
  let sG : G := s
  have hsmap : sG ∈ (SE : Subgroup d.E).map d.E.subtype :=
    Subgroup.mem_map.mpr ⟨s, hsSE, rfl⟩
  have hsSM : sG ∈ ((SM : Subgroup w.M).map w.M.subtype) := by
    rw [hSEamb] at hsmap
    exact hsmap.1
  have hsM : sG ∈ w.M :=
    (Subgroup.map_subtype_le (SM : Subgroup w.M)) hsSM
  let Esub : Subgroup (↥w.M) := d.E.subgroupOf w.M
  have hEsubNormal : Esub.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := w.M) (N := d.E)
      (le_normalizer_of_isNormalIn d.E_normal)
  let : Esub.Normal := hEsubNormal
  let p : w.M →* w.M ⧸ Esub := QuotientGroup.mk' Esub
  let yM : w.M := ⟨y, hyM⟩
  let sM : w.M := ⟨sG, hsM⟩
  have hconjM : sM * yM * sM⁻¹ = yM⁻¹ := by
    apply Subtype.ext
    change sG * y * sG⁻¹ = y⁻¹
    exact hyinv
  have hsq : (p yM) ^ 2 = 1 := by
    have hp1 : p (sM * yM * sM⁻¹) = p yM := by
      calc
        p (sM * yM * sM⁻¹) = p sM * p yM * (p sM)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        _ = 1 * p yM * 1 := by
          have hs1 : p sM = 1 := by
            apply (QuotientGroup.eq_one_iff (N := Esub) sM).mpr
            exact Subgroup.mem_subgroupOf.mpr (s : d.E).2
          rw [hs1, one_mul, inv_one, mul_one]
        _ = p yM := by simp
    have hp2 : p (sM * yM * sM⁻¹) = (p yM)⁻¹ := by
      simpa using congrArg p hconjM
    have h : p yM = (p yM)⁻¹ := hp1.symm.trans hp2
    rw [pow_two]
    calc
      p yM * p yM = (p yM)⁻¹ * p yM :=
        congrArg (fun z => z * p yM) h
      _ = 1 := by simp
  have hordY : Odd (orderOf y) :=
    secondCase_odd_order_of_mem_U c y hyU
  have hordYdiv : orderOf (p yM) ∣ orderOf y := by
    have h1 : orderOf (p yM) ∣ orderOf yM := orderOf_map_dvd p yM
    have h2 : orderOf yM = orderOf y :=
      (orderOf_injective w.M.subtype w.M.subtype_injective yM).symm
    rwa [h2] at h1
  have hordOdd : Odd (orderOf (p yM)) := Odd.of_dvd_nat hordY hordYdiv
  have hp1' : p yM = 1 := by
    have hdvd2 : orderOf (p yM) ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := p yM) (n := 2)).2 hsq
    have hcop : Nat.Coprime 2 (orderOf y) :=
      Nat.coprime_two_left.mpr hordY
    have hdvd1 : orderOf (p yM) ∣ 1 := by
      simpa [hcop.gcd_eq_one] using (Nat.dvd_gcd hdvd2 hordYdiv)
    exact (orderOf_eq_one_iff (x := p yM)).1 (Nat.dvd_one.mp hdvd1)
  have hyEsub : yM ∈ Esub :=
    (QuotientGroup.eq_one_iff (N := Esub) yM).mp hp1'
  exact Subgroup.mem_subgroupOf.mp hyEsub

end CFSG.GorensteinWalter
