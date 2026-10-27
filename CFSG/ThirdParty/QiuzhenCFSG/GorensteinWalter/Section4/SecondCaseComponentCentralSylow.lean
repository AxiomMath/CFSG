module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentA7InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentPSL2InvolutionFusion
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: a Sylow `2`-subgroup of the second-case component centralizes `t`

The selected component `E` contains a Sylow `2`-subgroup lying in
`C_G(t)`.  Any Sylow `2`-subgroup `P₀` of `E` is nontrivial, so its center
contains an involution `z`.  The landed component-fusion theorem fuses `z`
to `t` inside `E`; conjugating `P₀` by that conjugating element preserves
the Sylow property and, because `z` was central in `P₀`, makes every element
of the resulting Sylow subgroup centralize `t`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- A nontrivial Sylow `2`-subgroup has an involution in its center. -/
private lemma exists_order_two_center_of_sylow_ne_bot
    {G : Type u} [Group G] [Finite G]
    (P : Sylow 2 G) (hP : (P : Subgroup G) ≠ ⊥) :
    ∃ z : P, z ∈ Subgroup.center P ∧ orderOf z = 2 := by
  classical
  have hPnt : Nontrivial P :=
    (Subgroup.nontrivial_iff_ne_bot (P : Subgroup G)).mpr hP
  have hCentPG : IsPGroup 2 (Subgroup.center P) :=
    P.isPGroup'.to_subgroup (Subgroup.center P)
  have hCentNt : Nontrivial (Subgroup.center P) :=
    IsPGroup.center_nontrivial P.isPGroup'
  have hCard : 2 ∣ Nat.card (Subgroup.center P) := by
    obtain ⟨n, hn0, hn⟩ := (IsPGroup.nontrivial_iff_card hCentPG).mp hCentNt
    exact hn.symm ▸ dvd_pow_self 2 (ne_of_gt hn0)
  obtain ⟨zC, hzC⟩ := exists_prime_orderOf_dvd_card' 2 hCard
  have hzC' : orderOf (zC : P) = 2 := (Subgroup.orderOf_coe zC).trans hzC
  exact ⟨zC.1, zC.2, hzC'⟩

/-- In the second case, the selected component has a Sylow `2`-subgroup
contained in the centralizer of the distinguished involution `t`. -/
public theorem secondCase_componentCentralizer_contains_sylow
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    ∃ P : Sylow 2 (↥d.E),
      (P : Subgroup d.E) ≤
        (Subgroup.centralizer ({c.t} : Set G)).comap d.E.subtype := by
  classical
  have h2dvdE : 2 ∣ Nat.card (↥d.E) := by
    let tE : d.E := ⟨c.t, d.t_mem_E⟩
    have htEI : IsInvolution tE := by
      constructor
      · intro h1
        exact c.t_involution.1 (congrArg Subtype.val h1)
      · exact Subtype.ext c.t_involution.2
    have hord : orderOf tE = 2 := orderOf_eq_prime htEI.2 htEI.1
    rw [← hord]
    exact orderOf_dvd_natCard tE
  obtain ⟨P0⟩ : Nonempty (Sylow 2 (↥d.E)) := inferInstance
  have hP0ne : (P0 : Subgroup d.E) ≠ ⊥ := P0.ne_bot_of_dvd_card h2dvdE
  obtain ⟨z0, hz0cent, hz0order⟩ :=
    exists_order_two_center_of_sylow_ne_bot P0 hP0ne
  let zE : d.E := (z0 : d.E)
  let z : G := zE
  have hzorder : orderOf z = 2 := by
    calc
      orderOf z = orderOf (z0 : d.E) := by
        simp [z, zE]
      _ = orderOf z0 := by
        simp
      _ = 2 := hz0order
  have hzI : IsInvolution z := by
    exact (orderOf_eq_prime_iff.mp hzorder).symm
  have hzE : z ∈ d.E := zE.2
  obtain ⟨g, hgE, hgt⟩ := by
    cases d.model with
    | alternating e =>
        exact component_involutions_fused_of_central_quotient_aSeven
          d.E d.center_odd e d.t_mem_E c.t_involution z hzE hzI
    | projectiveSpecialLinear K hKprimePower e =>
        exact component_involutions_fused_of_central_quotient_psl2
          d.E K hKprimePower d.center_odd e d.t_mem_E c.t_involution z hzE hzI
  let gE : d.E := ⟨g, hgE⟩
  let P : Sylow 2 (↥d.E) := P0.mapSurjective
    (f := (MulAut.conj gE).toMonoidHom) (MulAut.conj gE).surjective
  refine ⟨P, ?_⟩
  intro x hx
  change x ∈ (P0 : Subgroup d.E).map (MulAut.conj gE).toMonoidHom at hx
  rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
  rw [Subgroup.mem_comap]
  rw [Subgroup.mem_centralizer_singleton_iff]
  let pP : P0 := ⟨p, hp⟩
  have hcommP : pP * z0 = z0 * pP :=
    Subgroup.mem_center_iff.mp hz0cent pP
  have hcomm : (p : G) * z = z * (p : G) := by
    simpa [pP, z, zE] using
      congrArg (fun y : P0 => (y : G)) hcommP
  calc
    ((gE * p * gE⁻¹ : d.E) : G) * c.t =
        (g * (p : G) * g⁻¹) * (g * z * g⁻¹) := by
      rw [hgt]
      simp [gE]
    _ = g * ((p : G) * z) * g⁻¹ := by
      group
    _ = g * (z * (p : G)) * g⁻¹ := by
      rw [hcomm]
    _ = (g * z * g⁻¹) * (g * (p : G) * g⁻¹) := by
      group
    _ = c.t * ((gE * p * gE⁻¹ : d.E) : G) := by
      rw [hgt]
      simp [gE]

end CFSG.GorensteinWalter
