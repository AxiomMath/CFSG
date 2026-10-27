module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2AlignedSylowEscape
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2NormalizerSylowNoncyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# An outer involution in the aligned ambient Sylow

The aligned Sylow subgroup of `M` is a subgroup of the fixed dihedral Sylow
of `G`.  The PSL₂ component forces that Sylow subgroup to be noncyclic.  If
it is not contained in the component, a reflection outside the component is
obtained by multiplying an escaping element by a component reflection when
necessary.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Failure of component containment produces an involution in the aligned
ambient Sylow, outside the selected component and centralizing `t`. -/
public theorem secondCase_psl2_aligned_outer_involution
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤ (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (F : Subgroup G)
    (hF_eq : F = c.FU ⊓ Subgroup.centralizer
      (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G))
    (hNF : Subgroup.normalizer (F : Set G) = w.M)
    (hSnotE : ¬ (c.S : Subgroup G) ≤ d.E) :
    ∃ r : w.M, r ∈ (SM : Subgroup w.M) ∧
      IsInvolution (r : G) ∧ (r : G) ∉ d.E ∧
        Commute c.t (r : G) := by
  classical
  let A : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  let I : Subgroup G := (c.S : Subgroup G) ⊓ w.M
  let IM : Subgroup w.M := I.subgroupOf w.M
  have hIMp : IsPGroup 2 IM := by
    have hIp : IsPGroup 2 I := c.S.isPGroup'.to_inf_left
    exact hIp.comap_subtype
  have hSMleIM : (SM : Subgroup w.M) ≤ IM := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact ⟨hSMleS (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hIMeq : IM = (SM : Subgroup w.M) := SM.is_maximal' hIMp hSMleIM
  have hAeqI : A = I := by
    apply le_antisymm
    · exact le_inf hSMleS (Subgroup.map_subtype_le (SM : Subgroup w.M))
    · intro x hx
      let xM : w.M := ⟨x, hx.2⟩
      have hxIM : xM ∈ IM := Subgroup.mem_subgroupOf.mpr hx
      rw [hIMeq] at hxIM
      exact Subgroup.mem_map.mpr ⟨xM, hxIM, rfl⟩
  have hInotE : ¬ I ≤ d.E :=
    secondCase_psl2_aligned_sylow_intersection_escape c w d SM hSMleS SE
      hSEamb F hF_eq hNF hSnotE
  have hAnotE : ¬ A ≤ d.E := by simpa [hAeqI] using hInotE
  obtain ⟨x, hxA, hxE⟩ := SetLike.not_le_iff_exists.mp hAnotE
  have hAnc : ¬ IsCyclic A := by
    intro hAcyc
    let eSM : (SM : Subgroup w.M) ≃* A :=
      Subgroup.equivMapOfInjective (SM : Subgroup w.M)
        w.M.subtype w.M.subtype_injective
    have hSMcyc : IsCyclic SM := (MulEquiv.isCyclic eSM).mpr hAcyc
    exact (secondCase_psl2_sylow_not_cyclic_of_component_le c w d K hK e
      w.M d.E_component.1 SM) hSMcyc
  have hAnotS0 : ¬ A ≤ c.S0 := by
    intro hAle
    let : IsCyclic c.S0 := c.S0_cyclic
    exact hAnc (Subgroup.isCyclic_of_le hAle)
  obtain ⟨s, hsA, hsS0⟩ := SetLike.not_le_iff_exists.mp hAnotS0
  have hAleS : A ≤ (c.S : Subgroup G) := hSMleS
  have hAleM : A ≤ w.M := Subgroup.map_subtype_le (SM : Subgroup w.M)
  have memSM_of_mem_A {z : G} (hz : z ∈ A) :
      (⟨z, hAleM hz⟩ : w.M) ∈ (SM : Subgroup w.M) := by
    rcases Subgroup.mem_map.mp hz with ⟨zM, hzM, hzval⟩
    have heq : (⟨z, hAleM hz⟩ : w.M) = zM := Subtype.ext hzval.symm
    rw [heq]
    exact hzM
  have commute_t_of_mem_S {r : G} (hrS : r ∈ (c.S : Subgroup G)) :
      Commute c.t r := by
    have hrH : r ∈ c.H := centralizerSetup_S_le_H c hrS
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff] at hrH
    exact hrH c.t (by simp)
  by_cases hsE : s ∈ d.E
  · by_cases hxS0 : x ∈ c.S0
    · let r : G := x * s
      have hrA : r ∈ A := A.mul_mem hxA hsA
      have hrS : r ∈ (c.S : Subgroup G) := hAleS hrA
      have hrS0 : r ∉ c.S0 := by
        intro hr0
        have hs0 : s = x⁻¹ * r := by simp [r]
        exact hsS0 (by
          rw [hs0]
          exact c.S0.mul_mem (c.S0.inv_mem hxS0) hr0)
      have hrE : r ∉ d.E := by
        intro hr
        have hxeq : x = r * s⁻¹ := by simp [r]
        apply hxE
        rw [hxeq]
        exact d.E.mul_mem hr (d.E.inv_mem hsE)
      exact ⟨⟨r, hAleM hrA⟩, memSM_of_mem_A hrA,
        centralizerSetup_reflection_isInvolution c ⟨hrS, hrS0⟩,
        hrE, commute_t_of_mem_S hrS⟩
    · exact ⟨⟨x, hAleM hxA⟩, memSM_of_mem_A hxA,
        centralizerSetup_reflection_isInvolution c ⟨hAleS hxA, hxS0⟩,
        hxE, commute_t_of_mem_S (hAleS hxA)⟩
  · exact ⟨⟨s, hAleM hsA⟩, memSM_of_mem_A hsA,
      centralizerSetup_reflection_isInvolution c ⟨hAleS hsA, hsS0⟩,
      hsE, commute_t_of_mem_S (hAleS hsA)⟩

end CFSG.GorensteinWalter
