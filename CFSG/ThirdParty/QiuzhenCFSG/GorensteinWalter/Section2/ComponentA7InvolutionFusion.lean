module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddKernelInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involution fusion in a component with odd central `A₇` quotient

The `A₇` analogue of the `PSL₂` internal-fusion endpoint: if a component
subgroup has odd center and central quotient isomorphic to `A₇`, then all of
its involutions are fused internally to any fixed involution `t` belonging
to the subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If a component subgroup has odd center and central quotient isomorphic
to `A₇`, then all of its involutions are fused internally to any fixed
involution `t` belonging to the subgroup. -/
public theorem component_involutions_fused_of_central_quotient_aSeven
    {G : Type u} [Group G] [Finite G]
    (E : Subgroup G)
    (hZodd : Odd (Nat.card (Subgroup.center E)))
    (e : Nonempty ((E ⧸ Subgroup.center E) ≃* alternatingGroup (Fin 7)))
    {t : G} (htE : t ∈ E) (htI : IsInvolution t) :
    ∀ z : G, z ∈ E → IsInvolution z →
      ∃ g : G, g ∈ E ∧ g * z * g⁻¹ = t := by
  classical
  rcases e with ⟨e⟩
  let N : Subgroup E := Subgroup.center E
  let q : E →* E ⧸ N := QuotientGroup.mk' N
  have hquotient_involution : ∀ {a : E}, IsInvolution a →
      IsInvolution (q a) := by
    intro a ha
    constructor
    · intro hqa
      have haN : a ∈ N :=
        (QuotientGroup.eq_one_iff (N := N) a).mp hqa
      let aN : N := ⟨a, haN⟩
      have haNI : IsInvolution aN := by
        constructor
        · intro haone
          exact ha.1 (congrArg Subtype.val haone)
        · exact Subtype.ext ha.2
      have haNorder : orderOf aN = 2 :=
        orderOf_eq_prime haNI.2 haNI.1
      have htwo : 2 ∣ Nat.card N := by
        rw [← haNorder]
        exact orderOf_dvd_natCard aN
      exact hZodd.not_two_dvd_nat (by simpa [N] using htwo)
    · simpa [q] using congrArg (QuotientGroup.mk' N) ha.2
  let tE : E := ⟨t, htE⟩
  have htEI : IsInvolution tE := by
    constructor
    · intro htone
      exact htI.1 (congrArg Subtype.val htone)
    · exact Subtype.ext htI.2
  intro z hzE hzI
  let zE : E := ⟨z, hzE⟩
  have hzEI : IsInvolution zE := by
    constructor
    · intro hzone
      exact hzI.1 (congrArg Subtype.val hzone)
    · exact Subtype.ext hzI.2
  have hqzI : IsInvolution (q zE) := hquotient_involution hzEI
  have hqtI : IsInvolution (q tE) := hquotient_involution htEI
  have heq : E ⧸ N ≃* alternatingGroup (Fin 7) := by simpa [N] using e
  have heqzI : IsInvolution (heq (q zE)) := by
    constructor
    · intro hone
      exact hqzI.1 (heq.injective (by simpa using hone))
    · simpa using congrArg heq hqzI.2
  have heqtI : IsInvolution (heq (q tE)) := by
    constructor
    · intro hone
      exact hqtI.1 (heq.injective (by simpa using hone))
    · simpa using congrArg heq hqtI.2
  obtain ⟨gm, hgm⟩ :=
    aSeven_involutions_conjugate (heq (q zE)) (heq (q tE)) heqzI heqtI
  have hqconj : ∃ gq : E ⧸ N, gq * q zE * gq⁻¹ = q tE := by
    refine ⟨heq.symm gm, ?_⟩
    apply heq.injective
    simpa using hgm
  obtain ⟨g, hg⟩ :=
    involutions_conjugate_of_quotient_conjugate_odd_kernel
      N (by simpa [N] using hZodd) hzEI htEI hqconj
  exact ⟨(g : G), g.2, congrArg Subtype.val hg⟩

end CFSG.GorensteinWalter
