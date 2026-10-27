module

public import CFSG.Permutation.FiveTransitive.OrbitRestrictionKernel
public import CFSG.Permutation.FiveTransitive.A9SmallKernelFactor
public import CFSG.Permutation.FiveTransitive.A9TransitiveTenThirteen
public import CFSG.Permutation.FiveTransitive.A9SmallDegreePrimitive
public import CFSG.Permutation.FiveTransitive.DegreeFourteenPrimitiveQuotient

public section

namespace CFSG

namespace FiveTransitive.A9FourteenNineOrbit
open MulAction

theorem exists_nine_orbit
    {F E : Type} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E ≤ 14)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) : ∃ x : E, Nat.card (orbit B x) = 9 := by
  classical
  have hbig : ∃ x : E, 9 ≤ Nat.card (orbit B x) := by
    by_contra! hn
    let rho := (alternatingGroup F).subtype.comp tau
    have hAlt : alternatingGroup F ≤ rho.range := by
      intro g hg
      obtain ⟨b,hb⟩ := htau ⟨g,hg⟩
      exact ⟨b,congrArg Subtype.val hb⟩
    exact A9SmallOrbitQuotient.false_of_small_orbits hF rho hAlt (fun x => by have := hn x; omega)
  obtain ⟨x,hx⟩ := hbig
  let O := orbit B x
  let _ : Fintype O := Fintype.ofFinite _
  let sigma := toPermHom B O
  have hk : Nat.card sigma.ker < 181440 :=
    lt_of_le_of_lt (OrbitRestrictionKernel.card_kernel_le B x hE hx) (by decide)
  obtain ⟨t,ht,he⟩ := A9SmallKernelFactor.exists_factor hF tau htau sigma hk
  let D := sigma.range
  let _ : IsPretransitive D O := by
    constructor
    intro y z
    obtain ⟨b,hb⟩ := (inferInstance : IsPretransitive B O).exists_smul_eq y z
    exact ⟨⟨sigma b,⟨b,rfl⟩⟩,hb⟩
  have hO : Nat.card O ≤ 14 :=
    (Nat.card_le_card_of_injective (fun y : O => y.val) Subtype.val_injective).trans hE
  refine ⟨x,?_⟩
  by_contra hn
  by_cases h14 : Nat.card O = 14
  · let rho := (alternatingGroup F).subtype.comp t
    have hAlt : alternatingGroup F ≤ rho.range := by
      intro g hg
      obtain ⟨b,hb⟩ := ht ⟨g,hg⟩
      exact ⟨b,congrArg Subtype.val hb⟩
    have hp := A9SmallDegreePrimitive.isPreprimitive hF rho hAlt hO
    exact DegreeFourteenPrimitiveQuotient.not_surjective h14 hF D hp t ht
  · have hlo : 10 ≤ Nat.card O := by dsimp only [O]; omega
    exact A9TransitiveTenThirteen.not_surjective hF hlo (by omega) D t ht

end FiveTransitive.A9FourteenNineOrbit

end CFSG
