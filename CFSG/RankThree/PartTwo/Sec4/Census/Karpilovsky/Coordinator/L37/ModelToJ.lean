module

public import CFSG.RankThree.Native.ONTripleRed

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple CFSG.Sporadic.Bridge.ON CFSG.Sporadic.ON


theorem toJ_injective : Function.Injective (toJ : PON.Group →* J) := by
  have hfin : Finite PON.Group := Nat.finite_of_card_ne_zero (by rw [card_PON]; norm_num)
  exact (toJ_surjective.bijective_of_nat_card_le (by rw [card_PON, card_J])).1

@[expose] noncomputable def phiJ : GM →* J :=
  (toJ : PON.Group →* J).comp (piON.comp modelEquiv.symm.toMonoidHom)

theorem phiJ_surjective : Function.Surjective phiJ :=
  toJ_surjective.comp (piON_surjective.comp modelEquiv.symm.surjective)

theorem ker_phiJ : phiJ.ker = Subgroup.zpowers zG := by
  ext g
  rw [MonoidHom.mem_ker, phiJ, MonoidHom.comp_apply, MonoidHom.comp_apply,
    (map_eq_one_iff toJ toJ_injective), ← MonoidHom.mem_ker, ker_piON,
    MulEquiv.coe_toMonoidHom, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← modelEquiv_zF, ← map_zpow, hk, MulEquiv.apply_symm_apply]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← modelEquiv_zF, ← map_zpow, MulEquiv.symm_apply_apply]

theorem ker_phiJ_eq_center :
    phiJ.ker = Subgroup.center GM := by
  rw [ker_phiJ, center_GM]

theorem phiJ_of (k : Fin 8) :
    phiJ (modelEquiv (PresentedGroup.of k)) = toJ (piON (PresentedGroup.of k)) := by
  rw [phiJ, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37
