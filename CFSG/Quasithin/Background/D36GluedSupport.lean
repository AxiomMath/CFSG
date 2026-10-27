module

public import CFSG.Quasithin.Background.SmithD36TLift

public section

namespace CFSG.Quasithin

section Normalized

variable {W : Type} [CommGroup W] [Finite W]
  {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}

theorem d36_intersection_le_fixed (structureInput : D3L38)
    (normalized : D36Norm M Mp T L V t) :
    commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom ≤
      orbSup T V ⊓ fixV Mp := by
  have commutator_le : commSub (orbSup T V) L ≤ orbSup T V := by
    rw [d36_U_eq structureInput normalized]
    exact orbSup_le fun automorphism membership => map_le_orbSup membership.1
  exact le_inf (inf_le_left.trans commutator_le)
    (d36t_D_le_fixV structureInput normalized)

theorem d36_gluedPair_with_rank_centralizer (structureInput : D3L38)
    (normalized : D36Norm M Mp T L V t) :
    GluedPair (autSub (Mp ⊔ T) (orbSup T V))
      ((commSub (orbSup T V) L).subgroupOf (orbSup T V))
      (((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) ∧
    (rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V) ⊓
      ((commSub (orbSup T V) L).map t.toMonoidHom).subgroupOf (orbSup T V)) + 2 <
        rk ↥((commSub (orbSup T V) L).subgroupOf (orbSup T V))) ∧
    (commSub (orbSup T V) L ⊓ (commSub (orbSup T V) L).map t.toMonoidHom ≤
      orbSup T V ⊓ fixV Mp) := by
  exact ⟨⟨d36_sup_Y structureInput normalized, d36_perm_Y structureInput normalized,
      d36_swap_Y structureInput normalized, d36_faithful_Y structureInput normalized⟩,
    d36_rank_Y structureInput normalized, d36_intersection_le_fixed structureInput normalized⟩

end Normalized

end CFSG.Quasithin
