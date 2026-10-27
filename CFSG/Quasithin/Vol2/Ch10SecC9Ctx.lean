module

public import CFSG.Quasithin.Vol2.Ch10SecC8Main4c
public import CFSG.Quasithin.Vol2.Ch10SecC9Out

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

structure Conf (T L I : Subgroup G) (t w : G) (J : Subgroup G) : Prop where
  hyp : Hyp10 G T L I
  ht : t ∈ T
  htn : t ∉ Subgroup.normalizer (L : Set G)
  claim : ClaimOut T L I t w
  mem : J ∈ cComp (Subgroup.centralizer ({w} : Set G))
  le : L ≤ J
  ne : L ≠ J
  normal : (J.subgroupOf (Subgroup.centralizer ({w} : Set G))).Normal
  not_le : ¬ J ≤ fsuM T L

namespace Conf

variable {T L I J : Subgroup G} {t w : G} (c : Conf T L I t w J)
include c

theorem w_mem_V : w ∈ fsuVM T L I := commutator_le_left_of_le_normalizer
  ((SecA.conjugate_le_fsuL0 c.ht).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) c.claim.1

theorem w_ne_one : w ≠ 1 := fun h => c.claim.2.1 (h ▸ Subgroup.one_mem _)

theorem w_sq : w ^ 2 = 1 := (SecA.isElemAbelian_fsuVM c.hyp).2 w c.w_mem_V

theorem J_le : J ≤ Subgroup.centralizer ({w} : Set G) := le_of_mem_cComp c.mem

theorem sylow : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G))
    (Subgroup.centralizer ({w} : Set G)) := c.claim.2.2.2.1

theorem Tw_le_normalizer : T ⊓ Subgroup.centralizer ({w} : Set G) ≤
    Subgroup.normalizer (J : Set G) :=
  inf_le_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer c.J_le).mp c.normal)

theorem isSylowTwoOf_sup : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G))
    (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) :=
  A4.isSylowTwoOf_mono c.sylow le_sup_right (sup_le c.J_le inf_le_right)

theorem Tw_le_T1 (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) :
    T ⊓ Subgroup.centralizer ({w} : Set G) ≤ T1 T L := by
  rintro s ⟨hs, hsw⟩
  refine ⟨hs, ?_⟩
  rcases SecA.conjugate_eq_or h37 h38 c.hyp c.ht c.htn (SecA.le_fsuM T L hs) with h | h
  · exact SecA.conjugate_eq_self_iff.mp h
  · exfalso
    have hsw' : s * w * s⁻¹ = w := mul_conj_eq_of_mem_centralizer hsw
    have key : w ∈ ⁅fsuVM T L I, CFSG.conjugate L s⁆ := by
      rw [h]
      exact c.claim.1
    rw [← SecA.conjugate_commutator_fsuVM (I := I) (SecA.le_fsuM T L hs), SecA.mem_conjugate_iff,
      hsw'] at key
    exact c.claim.2.1 key

end Conf

end CFSG.Quasithin.Vol2.Ch10.SecC
