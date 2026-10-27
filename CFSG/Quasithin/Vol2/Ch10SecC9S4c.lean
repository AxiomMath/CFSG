module

public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Vol2.Ch10SecC9Comp
public import CFSG.Quasithin.Vol2.Ch10SecC9U

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

abbrev VI (T L I J : Subgroup G) (w : G) : Subgroup G :=
  conjClosure (fsuUL T L I ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G))
    (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))

theorem fsuUL_inf_le_omegaOne (hyp : Hyp10 G T L I) {w : G} (hwV : w ∈ fsuVM T L I) :
    fsuUL T L I ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) ≤
      quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({w} : Set G)) := by
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  have hV1V : fsuUL T L I ≤ fsuVM T L I := commutator_le_left_of_le_normalizer hLN
  rintro x ⟨hx1, hxc⟩
  have hxV := hV1V hx1
  refine Subgroup.subset_closure ⟨⟨⟨SecA.fsuVM_le_T hyp hxV, ?_⟩, hxc⟩,
    (SecA.isElemAbelian_fsuVM hyp).2 x hxV⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (fsuVM_comm hyp hxV hwV)

theorem VI_props (hyp : Hyp10 G T L I) {w : G} (hwV : w ∈ fsuVM T L I) {J : Subgroup G}
    (hSyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({w} : Set G))
      (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hF : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G)))) :
    VI T L I J w ≤ pCoreOf 2 (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) ⊓
        Subgroup.centralizer
          (pCoreOf 2 (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) : Set G) ∧
      IsElemAbelian 2 (VI T L I J w) ∧
      IsTwoReducedIn (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) (VI T L I J w) :=
  conjClosure_isTwoReducedIn_of_charTwo hSyl hF (fsuUL_inf_le_omegaOne hyp hwV)

theorem centralizer_le_of_fsuUL_le (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) {X : Subgroup G}
    (hX : fsuUL T L I ≤ X) : Subgroup.centralizer (X : Set G) ≤ fsuM T L :=
  (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX)).trans
    ((Subgroup.centralizer_le_normalizer _).trans ((h1026 G T L I hyp).2.1 L (Or.inl rfl)))

theorem centralizer_le_of_mem (hyp : Hyp10 G T L I) (h1026 : Stmt10_2_6) {X : Subgroup G} {z : G}
    (hzX : z ∈ X) (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzc : fsuL0 T L ⊔ T1 T L ≤ Subgroup.centralizer ({z} : Set G)) :
    Subgroup.centralizer (X : Set G) ≤ fsuM T L :=
  (Subgroup.centralizer_le (by simpa using hzX)).trans
    (le_fsuM_of_le hyp h1026 hzc (pCoreOf_centralizer_ne_bot hz1 hz2))

theorem conjClosure_eq_of_lt {X J : Subgroup G} (hJ : J ∈ cComp X) (hLJ : L ≤ J)
    (hLs : ¬ Group.IsSolvable ↥L) : conjClosure L J = J := by
  have hle : conjClosure L J ≤ J := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, l, hl, rfl⟩
    exact J.mul_mem (J.mul_mem hh (hLJ hl)) (J.inv_mem hh)
  have hn : ((conjClosure L J).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr (le_normalizer_conjClosure L J)
  rcases normal_eq_top_or_map_le_solvRad hJ ((conjClosure L J).subgroupOf J) with h | h
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hle h
  · exfalso
    rw [Subgroup.map_subgroupOf_eq_of_le hle] at h
    have hLR : L ≤ solvRad J := (le_conjClosure L J).trans h
    have := solvRad_isSolvable J
    exact hLs (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLR))

end CFSG.Quasithin.Vol2.Ch10.SecC
