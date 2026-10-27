module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFJCent
public import CFSG.Quasithin.EmptyFaithful.SBd18Out

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Sporadic.Schreier CFSG.ComponentClassification.J2Cover

theorem not_isSolvable_map_conj {M : Type*} [Group M] (K : Subgroup M) (c : M)
    (h : ¬ Group.IsSolvable ↥K) : ¬ Group.IsSolvable ↥(K.map (MulAut.conj c).toMonoidHom) := by
  intro hs
  exact h (Group.isSolvable_of_isSolvable_injective
    (f := (K.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).toMonoidHom)
    (K.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).injective)

theorem map_fixedSub_rConj (r : R) :
    (SBd18.fixedSub (rConj r)).map P.subtype = centralizerIn P (r : Equiv.Perm (Fin 315)) := by
  ext q
  rw [Subgroup.mem_map, mem_centralizerIn]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, ?_⟩
    have h := congrArg (fun z : P => (z : Equiv.Perm (Fin 315))) (SBd18.mem_fixedSub.mp hp)
    simp only [rConj_apply] at h
    calc (p : Equiv.Perm (Fin 315)) * r = r * p * (r : Equiv.Perm (Fin 315))⁻¹ * r := by rw [h]
      _ = r * p := by group
  · rintro ⟨hq, hqr⟩
    refine ⟨⟨q, hq⟩, SBd18.mem_fixedSub.mpr (Subtype.ext ?_), rfl⟩
    rw [rConj_apply]
    calc (r : Equiv.Perm (Fin 315)) * q * (r : Equiv.Perm (Fin 315))⁻¹
        = (q * r) * (r : Equiv.Perm (Fin 315))⁻¹ := by rw [hqr]
      _ = q := by group

theorem not_isSolvable_fixedSub_rConj (r : R)
    (h : ¬ Group.IsSolvable ↥(centralizerIn P (r : Equiv.Perm (Fin 315)))) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub (rConj r)) := by
  intro hs
  apply h
  rw [← map_fixedSub_rConj r]
  let e := (SBd18.fixedSub (rConj r)).equivMapOfInjective P.subtype P.subtype_injective
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem not_isSolvable_fixedSub_of_sq_P
    (α : MulAut P) (hα : α * α = 1) :
    ¬ Group.IsSolvable ↥(SBd18.fixedSub α) := by
  obtain ⟨r, rfl⟩ := rConj_bijective.2 α
  have hr2 : r * r = 1 := rConj_injective (by rw [map_mul, hα, map_one])
  have hrr : (r : Equiv.Perm (Fin 315)) * r = 1 := by
    have := congrArg Subtype.val hr2
    simpa using this
  refine not_isSolvable_fixedSub_rConj r ?_
  by_cases hr1 : (r : Equiv.Perm (Fin 315)) = 1
  · have : centralizerIn P (r : Equiv.Perm (Fin 315)) = P := by
      rw [hr1]
      ext x
      rw [mem_centralizerIn]
      simp
    rw [this]
    exact not_isSolvable_P
  · have hord : orderOf (r : Equiv.Perm (Fin 315)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hrr) hr1
    rcases mem_P_or_coset r.2 with hrP | hru
    · obtain ⟨s, hs, c, hc, hrc⟩ := inner_classes.1 _ hrP hord
      rw [hrc, centralizerIn_conj P hc]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · rw [inner_classes.2.2.1]
        exact not_isSolvable_map_conj _ _ not_isSolvable_cent2B
      · rw [inner_classes.2.2.2.2]
        exact not_isSolvable_map_conj _ _ not_isSolvable_cent2A
    · obtain ⟨c, hc, hrc⟩ := outer_classes.1 _ hru hord
      rw [hrc, centralizerIn_conj P hc, outer_classes.2.2]
      exact not_isSolvable_map_conj _ _ not_isSolvable_centOuter

end CFSG.Quasithin.SBd19F
