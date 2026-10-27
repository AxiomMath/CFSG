module

public import CFSG.RankThree.PartOne.U5K.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.RankThree.PartOne.U5K.Model

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG CFSG.QuasithinUnique.Setup.Campbell

section Map

variable {H H' : Type} [Group H] [Group H'] [Finite H] (f : H →* H')

noncomputable def equivMapOfInjOn {T : Subgroup H} (hf : Function.Injective (f.comp T.subtype)) :
    ↥T ≃* ↥(T.map f) :=
  (MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

omit [Finite H] in
theorem subtype_comp_equivMapOfInjOn {T : Subgroup H} (hf : Function.Injective (f.comp T.subtype)) :
    (T.map f).subtype.comp (equivMapOfInjOn f hf).toMonoidHom = f.comp T.subtype := by
  ext x
  rfl

theorem map_elemCenter_subtype {T : Subgroup H} (hf : Function.Injective (f.comp T.subtype)) :
    ((elemThompsonCenterTorsion ↥T 2).map T.subtype).map f =
      (elemThompsonCenterTorsion ↥(T.map f) 2).map (T.map f).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(T.map f) := Finite.of_equiv ↥T (equivMapOfInjOn f hf).toEquiv
  rw [← elemThompsonCenterTorsion_map_mulEquiv (equivMapOfInjOn f hf) 2, Subgroup.map_map,
    Subgroup.map_map, subtype_comp_equivMapOfInjOn f hf]

theorem map_pushingUpS {T : Subgroup H} (hf : Function.Injective (f.comp T.subtype)) :
    (pushingUpS T).map f = pushingUpS (T.map f) := by
  have hJ : (inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) T).map f =
      inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) (T.map f) := map_elemCenter_subtype f hf
  have hJT : inSubgroup (fun K _ => elemThompsonCenterTorsion K 2) T ≤ T :=
    Subgroup.map_subtype_le _
  unfold pushingUpS
  rw [← hJ]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨x, ⟨hxT, hxc⟩, rfl⟩
    refine ⟨⟨x, hxT, rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul, hxc j hj]
  · rintro ⟨⟨x, hxT, rfl⟩, hc⟩
    refine ⟨x, ⟨hxT, fun j hj => ?_⟩, rfl⟩
    have h1 := hc (f j) ⟨j, hj, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    have hj' : j ∈ T := hJT hj
    have := @hf ⟨j * x, T.mul_mem hj' hxT⟩ ⟨x * j, T.mul_mem hxT hj'⟩ h1
    exact congrArg Subtype.val this

omit [Finite H] in
theorem map_zOf {S : Subgroup H} (hf : Function.Injective (f.comp S.subtype)) :
    (zOf S).map f = zOf (S.map f) := by
  let e := equivMapOfInjOn f hf
  have hcomp := subtype_comp_equivMapOfInjOn f hf
  have hc : (Subgroup.center ↥S).map e.toMonoidHom = Subgroup.center ↥(S.map f) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := Subgroup.mem_center_iff.1 hx
      refine Subgroup.mem_center_iff.2 fun z => ?_
      obtain ⟨w, rfl⟩ := e.surjective z
      show e w * e x = e x * e w
      rw [← map_mul, ← map_mul, hx' w]
    · intro hy
      have hy' := Subgroup.mem_center_iff.1 hy
      refine ⟨e.symm y, Subgroup.mem_center_iff.2 fun z => ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hy' (e z)]
  unfold zOf
  rw [← hc, Subgroup.map_map, Subgroup.map_map, hcomp]

end Map

section Rm

variable {G : Type} [Group G] [Finite G] {Â : Type} [Group Â] {N : Subgroup G} {ρ : ↥N →* Â}

omit [Finite G] in
theorem pushingUpS_le (T : Subgroup G) : pushingUpS T ≤ T := inf_le_left

omit [Finite G] in
theorem injective_comp_subtype {T : Subgroup G}
    (hinj : ∀ t ∈ T, ∀ ht : t ∈ N, ρ ⟨t, ht⟩ = 1 → t = 1) :
    Function.Injective (ρ.comp (T.subgroupOf N).subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : ρ (a : ↥N) = 1 := ha
  have h2 : ((a : ↥N) : G) = 1 := hinj ((a : ↥N) : G) a.2 (a : ↥N).2 h1
  exact Subtype.ext (Subtype.ext h2)

theorem rm_pushingUpS {T : Subgroup G} (hTN : T ≤ N)
    (hinj : ∀ t ∈ T, ∀ ht : t ∈ N, ρ ⟨t, ht⟩ = 1 → t = 1) :
    rm N ρ (pushingUpS T) = pushingUpS (rm N ρ T) ∧
      (pushingUpS T).subgroupOf N = pushingUpS (T.subgroupOf N) := by
  have hT : (T.subgroupOf N).map N.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTN
  have hinjT := injective_comp_subtype (ρ := ρ) hinj
  have hinjN : Function.Injective (N.subtype.comp (T.subgroupOf N).subtype) :=
    N.subtype_injective.comp (T.subgroupOf N).subtype_injective
  have h1 : (pushingUpS (T.subgroupOf N)).map N.subtype = pushingUpS T := by
    rw [map_pushingUpS N.subtype hinjN, hT]
  have h2 : (pushingUpS T).subgroupOf N = pushingUpS (T.subgroupOf N) := by
    rw [← h1, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  refine ⟨?_, h2⟩
  unfold rm
  rw [h2, map_pushingUpS ρ hinjT]

theorem rm_zOf {T : Subgroup G} (hTN : T ≤ N)
    (hinj : ∀ t ∈ T, ∀ ht : t ∈ N, ρ ⟨t, ht⟩ = 1 → t = 1) :
    rm N ρ (zOf (pushingUpS T)) = zOf (pushingUpS (rm N ρ T)) := by
  obtain ⟨hS, h2⟩ := rm_pushingUpS (ρ := ρ) hTN hinj
  have hSN : pushingUpS T ≤ N := (pushingUpS_le T).trans hTN
  set S := pushingUpS T with hSdef
  have hSt : (S.subgroupOf N).map N.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSN
  have hinjS : Function.Injective (ρ.comp (S.subgroupOf N).subtype) :=
    injective_comp_subtype (ρ := ρ) fun t ht htN => hinj t (pushingUpS_le T ht) htN
  have hinjN : Function.Injective (N.subtype.comp (S.subgroupOf N).subtype) :=
    N.subtype_injective.comp (S.subgroupOf N).subtype_injective
  have h3 : (zOf S).subgroupOf N = zOf (S.subgroupOf N) := by
    have := map_zOf N.subtype hinjN
    rw [hSt] at this
    rw [← this, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  unfold rm
  rw [h3, map_zOf ρ hinjS]
  have : (S.subgroupOf N).map ρ = pushingUpS (rm N ρ T) := by rw [← hS]; rfl
  rw [this]
  rfl

end Rm

end CFSG.RankThree.PartOne.U5K
