module

public import CFSG.Quasithin.Vol2.Ch11SecBK9A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

variable {G : Type} [Group G]

@[expose] def hypSet (V : Subgroup G) : Set (Subgroup G) :=
  {U | U ≤ V ∧ U.relIndex V = 2}

theorem map_conj_eq_of_mem_normalizer {V : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) : V.map (MulAut.conj t).toMonoidHom = V := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ht v).mp hv
  · intro hx
    refine ⟨t⁻¹ * x * t, (Subgroup.mem_normalizer_iff.mp ht _).mpr ?_, ?_⟩
    · rwa [show t * (t⁻¹ * x * t) * t⁻¹ = x by group]
    · show t * (t⁻¹ * x * t) * t⁻¹ = x
      group

theorem map_conj_mem_hypSet {V U : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hU : U ∈ hypSet V) :
    U.map (MulAut.conj t).toMonoidHom ∈ hypSet V := by
  refine ⟨?_, ?_⟩
  · rw [← map_conj_eq_of_mem_normalizer ht]
    exact Subgroup.map_mono hU.1
  · rw [← hU.2, ← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj t).toMonoidHom) U V
      (MulAut.conj t).injective, map_conj_eq_of_mem_normalizer ht]

@[expose, instance_reducible] def hypAct (V T : Subgroup G)
    (hT : T ≤ Subgroup.normalizer (V : Set G)) : MulAction ↥T ↥(hypSet V) where
  smul t U := ⟨U.1.map (MulAut.conj (t : G)).toMonoidHom, map_conj_mem_hypSet (hT t.2) U.2⟩
  one_smul U := Subtype.ext (by
    show U.1.map (MulAut.conj ((1 : ↥T) : G)).toMonoidHom = U.1
    ext x
    simp)
  mul_smul s t U := Subtype.ext (by
    show U.1.map (MulAut.conj ((s * t : ↥T) : G)).toMonoidHom =
      (U.1.map (MulAut.conj (t : G)).toMonoidHom).map (MulAut.conj (s : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc])

theorem le_normalizer_of_mem_fixedPoints {V T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (V : Set G)) {U : ↥(hypSet V)}
    (hU : U ∈ @MulAction.fixedPoints ↥T ↥(hypSet V) _ (hypAct V T hT)) :
    T ≤ Subgroup.normalizer (U.1 : Set G) := by
  intro t ht
  have h := congrArg Subtype.val (hU ⟨t, ht⟩)
  change U.1.map (MulAut.conj t).toMonoidHom = U.1 at h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      change t * y * t⁻¹ = t * x * t⁻¹ at hyx
      simpa using hyx
    rwa [← this]

theorem exists_fixed_hyp [Finite G] {V T : Subgroup G} (hT2 : IsPGroup 2 ↥T)
    (hT : T ≤ Subgroup.normalizer (V : Set G)) (hodd : ¬ 2 ∣ Nat.card ↥(hypSet V)) :
    ∃ U ∈ hypSet V, T ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := hypAct V T hT
  obtain ⟨U, hU⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card ↥(hypSet V) hodd
  exact ⟨U.1, U.2, le_normalizer_of_mem_fixedPoints hT hU⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
