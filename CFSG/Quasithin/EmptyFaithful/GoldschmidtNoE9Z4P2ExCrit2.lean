module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2ExCrit

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E9P2.ExCrit

section Transport

variable {X : Type} [Group X] {L : Subgroup X} {L' : Type} [Group L']

theorem mem_map_subgroupOf {V : Subgroup X} (e : ↥L ≃* L') (y : L') :
    y ∈ (V.subgroupOf L).map e.toMonoidHom ↔ ((e.symm y : ↥L) : X) ∈ V :=
  Subgroup.mem_map_equiv.trans Subgroup.mem_subgroupOf

theorem card_map_subgroupOf {V : Subgroup X} (hV : V ≤ L) (e : ↥L ≃* L') :
    Nat.card ↥((V.subgroupOf L).map e.toMonoidHom) = Nat.card ↥V := by
  rw [Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV).toEquiv]

theorem isSylowTwoOf_map {G G' : Type} [Group G] [Group G'] {V : Subgroup G}
    (hV : IsSylowTwoOf V ⊤) (e : G ≃* G') : IsSylowTwoOf (V.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hV.2.1.map e.toMonoidHom, ?_⟩
  have h2 : ¬ 2 ∣ V.relIndex ⊤ := hV.2.2
  rw [Subgroup.relIndex_top_right] at h2
  have key : (V.map e.toMonoidHom).index = V.index := Subgroup.index_map_equiv V e
  show ¬ 2 ∣ (V.map e.toMonoidHom).relIndex ⊤
  rwa [Subgroup.relIndex_top_right, key]

end Transport

end E9P2.ExCrit

section Criterion

variable {X : Type} [Group X] [Finite X]

theorem E9Local.false_of_binCrit {L Th Hh Eh R : Subgroup X} (h : E9Local L Th Hh Eh R)
    {L' : Type} [Group L'] (e : ↥L ≃* L') (hc : BinCrit L') : False := by
  have hUL : Th ⊓ L ≤ L := inf_le_right
  have hmem := fun (V : Subgroup X) (y : L') => E9P2.ExCrit.mem_map_subgroupOf (V := V) e y
  set U' : Subgroup L' := ((Th ⊓ L).subgroupOf L).map e.toMonoidHom with hU'
  have hsyl : IsSylowTwoOf U' ⊤ :=
    E9P2.ExCrit.isSylowTwoOf_map (E9P2.Loc.isSylowTwoOf_inf_subgroupOf h.sylow_T h.normal_L) e
  refine h.false_of_criterion ?_ ?_ ?_ ?_
  · obtain ⟨k, hk⟩ := hc.card_sylow U' hsyl
    exact ⟨k, by rw [← E9P2.ExCrit.card_map_subgroupOf hUL e]; exact hk⟩
  · refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) fun u hu => ?_
    have hgen := hc.gen_invol U' hsyl
    let Z : Subgroup L' :=
      ((Subgroup.closure {x : X | x ∈ Th ⊓ L ∧ x * x = 1}).comap L.subtype).map e.toMonoidHom
    have hZ : Subgroup.closure {y : L' | y ∈ U' ∧ y * y = 1} ≤ Z := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyU, hyy⟩
      refine ⟨e.symm y, Subgroup.subset_closure ⟨(hmem _ y).mp hyU, ?_⟩, by simp⟩
      have : e.symm y * e.symm y = 1 := by rw [← map_mul, hyy, map_one]
      simpa using congrArg Subtype.val this
    have hu' : e ⟨u, hUL hu⟩ ∈ U' := (hmem _ _).mpr (by simpa using hu)
    have hu'' : e ⟨u, hUL hu⟩ ∈ Subgroup.closure {y : L' | y ∈ U' ∧ y * y = 1} := by
      rw [hgen]; exact hu'
    obtain ⟨v, hv, hve⟩ := hZ hu''
    have : v = ⟨u, hUL hu⟩ := e.injective hve
    subst this
    exact hv
  · intro z hz hzz hcomm
    let E' : Subgroup L' := (Eh.subgroupOf L).map e.toMonoidHom
    have hE'card : Nat.card ↥E' = 9 := by
      rw [E9P2.ExCrit.card_map_subgroupOf h.E_le_L e]; exact h.card_E
    have hE'exp : ∀ y ∈ E', y ^ 3 = 1 := by
      intro y hy
      have : (e.symm y) ^ 3 = 1 := Subtype.ext (h.exp_E _ ((hmem _ y).mp hy))
      calc y ^ 3 = e (e.symm y ^ 3) := by simp
        _ = 1 := by rw [this, map_one]
    have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
      intro a ha b hb
      have h2 : e.symm a * e.symm b = e.symm b * e.symm a :=
        Subtype.ext (h.comm_E _ ((hmem _ a).mp ha) _ ((hmem _ b).mp hb))
      simpa using congrArg e h2
    have h1 : e ⟨z, hz⟩ = 1 := by
      refine hc.no_invol E' hE'card hE'exp hE'comm (e ⟨z, hz⟩) ?_ ?_
      · rw [← map_mul, show (⟨z, hz⟩ : ↥L) * ⟨z, hz⟩ = 1 from Subtype.ext hzz, map_one]
      · intro y hy
        have h2 : (⟨z, hz⟩ : ↥L) * e.symm y = e.symm y * ⟨z, hz⟩ :=
          Subtype.ext (hcomm _ ((hmem _ y).mp hy))
        simpa using congrArg e h2
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
  · intro x hx hxn hx3
    have hn' : e ⟨x, hx⟩ ∈ Subgroup.normalizer (U' : Set L') := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmem _ y, hmem _ (e ⟨x, hx⟩ * y * (e ⟨x, hx⟩)⁻¹),
        show e.symm (e ⟨x, hx⟩ * y * (e ⟨x, hx⟩)⁻¹) = ⟨x, hx⟩ * e.symm y * ⟨x, hx⟩⁻¹ by simp]
      exact Subgroup.mem_normalizer_iff.mp hxn _
    have h1 : e ⟨x, hx⟩ = 1 := by
      refine hc.no_normalizer U' hsyl _ hn' ?_
      rw [← map_pow, show (⟨x, hx⟩ : ↥L) ^ 3 = 1 from Subtype.ext hx3, map_one]
    exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))

end Criterion

end CFSG.Quasithin
