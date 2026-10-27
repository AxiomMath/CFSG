module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.QuasithinUnique CFSG.Open
open CFSG.QuasithinUnique.Setup.Layer (isSylowTwoOf_map_mulEquiv normal_subgroupOf_map_iff)

section Subgroups

variable {G G' : Type*} [Group G] [Group G']

theorem centralizer_map_equiv (θ : G ≃* G') (D : Subgroup G) :
    Subgroup.centralizer ((D.map θ.toMonoidHom : Subgroup G') : Set G') =
      (Subgroup.centralizer (D : Set G)).map θ.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨θ.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have := hx (θ d) (Subgroup.mem_map_of_mem _ hd)
    apply θ.injective
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hy d hd
    simpa using congrArg θ this

theorem map_symm_map (θ : G ≃* G') (Q : Subgroup G) :
    (Q.map θ.toMonoidHom).map θ.symm.toMonoidHom = Q := by
  rw [Subgroup.map_map]
  have : θ.symm.toMonoidHom.comp θ.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id]

theorem isSylowTwoOf_bot_of_odd {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hodd : Odd (Nat.card H)) : IsSylowTwoOf (⊥ : Subgroup G) H := by
  refine ⟨bot_le, IsPGroup.of_card (n := 0) (by simp), ?_⟩
  have h := Subgroup.relIndex_mul_card (⊥ : Subgroup G) H
  rw [inf_eq_left.2 bot_le] at h
  simp only [Subgroup.card_bot, mul_one] at h
  change ¬ 2 ∣ (⊥ : Subgroup G).relIndex H
  rw [h]
  exact fun hd => Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 hd)

end Subgroups

end CFSG.Quasithin.H13.F431.D4q.Struct
