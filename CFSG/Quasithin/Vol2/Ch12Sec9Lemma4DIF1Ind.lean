module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Trans
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Idx

public section

namespace CFSG.Quasithin.H13.C1294

open Module MulAction

section Actions

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I]

abbrev SuperOf (W : Submodule (ZMod 2) I) (j : ℕ) : Type :=
  {U : Submodule (ZMod 2) I // W ≤ U ∧ finrank (ZMod 2) U = j}

instance instMulActionStabSubsOf (W : Submodule (ZMod 2) I) (j : ℕ) :
    MulAction (stabS W) (SubsOf W j) where
  smul g U := ⟨U.1.map (g.1 : I →ₗ[ZMod 2] I), by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : I) ∈ W := U.2.1 hx
      exact ((g : stabS W).2 x).1 hx'
    · rw [LinearEquiv.finrank_map_eq]
      exact U.2.2⟩
  one_smul U := Subtype.ext (Submodule.map_id _)
  mul_smul g h U := Subtype.ext (by
    show U.1.map ((g * h).1 : I →ₗ[ZMod 2] I) =
      (U.1.map (h.1 : I →ₗ[ZMod 2] I)).map
        (g.1 : I →ₗ[ZMod 2] I)
    rw [← Submodule.map_comp]
    rfl)

instance instMulActionStabSuperOf (W : Submodule (ZMod 2) I) (j : ℕ) :
    MulAction (stabS W) (SuperOf W j) where
  smul g U := ⟨U.1.map (g.1 : I →ₗ[ZMod 2] I), by
    refine ⟨?_, ?_⟩
    · have hW : W.map (g.1 : I →ₗ[ZMod 2] I) = W := map_eq_of_mem_stabS g.2
      exact (le_of_eq hW.symm).trans (Submodule.map_mono U.2.1)
    · rw [LinearEquiv.finrank_map_eq]
      exact U.2.2⟩
  one_smul U := Subtype.ext (Submodule.map_id _)
  mul_smul g h U := Subtype.ext (by
    show U.1.map ((g * h).1 : I →ₗ[ZMod 2] I) =
      (U.1.map (h.1 : I →ₗ[ZMod 2] I)).map
        (g.1 : I →ₗ[ZMod 2] I)
    rw [← Submodule.map_comp]
    rfl)

theorem stabilizer_subsOf_eq (W : Submodule (ZMod 2) I) {U : Submodule (ZMod 2) I}
    (hU : U ≤ W) :
    stabilizer (stabS W) (⟨U, hU, rfl⟩ : SubsOf W (finrank (ZMod 2) U)) =
      (stabS U ⊓ stabS W).subgroupOf (stabS W) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    have hU' : U.map (g.1 : I →ₗ[ZMod 2] I) = U := h'
    exact ⟨(map_eq_iff_mem_stabS U _).1 hU', g.2⟩
  · intro h
    apply Subtype.ext
    exact (map_eq_iff_mem_stabS U _).2 h.1


theorem stabilizer_superOf_eq (W : Submodule (ZMod 2) I) {U : Submodule (ZMod 2) I}
    (hWU : W ≤ U) :
    stabilizer (stabS W) (⟨U, hWU, rfl⟩ : SuperOf W (finrank (ZMod 2) U)) =
      (stabS U).subgroupOf (stabS W) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    have hU' : U.map (g.1 : I →ₗ[ZMod 2] I) = U := h'
    exact (map_eq_iff_mem_stabS U _).1 hU'
  · intro h
    apply Subtype.ext
    exact (map_eq_iff_mem_stabS U _).2 h

instance isPretransitive_stabS_superOf [FiniteDimensional (ZMod 2) I] (W : Submodule (ZMod 2) I)
    (j : ℕ) : IsPretransitive (stabS W) (SuperOf W j) := by
  constructor
  rintro ⟨U, hU, hUj⟩ ⟨U', hU', hUj'⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  obtain ⟨g, hg, -, hmap⟩ := exists_stabS_fix_map_super hC hU hU' (hUj.trans hUj'.symm)
  exact ⟨⟨g, hg⟩, Subtype.ext hmap⟩

instance isPretransitive_stabS_subsOf [FiniteDimensional (ZMod 2) I] (W : Submodule (ZMod 2) I)
    (j : ℕ) : IsPretransitive (stabS W) (SubsOf W j) := by
  constructor
  rintro ⟨U, hU, hUj⟩ ⟨U', hU', hUj'⟩
  obtain ⟨g, hg, hmap⟩ := exists_stabS_map_sub W hU hU' (hUj.trans hUj'.symm)
  exact ⟨⟨g, hg⟩, Subtype.ext hmap⟩

theorem index_inf_sub [FiniteDimensional (ZMod 2) I] {W U : Submodule (ZMod 2) I}
    (hU : U ≤ W) :
    (stabS U ⊓ stabS W).index =
      (stabS W).index * Nat.card (SubsOf W (finrank (ZMod 2) U)) := by
  have h1 := Subgroup.relIndex_mul_index (inf_le_right : stabS U ⊓ stabS W ≤ stabS W)
  have hrel : (stabS U ⊓ stabS W).relIndex (stabS W) = Nat.card (SubsOf W (finrank (ZMod 2) U)) := by
    rw [Subgroup.relIndex, ← stabilizer_subsOf_eq W hU, MulAction.index_stabilizer_of_transitive]
  rw [← h1, hrel, mul_comm]

theorem index_inf_super [FiniteDimensional (ZMod 2) I] {W U : Submodule (ZMod 2) I}
    (hWU : W ≤ U) :
    (stabS W ⊓ stabS U).index =
      (stabS W).index * Nat.card (SuperOf W (finrank (ZMod 2) U)) := by
  have h1 := Subgroup.relIndex_mul_index (inf_le_left : stabS W ⊓ stabS U ≤ stabS W)
  have hrel : (stabS W ⊓ stabS U).relIndex (stabS W) =
      Nat.card (SuperOf W (finrank (ZMod 2) U)) := by
    have e : (stabS W ⊓ stabS U).subgroupOf (stabS W) = (stabS U).subgroupOf (stabS W) := by
      ext h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h' => h'.2, fun h' => ⟨h.2, h'⟩⟩
    rw [Subgroup.relIndex, e, ← stabilizer_superOf_eq W hWU, MulAction.index_stabilizer_of_transitive]
  rw [← h1, hrel, mul_comm]

end Actions

end CFSG.Quasithin.H13.C1294
