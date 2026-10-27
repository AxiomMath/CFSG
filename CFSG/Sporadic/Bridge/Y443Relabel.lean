module

public import CFSG.Sporadic.Bridge.Y443Split
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.MonsterY443Defs

public section

namespace CFSG.Sporadic.Bridge.Y443

open CFSG.Blueprint.NativeSporadic CFSG.Open

@[expose] def gen (i : Fin 12) : MonsterY443Gen :=
  if i.val = 0 then none
  else if h1 : i.val ≤ 4 then some ⟨0, ⟨i.val - 1, by simp [monsterY443ArmLength]; omega⟩⟩
  else if h2 : i.val ≤ 8 then some ⟨1, ⟨i.val - 5, by simp [monsterY443ArmLength]; omega⟩⟩
  else some ⟨2, ⟨i.val - 9, by simp [monsterY443ArmLength]; omega⟩⟩

@[expose] def num : MonsterY443Gen → Fin 12
  | none => 0
  | some ⟨0, j⟩ => ⟨j.val + 1, by have := j.isLt; simp [monsterY443ArmLength] at this; omega⟩
  | some ⟨1, j⟩ => ⟨j.val + 5, by have := j.isLt; simp [monsterY443ArmLength] at this; omega⟩
  | some ⟨2, j⟩ => ⟨j.val + 9, by have := j.isLt; simp [monsterY443ArmLength] at this; omega⟩

theorem num_gen : ∀ i : Fin 12, num (gen i) = i := by decide

theorem gen_num : ∀ s : MonsterY443Gen, gen (num s) = s := by decide

theorem adj_gen (i j : Fin 12) : MonsterY443Adj (gen i) (gen j) ↔ adjB i j = true := by
  fin_cases i <;> fin_cases j <;> simp [gen, MonsterY443Adj, adjB, adjList]

theorem gen_injective : Function.Injective gen := fun i j h => by
  rw [← num_gen i, ← num_gen j, h]

theorem num_injective : Function.Injective num := fun s t h => by
  rw [← gen_num s, ← gen_num t, h]

theorem adjB_irrefl : ∀ i : Fin 12, adjB i i = false := by decide

theorem lift_gen_eq (r : FreeGroup (Fin 12)) :
    FreeGroup.lift (fun i => (PresentedGroup.of (gen i) : MonsterY443)) r =
      PresentedGroup.mk monsterY443Rels (FreeGroup.map gen r) := by
  have : FreeGroup.lift (fun i => (PresentedGroup.of (gen i) : MonsterY443)) =
      (PresentedGroup.mk monsterY443Rels).comp (FreeGroup.map gen) :=
    FreeGroup.ext_hom _ _ fun i => by simp [PresentedGroup.of]
  rw [this, MonoidHom.comp_apply]

noncomputable def toOpen : Y443 →* MonsterY443 :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.of (gen i)) (by
    intro r hr
    rw [lift_gen_eq]
    apply PresentedGroup.one_of_mem
    unfold y443Relations at hr
    rcases hr with ((⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩) | rfl)
    · exact Or.inl (Or.inl (Or.inl ⟨gen i, by simp⟩))
    · have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
      by_cases hb : adjB i j = true
      · rw [ite_eq_left ((adjacent_iff_adjB i j).2 hb)]
        exact Or.inl (Or.inl (Or.inr ⟨gen i, gen j, (adj_gen i j).2 hb, by simp⟩))
      · rw [ite_eq_right (fun h => hb ((adjacent_iff_adjB i j).1 h))]
        exact Or.inl (Or.inr ⟨gen i, gen j, gen_injective.ne hne,
          fun h => hb ((adj_gen i j).1 h), by simp⟩)
    · refine Or.inr ?_
      simp only [Set.mem_singleton_iff, map_pow, map_mul, FreeGroup.map.of]
      rfl)

theorem toOpen_x (i : Fin 12) : toOpen (x i) = PresentedGroup.of (gen i) :=
  PresentedGroup.toGroup.of _

noncomputable def fromOpen : MonsterY443 →* Y443 :=
  PresentedGroup.toGroup (f := fun s => x (num s)) (by
    rintro r (((⟨s, rfl⟩ | ⟨s, t, hst, rfl⟩) | ⟨s, t, hne, hst, rfl⟩) | hr)
    · rw [pow_two, map_mul, FreeGroup.lift_apply_of, x_mul_self]
    · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
      rw [← gen_num s, ← gen_num t, adj_gen] at hst
      refine x_adj (fun h => ?_) ((adjacent_iff_adjB _ _).2 hst)
      rw [h, adjB_irrefl] at hst
      exact Bool.false_ne_true hst
    · simp only [map_pow, map_mul, FreeGroup.lift_apply_of]
      rw [← gen_num s, ← gen_num t, adj_gen] at hst
      exact x_nadj (num_injective.ne hne) (fun h => hst ((adjacent_iff_adjB _ _).1 h))
    · rw [Set.mem_singleton_iff] at hr
      subst hr
      simp only [monsterY443SpiderWord, monsterY443Node, map_pow, map_mul,
        FreeGroup.lift_apply_of]
      exact spider)

theorem fromOpen_of (s : MonsterY443Gen) : fromOpen (PresentedGroup.of s) = x (num s) :=
  PresentedGroup.toGroup.of _

noncomputable def mulEquiv : Y443 ≃* MonsterY443 :=
  MonoidHom.toMulEquiv toOpen fromOpen
    (PresentedGroup.ext fun i => by
      rw [MonoidHom.comp_apply, toOpen_x, fromOpen_of, num_gen, MonoidHom.id_apply])
    (PresentedGroup.ext fun s => by
      rw [MonoidHom.comp_apply, fromOpen_of, toOpen_x, gen_num, MonoidHom.id_apply])

noncomputable def commutatorMulEquiv : commutator Y443 ≃* MonsterY443Derived :=
  (mulEquiv.subgroupMap (commutator Y443)).trans (MulEquiv.subgroupCongr (by
    have h : (⊤ : Subgroup Y443).map (mulEquiv : Y443 →* MonsterY443) = ⊤ :=
      Subgroup.map_top_of_surjective _ mulEquiv.surjective
    rw [commutator, Subgroup.map_commutator, h]
    rfl))

end CFSG.Sporadic.Bridge.Y443
