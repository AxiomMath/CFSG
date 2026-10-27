
module

public import CFSG.Monster.B.TwoA.Base.PetersenB
public import CFSG.Monster.B.TwoA.Base.PetersenData
public import CFSG.Monster.B.TwoA.Base.Space34ABase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

@[expose] def aut4 (c : Fin 15) : AutPerm := ⟨perm4 c, perm4_mem c⟩

@[expose] def aut5 (d : Fin 10) : AutPerm := ⟨perm5 d, perm5_mem d⟩

theorem aut4_mem_Ppair (c : Fin 15) : aut4 c ∈ Ppair :=
  (mem_Ppair_iff _).2 (.inl ⟨perm4_fix c 0 (by decide), perm4_fix c 1 (by decide)⟩)

theorem aut5_mem_Ppair (d : Fin 10) : aut5 d ∈ Ppair :=
  (mem_Ppair_iff _).2 (.inl ⟨perm5_fix d 0 (by decide), perm5_fix d 1 (by decide)⟩)

@[expose] def UR4
    (c : Fin 15) : Submodule (ZMod 2) (Wv v0) :=
  U3.map (wAct v0 (kmon (aut4 c) (aut4_mem_Ppair c)))

@[expose] def UR5
    (d : Fin 10) : Submodule (ZMod 2) (Wv v0) :=
  U4.map (wAct v0 (kmon (aut5 d) (aut5_mem_Ppair d)))

@[expose] def Y4
    (c : Fin 15) : Subgroup Dfull := EU (UR4 c)

@[expose] def Y5
    (d : Fin 10) : Subgroup Dfull := EU (UR5 d)

abbrev PetVert : Type := {s : Finset ℕ // s ∈ twoSubsets}

abbrev PetEdge : Type :=
  {e : Finset PetVert // e.card = 2 ∧ ∀ a ∈ e, ∀ b ∈ e, a ≠ b → Disjoint a.1 b.1}

@[expose] def vlab (d : Fin 10) : PetVert := ⟨tetLab d, tetLab_mem d⟩

theorem vlab_injective : Function.Injective vlab :=
  fun _ _ h => tetLab_injective (congrArg Subtype.val h)

theorem vlab_bijective : Function.Bijective vlab := by
  refine ⟨vlab_injective, fun s => ?_⟩
  obtain ⟨d, hd⟩ := exists_tetLab s.1 s.2
  exact ⟨d, Subtype.ext hd⟩

@[expose] def edgeLab (c : Fin 15) : PetEdge :=
  ⟨{vlab (ev4 c 0), vlab (ev4 c 1)}, by
    rw [Finset.card_pair (vlab_injective.ne (ev4_disjoint c).1)], by
    intro a ha b hb hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact (ev4_disjoint c).2
    · exact (ev4_disjoint c).2.symm
    · exact absurd rfl hab⟩

theorem edgeLab_injective : Function.Injective edgeLab := by
  intro c c' h
  have h1 := congrArg Subtype.val h
  change ({vlab (ev4 c 0), vlab (ev4 c 1)} : Finset PetVert) =
    {vlab (ev4 c' 0), vlab (ev4 c' 1)} at h1
  have h2 : (({ev4 c 0, ev4 c 1} : Finset (Fin 10))).image vlab =
      (({ev4 c' 0, ev4 c' 1} : Finset (Fin 10))).image vlab := by
    rw [Finset.image_insert, Finset.image_singleton, Finset.image_insert,
      Finset.image_singleton]
    exact h1
  exact ev4_injective c c' (Finset.image_injective vlab_injective h2)

theorem edgeLab_surjective : Function.Surjective edgeLab := by
  intro e
  obtain ⟨x, y, hxy, hexy⟩ := Finset.card_eq_two.1 e.2.1
  obtain ⟨d, rfl⟩ := vlab_bijective.2 x
  obtain ⟨d', rfl⟩ := vlab_bijective.2 y
  have hdisj : Disjoint (tetLab d) (tetLab d') :=
    e.2.2 _ (by rw [hexy]; simp) _ (by rw [hexy]; simp) hxy
  obtain ⟨c, hc | hc⟩ := exists_ev4 d d' (fun h => hxy (by rw [h])) hdisj
  · refine ⟨c, Subtype.ext ?_⟩
    change ({vlab (ev4 c 0), vlab (ev4 c 1)} : Finset PetVert) = e.1
    rw [hexy, hc.1, hc.2]
  · refine ⟨c, Subtype.ext ?_⟩
    change ({vlab (ev4 c 0), vlab (ev4 c 1)} : Finset PetVert) = e.1
    rw [hexy, hc.1, hc.2, Finset.pair_comm]

end CFSG.Monster.B.TwoA
