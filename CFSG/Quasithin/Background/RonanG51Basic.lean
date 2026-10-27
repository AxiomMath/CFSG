module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.GoldschmidtG52Reps
public import CFSG.Sporadic.Schreier.J4SSylowBase
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.RonanG51

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.Quasithin.H13.A6.G52

abbrev D (i : Fin 4) : Type := Fin (![1, 4, 4, 16] i) → ZMod 2

theorem addSubgroup_eq_bot_or_top_of_isIrreducible {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (τ : Representation (ZMod 2) G V) (hτ : τ.IsIrreducible)
    (S : AddSubgroup V) (hS : ∀ (g : G) (m : V), m ∈ S → τ g m ∈ S) : S = ⊥ ∨ S = ⊤ := by
  let P : Subrepresentation τ := ⟨S.toZModSubmodule 2, fun g v hv => hS g v hv⟩
  have hmem : ∀ x : V, x ∈ S ↔ x ∈ P.toSubmodule := fun x => Iff.rfl
  rcases hτ.eq_bot_or_eq_top P with h | h
  · have h' : P.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    left
    ext x
    rw [AddSubgroup.mem_bot, hmem x, h', Submodule.mem_bot]
  · have h' : P.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
    right
    ext x
    simp only [AddSubgroup.mem_top, iff_true]
    rw [hmem x, h']
    exact Submodule.mem_top

theorem isIrreducible_of_addSubgroup_bot_or_top {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [Nontrivial V] (τ : Representation (ZMod 2) G V)
    (h : ∀ S : AddSubgroup V, (∀ (g : G) (m : V), m ∈ S → τ g m ∈ S) → S = ⊥ ∨ S = ⊤) :
    Representation.IsIrreducible τ := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule hbt)
  · rcases h P.toSubmodule.toAddSubgroup (fun g m hm => P.apply_mem_toSubmodule g hm) with hP | hP
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (Submodule.toAddSubgroup_injective (hP.trans Submodule.bot_toAddSubgroup.symm)))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (Submodule.toAddSubgroup_injective (hP.trans Submodule.top_toAddSubgroup.symm)))

section


theorem a6_irred (i : Fin 4) :
    Nontrivial (D i) ∧ ∀ S : AddSubgroup (D i),
      (∀ (g : ↥(alternatingGroup (Fin 6))) (m : D i), m ∈ S → a6BinaryRep i g m ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
  haveI := isIrreducible_a6BinaryRep i
  exact ⟨nontrivial_of_isIrreducible (a6BinaryRep i), fun S hS =>
    addSubgroup_eq_bot_or_top_of_isIrreducible (a6BinaryRep i) (isIrreducible_a6BinaryRep i) S hS⟩

theorem mrep_irred (i : Fin 4) :
    Nontrivial (D i) ∧ ∀ S : AddSubgroup (D i),
      (∀ (g : Equiv.Perm (Fin 6)) (m : D i), m ∈ S → Mrep i g m ∈ S) → S = ⊥ ∨ S = ⊤ := by
  haveI := isIrreducible_Mrep i
  exact ⟨nontrivial_of_isIrreducible (Mrep i), fun S hS =>
    addSubgroup_eq_bot_or_top_of_isIrreducible (Mrep i) (isIrreducible_Mrep i) S hS⟩

theorem card_D (i : Fin 4) : Nat.card (D i) = 2 ^ (![1, 4, 4, 16] i) := by
  rw [D, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem a6_trivial (g : ↥(alternatingGroup (Fin 6))) (m : D 0) : a6BinaryRep 0 g m = m := by
  have h : ∀ x : Fin 1 → ZMod 2, matrixBaseChange (RingHom.id (ZMod 2)) rep1 g x = x := by
    intro x
    rw [matrixBaseChange_apply]
    simp [rep1]
  exact h m

theorem a6_not_iso (i j : Fin 4) (hij : i ≠ j) :
    ¬ ∃ f : D i ≃+ D j, ∀ (g : ↥(alternatingGroup (Fin 6))) (m : D i),
      f (a6BinaryRep i g m) = a6BinaryRep j g (f m) := by
  rintro ⟨f, hf⟩
  let e : D i ≃ₗ[ZMod 2] D j :=
    { f.toAddMonoidHom.toZModLinearMap 2 with
      invFun := f.symm
      left_inv := f.left_inv
      right_inv := f.right_inv }
  have he : ∀ g : ↥(alternatingGroup (Fin 6)),
      e.toLinearMap ∘ₗ a6BinaryRep i g = a6BinaryRep j g ∘ₗ e.toLinearMap :=
    fun g => LinearMap.ext fun m => hf g m
  haveI := isEmpty_equiv_a6BinaryRep i j hij
  exact IsEmpty.false (Representation.Equiv.mk e he)

theorem a6_complete {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
    (σ : Representation (ZMod 2) (↥(alternatingGroup (Fin 6))) W)
    (hS : ∀ S : AddSubgroup W, (∀ (g : ↥(alternatingGroup (Fin 6))) (m : W), m ∈ S → σ g m ∈ S) →
      S = ⊥ ∨ S = ⊤) :
    ∃ i : Fin 4, ∃ f : W ≃+ D i, ∀ (g : ↥(alternatingGroup (Fin 6))) (m : W),
      f (σ g m) = a6BinaryRep i g (f m) := by
  haveI : σ.IsIrreducible := isIrreducible_of_addSubgroup_bot_or_top σ hS
  obtain ⟨-, i, ⟨e⟩⟩ := a6BinaryRep_complete W σ this
  exact ⟨i, e.toLinearEquiv.toAddEquiv, fun g m =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g m⟩

theorem a6_three_iso_mrep :
    ∃ f : D 3 ≃+ D 3, ∀ (g : ↥(alternatingGroup (Fin 6))) (m : D 3),
      f (a6BinaryRep 3 g m) = Mrep 3 (g : Equiv.Perm (Fin 6)) (f m) := by
  let e := (MrepRestrictEquiv 3).symm
  exact ⟨e.toLinearEquiv.toAddEquiv, fun g m =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g m⟩

end

end CFSG.Quasithin.RonanG51
