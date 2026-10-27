module

public import CFSG.CharacterTheory.SteinbergBYAlternatingSixModular

public section

namespace CFSG.Quasithin.H13.A6.G52

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.AlternatingSix
  CFSG.CharacterTheory.SteinbergBY.FieldFour Equiv Matrix

@[expose] def kronHom : Perm (Fin 6) →* Matrix (Fin 16) (Fin 16) (ZMod 2) where
  toFun σ := kron16 (heartHom σ) (heartHom (totalPermHom σ))
  map_one' := by simp only [map_one]; exact kron16_one
  map_mul' σ τ := by simp only [map_mul]; exact kron16_mul _ _ _ _

@[expose] noncomputable def homM : ∀ i : Fin 4,
    Perm (Fin 6) →* Matrix (Fin (![1, 4, 4, 16] i)) (Fin (![1, 4, 4, 16] i)) (ZMod 2)
  | 0 => 1
  | 1 => heartHom
  | 2 => heartHom.comp totalPermHom
  | 3 => kronHom

@[expose] noncomputable def Mrep (i : Fin 4) :
    Representation (ZMod 2) (Perm (Fin 6)) (Fin (![1, 4, 4, 16] i) → ZMod 2) :=
  matrixBaseChange (RingHom.id (ZMod 2)) (homM i)

theorem isIrreducible_of_comp {k G H V : Type*} [Field k] [Group G] [Group H] [AddCommGroup V]
    [Module k V] (f : H →* G) (ρ : Representation k G V)
    (h : Representation.IsIrreducible (ρ.comp f)) : Representation.IsIrreducible ρ := by
  let res : Subrepresentation ρ → Subrepresentation (ρ.comp f) := fun P =>
    ⟨P.toSubmodule, fun g _ hv => P.apply_mem_toSubmodule (f g) hv⟩
  have hres : ∀ P Q : Subrepresentation ρ, res P = res Q → P = Q := fun P Q hPQ =>
    Subrepresentation.toSubmodule_injective
      (congrArg (fun x : Subrepresentation (ρ.comp f) => x.toSubmodule) hPQ)
  have hbot : res ⊥ = ⊥ := rfl
  have htop : res ⊤ = ⊤ := rfl
  refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun P => ?_ }
  · have := congrArg res hbt
    rw [hbot, htop] at this
    exact IsSimpleOrder.bot_ne_top this
  · rcases h.eq_bot_or_eq_top (res P) with hP | hP
    · exact Or.inl (hres _ _ (hP.trans hbot.symm))
    · exact Or.inr (hres _ _ (hP.trans htop.symm))

section Restrict

noncomputable def kronRestrictEquiv :
    Representation.Equiv ((Mrep 3).comp (alternatingGroup (Fin 6)).subtype) (a6BinaryRep 3) := by
  let N : alternatingGroup (Fin 6) →* Matrix (Fin 16) (Fin 16) (ZMod 2) :=
    kronHom.comp (alternatingGroup (Fin 6)).subtype
  have hT : ∀ g, basis8 * rep8a g = (N g).map ofPrime * basis8 := fun g =>
    (kron16F_mul_basis8 g).symm
  let f : (restrictFour rep8a).IntertwiningMap (matrixBaseChange (RingHom.id (ZMod 2)) N) :=
    realPartIntertwining rep8a N basis8 hT
  have hf0 : f ≠ 0 := by
    intro h
    have h1 : realPartMap basis8 = 0 := congrArg Representation.IntertwiningMap.toLinearMap h
    have h2 := realPartMap_eq_zero basis8 h1
    have h3 := proj8_mul_basis8
    rw [h2, Matrix.mul_zero] at h3
    exact zero_ne_one h3
  haveI := isIrreducible_restrictFour_rep8a
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf0
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank realEquiv.finrank_eq).mp hinj
  let e : (Fin 8 → FieldFour) ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
    LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩
  let φ : Representation.Equiv (restrictFour rep8a)
      (matrixBaseChange (RingHom.id (ZMod 2)) N) :=
    Representation.Equiv.mk e fun g => f.isIntertwining' g
  exact ((transportRepEquiv realEquiv (restrictFour rep8a)).symm.trans φ).symm

noncomputable def MrepRestrictEquiv : ∀ i : Fin 4,
    Representation.Equiv ((Mrep i).comp (alternatingGroup (Fin 6)).subtype) (a6BinaryRep i)
  | 0 => Representation.Equiv.refl _
  | 1 => Representation.Equiv.refl _
  | 2 => Representation.Equiv.refl _
  | 3 => kronRestrictEquiv

theorem isIrreducible_Mrep (i : Fin 4) : Representation.IsIrreducible (Mrep i) :=
  isIrreducible_of_comp (alternatingGroup (Fin 6)).subtype (Mrep i)
    (isIrreducible_of_equiv (MrepRestrictEquiv i).symm (isIrreducible_a6BinaryRep i))

end Restrict

end CFSG.Quasithin.H13.A6.G52
