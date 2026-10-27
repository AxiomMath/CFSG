module

public import CFSG.Quasithin.Background.Harris.Alt6.Heart
public import CFSG.CharacterTheory.SteinbergBYAlternatingSixModular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.Open CFSG.CharacterTheory.SteinbergBY AlternatingSix Equiv Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def repA6 (L : Subgroup (GLV V)) (e : ↥L ≃* alternatingGroup (Fin 6)) :
    Representation (ZMod 2) (alternatingGroup (Fin 6)) V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom)

theorem repA6_apply (L : Subgroup (GLV V)) (e : ↥L ≃* alternatingGroup (Fin 6))
    (g : alternatingGroup (Fin 6)) (v : V) : repA6 L e g v = ((e.symm g : ↥L) : GLV V) v := rfl

theorem repA6_isIrreducible {L : Subgroup (GLV V)} (e : ↥L ≃* alternatingGroup (Fin 6))
    (hL : CFSG.Quasithin.G11.IsIrr L ⊤) : (repA6 L e).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  obtain ⟨-, hlt, hirr⟩ := hL
  refine ⟨?_, fun U hU => ?_⟩
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt hlt
    exact ⟨⟨v, 0, fun h => hv (h ▸ Submodule.zero_mem _)⟩⟩
  · have hinv : CFSG.Quasithin.G11.Invariant L U := fun l hl u hu => by
      have := hU (e ⟨l, hl⟩) u hu
      simpa [repA6_apply] using this
    exact hirr U hinv bot_le le_top

theorem a6_ne_one : (⟨cyc3, cyc3_mem⟩ : alternatingGroup (Fin 6)) ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  decide +kernel

theorem exists_heart_equiv [Finite V] {L : Subgroup (GLV V)}
    (hL : CFSG.Quasithin.G11.IsIrr L ⊤) (e : ↥L ≃* alternatingGroup (Fin 6))
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2) V = 4 ∧ ∃ T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2),
      ((∀ (l : ↥L) (v : V), T ((l : GLV V) v) = heartHom (e l : Perm (Fin 6)) *ᵥ T v) ∨
       (∀ (l : ↥L) (v : V),
          T ((l : GLV V) v) = heartHom (totalPermHom (e l : Perm (Fin 6))) *ᵥ T v)) := by
  obtain ⟨-, i, ⟨φ⟩⟩ := a6BinaryRep_complete V (repA6 L e) (repA6_isIrreducible e hL)
  have hrank : Module.finrank (ZMod 2) V = ![1, 4, 4, 16] i := by
    rw [LinearEquiv.finrank_eq φ.toLinearEquiv]
    simp
  have hφ : ∀ g v, φ (repA6 L e g v) = a6BinaryRep i g (φ v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g v
  have hlift : ∀ (l : ↥L) (v : V), (repA6 L e (e l)) v = (l : GLV V) v := fun l v => by
    rw [repA6_apply, MulEquiv.symm_apply_apply]
  fin_cases i
  · exfalso
    have h1 : ∀ g v, repA6 L e g v = v := fun g v => by
      apply φ.toLinearEquiv.injective
      show φ (repA6 L e g v) = φ v
      rw [hφ]
      show (rep1 g).map (RingHom.id (ZMod 2)) *ᵥ φ v = φ v
      simp [rep1]
    apply a6_ne_one
    have h2 : ((e.symm ⟨cyc3, cyc3_mem⟩ : ↥L) : GLV V) = 1 :=
      LinearEquiv.ext fun v => by rw [← repA6_apply, h1]; rfl
    have h3 : e.symm ⟨cyc3, cyc3_mem⟩ = 1 := Subtype.ext h2
    simpa using congrArg e h3
  · let T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) := φ.toLinearEquiv
    refine ⟨by simpa using hrank, T, Or.inl fun l v => ?_⟩
    have := hφ (e l) v
    rw [hlift] at this
    show φ ((l : GLV V) v) = _
    rw [this]
    show (rep4a (e l)).map (RingHom.id (ZMod 2)) *ᵥ φ v = _
    simp [rep4a]
    rfl
  · let T : V ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) := φ.toLinearEquiv
    refine ⟨by simpa using hrank, T, Or.inr fun l v => ?_⟩
    have := hφ (e l) v
    rw [hlift] at this
    show φ ((l : GLV V) v) = _
    rw [this]
    show (rep4b (e l)).map (RingHom.id (ZMod 2)) *ᵥ φ v = _
    simp [rep4b]
    rfl
  · exfalso
    simp at hrank
    omega

end CFSG.Quasithin.G11.Harris.Alt6
