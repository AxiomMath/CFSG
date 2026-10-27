module

public import Mathlib.Data.FunLike.Fintype
public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.RingTheory.IntegralDomain
public import CFSG.Quasithin.Background.A1cModuleDefs

public section

namespace CFSG.Quasithin

namespace XMod

section Aut

variable (A : Type*) [Group A] (P : Type*) [CommGroup P] [MulDistribMulAction A P]

@[expose] def eqvAut : Subgroup (MulAut P) where
  carrier := {φ | ∀ (a : A) (p : P), φ (a • p) = a • φ p}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {φ ψ} hφ hψ a p => by
    change φ (ψ (a • p)) = a • φ (ψ p)
    rw [hψ a p, hφ a (ψ p)]
  inv_mem' := fun {φ} hφ a p => by
    change φ.symm (a • p) = a • φ.symm p
    apply φ.injective
    rw [MulEquiv.apply_symm_apply, hφ a (φ.symm p), MulEquiv.apply_symm_apply]

@[expose] def actEnd (a : A) : AddMonoid.End (Additive P) :=
  MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom P a)

@[expose] def eqvEnd : Subring (AddMonoid.End (Additive P)) :=
  Subring.centralizer (Set.range (actEnd A P))

variable {A P}

@[expose] def toMonoidEnd (f : AddMonoid.End (Additive P)) : P →* P :=
  MonoidHom.toAdditive.symm f

theorem toMonoidEnd_apply (f : AddMonoid.End (Additive P)) (p : P) :
    toMonoidEnd f p = Additive.toMul (f (Additive.ofMul p)) := rfl

theorem mem_eqvAut_iff {φ : MulAut P} :
    φ ∈ eqvAut A P ↔ ∀ (a : A) (p : P), φ (a • p) = a • φ p := Iff.rfl

theorem mem_eqvEnd_iff {f : AddMonoid.End (Additive P)} :
    f ∈ eqvEnd A P ↔ ∀ (a : A) (p : P), toMonoidEnd f (a • p) = a • toMonoidEnd f p := by
  rw [eqvEnd, Subring.mem_centralizer_iff]
  constructor
  · intro h a p
    have := congrArg (fun g : AddMonoid.End (Additive P) => g (Additive.ofMul p))
      (h (actEnd A P a) ⟨a, rfl⟩)
    exact this.symm
  · rintro h _ ⟨a, rfl⟩
    ext p
    exact (h a (Additive.toMul p)).symm

theorem toMonoidEnd_toAdditive (g : P →* P) : toMonoidEnd (MonoidHom.toAdditive g) = g := rfl

theorem eqvEnd_isUnit_or_eq_zero (hsimple : IsIrrSec A (⊥ : Subgroup P) ⊤)
    (e : eqvEnd A P) : IsUnit e ∨ e = 0 := by
  by_cases he : e = 0
  · exact Or.inr he
  left
  have hf : ∀ (a : A) (p : P), toMonoidEnd (e : AddMonoid.End (Additive P)) (a • p) =
      a • toMonoidEnd (e : AddMonoid.End (Additive P)) p := mem_eqvEnd_iff.1 e.2
  set f : P →* P := toMonoidEnd (e : AddMonoid.End (Additive P)) with hfdef
  have hfne : f ≠ 1 := by
    intro h1
    apply he
    apply Subtype.ext
    apply AddMonoidHom.ext
    intro p
    have h2 : f (Additive.toMul p) = 1 := by rw [h1]; rfl
    exact Additive.toMul.injective h2
  have hker : IsInv A f.ker := by
    intro a l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    rw [hf, hl, smul_one]
  have hrange : IsInv A f.range := by
    rintro a _ ⟨p, rfl⟩
    exact ⟨a • p, hf a p⟩
  have hinj : Function.Injective f := by
    rcases hsimple.2 f.ker hker bot_le le_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff f).1 h
    · exfalso
      apply hfne
      ext p
      have : p ∈ f.ker := by rw [h]; trivial
      exact MonoidHom.mem_ker.1 this
  have hsurj : Function.Surjective f := by
    rcases hsimple.2 f.range hrange bot_le le_top with h | h
    · exfalso
      apply hfne
      ext p
      have : f p ∈ f.range := ⟨p, rfl⟩
      rw [h] at this
      exact Subgroup.mem_bot.1 this
    · exact MonoidHom.range_eq_top.1 h
  let g : P ≃* P := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hg : ∀ (a : A) (p : P), g.symm (a • p) = a • g.symm p := by
    intro a p
    apply g.injective
    rw [MulEquiv.apply_symm_apply]
    change _ = f (a • g.symm p)
    rw [hf]
    change _ = a • g (g.symm p)
    rw [MulEquiv.apply_symm_apply]
  let e' : AddMonoid.End (Additive P) := MonoidHom.toAdditive g.symm.toMonoidHom
  have hmem : e' ∈ eqvEnd A P := by
    rw [mem_eqvEnd_iff]
    intro a p
    exact hg a p
  refine isUnit_iff_exists.2 ⟨⟨_, hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    apply AddMonoidHom.ext
    intro p
    apply Additive.toMul.injective
    change f (g.symm (Additive.toMul p)) = Additive.toMul p
    exact g.apply_symm_apply _
  · apply Subtype.ext
    apply AddMonoidHom.ext
    intro p
    apply Additive.toMul.injective
    change g.symm (f (Additive.toMul p)) = Additive.toMul p
    exact g.symm_apply_apply _

theorem nontrivial_of_isIrrSec_bot_top (hsimple : IsIrrSec A (⊥ : Subgroup P) ⊤) :
    ∃ p : P, p ≠ 1 := by
  by_contra h
  push Not at h
  have : (⊤ : Subgroup P) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun x _ => h x
  exact hsimple.1.ne this.symm

theorem nontrivial_eqvEnd (hsimple : IsIrrSec A (⊥ : Subgroup P) ⊤) :
    Nontrivial ↥(eqvEnd A P) := by
  obtain ⟨p, hp⟩ := nontrivial_of_isIrrSec_bot_top hsimple
  refine ⟨⟨1, 0, fun h => hp ?_⟩⟩
  have h1 := congrArg (fun e : ↥(eqvEnd A P) => (e : AddMonoid.End (Additive P)) (Additive.ofMul p)) h
  exact Additive.ofMul.injective h1

theorem eqvEnd_two_eq_zero (hP : ∀ p : P, p ^ 2 = 1) : (2 : ↥(eqvEnd A P)) = 0 := by
  rw [← one_add_one_eq_two]
  apply Subtype.ext
  apply AddMonoidHom.ext
  intro p
  apply Additive.toMul.injective
  change Additive.toMul p * Additive.toMul p = 1
  rw [← sq]
  exact hP _

variable (A P) in
@[instance_reducible] noncomputable def eqvEndDivisionRing (hsimple : IsIrrSec A (⊥ : Subgroup P) ⊤) :
    DivisionRing ↥(eqvEnd A P) :=
  haveI := nontrivial_eqvEnd hsimple
  DivisionRing.ofIsUnitOrEqZero (eqvEnd_isUnit_or_eq_zero hsimple)

theorem finite_eqvEnd [Finite P] : Finite ↥(eqvEnd A P) := by
  have : Finite (AddMonoid.End (Additive P)) := FunLike.finite (Additive P →+ Additive P)
  infer_instance

theorem eqvEnd_isField_charTwo [Finite P] (hP : ∀ p : P, p ^ 2 = 1)
    (hsimple : IsIrrSec A (⊥ : Subgroup P) ⊤) :
    Finite ↥(eqvEnd A P) ∧ IsField ↥(eqvEnd A P) ∧ CharP ↥(eqvEnd A P) 2 := by
  have := nontrivial_eqvEnd hsimple
  have hfin := finite_eqvEnd (A := A) (P := P)
  refine ⟨hfin, ?_, ?_⟩
  · let : DivisionRing ↥(eqvEnd A P) := eqvEndDivisionRing A P hsimple
    exact (littleWedderburn ↥(eqvEnd A P)).toIsField
  · rw [CharP.charP_iff_prime_eq_zero Nat.prime_two]
    exact eqvEnd_two_eq_zero hP

theorem isCyclic_of_injective_eqvEnd [Finite P] (hsimple : IsIrrSec A (⊥ : Subgroup P) ⊤)
    {Γ : Type*} [Group Γ] [Finite Γ] (f : Γ →* ↥(eqvEnd A P)) (hf : Function.Injective f) :
    IsCyclic Γ := by
  have := nontrivial_eqvEnd hsimple
  have hfin := finite_eqvEnd (A := A) (P := P)
  let : DivisionRing ↥(eqvEnd A P) := eqvEndDivisionRing A P hsimple
  exact isCyclic_of_injective_ringHom (R := ↥(eqvEnd A P)) f hf

end Aut

end XMod

end CFSG.Quasithin
