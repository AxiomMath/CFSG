module

public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.EquivariantFiberOrbits

open MulAction

@[expose] def fiber
    {G T B : Type*} [Group G] [MulAction G T] [MulAction G B]
    (f : T → B) (hf : ∀ (g : G) (t : T), f (g • t) = g • f t) (b : B) :
    SubMulAction (stabilizer G b) T where
  carrier := {t | f t = b}
  smul_mem' := by
    intro g t ht
    change f ((g : G) • t) = b
    rw [hf, ht]
    exact g.property

private theorem rel_iff
    {G T B : Type*} [Group G] [MulAction G T] [MulAction G B]
    (f : T → B) (hf : ∀ (g : G) (t : T), f (g • t) = g • f t) (b : B)
    (x y : fiber f hf b) :
    orbitRel (stabilizer G b) (fiber f hf b) x y ↔
      orbitRel G T x.val y.val := by
  simp only [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.val, congrArg Subtype.val hg⟩
  · rintro ⟨g, hg⟩
    have hgb : g • b = b := by
      have h := congrArg f hg
      rw [hf, y.property, x.property] at h
      exact h
    exact ⟨⟨g, hgb⟩, Subtype.ext hg⟩

private noncomputable def orbitEquiv
    {G T B : Type*} [Group G] [MulAction G T] [MulAction G B]
    [IsPretransitive G B]
    (f : T → B) (hf : ∀ (g : G) (t : T), f (g • t) = g • f t) (b : B) :
    orbitRel.Quotient (stabilizer G b) (fiber f hf b) ≃ orbitRel.Quotient G T := by
  let qmap := Quotient.map (fun x : fiber f hf b => x.val)
    (fun x y h => (rel_iff f hf b x y).mp h)
  apply Equiv.ofBijective qmap
  constructor
  · intro x y
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
        intro h
        apply Quotient.sound
        exact (rel_iff f hf b x y).mpr (Quotient.exact h)
  · intro z
    induction z using Quotient.inductionOn with | _ t =>
      obtain ⟨g, hg⟩ := exists_smul_eq G (f t) b
      have hmem : f (g • t) = b := by rw [hf, hg]
      refine ⟨Quotient.mk'' (⟨g • t, hmem⟩ : fiber f hf b), ?_⟩
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨g, rfl⟩)

theorem card_orbits_eq
    {G T B : Type*} [Group G] [MulAction G T] [MulAction G B]
    [IsPretransitive G B]
    (f : T → B) (hf : ∀ (g : G) (t : T), f (g • t) = g • f t) (b : B) :
    Nat.card (orbitRel.Quotient G T) =
      Nat.card (orbitRel.Quotient (stabilizer G b) (fiber f hf b)) :=
  (Nat.card_congr (orbitEquiv f hf b)).symm

end FiveTransitive.EquivariantFiberOrbits

end CFSG
