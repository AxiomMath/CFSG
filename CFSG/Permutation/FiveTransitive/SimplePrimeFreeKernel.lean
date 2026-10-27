module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Index

public section

namespace CFSG

namespace FiveTransitive.SimplePrimeFreeKernel

theorem ker_le
    {L A B : Type} [Group L] [Group A] [Group B] [Finite L] [Finite A]
    [IsSimpleGroup A] (f : L →* A) (hf : Function.Surjective f)
    (g : L →* B) (p : ℕ) (hp : p ∣ Nat.card A)
    (hfree : ¬ p ∣ Nat.card g.ker) : g.ker ≤ f.ker := by
  let T := g.ker.map f
  let _ : T.Normal := (inferInstance : g.ker.Normal).map f hf
  rcases (inferInstance : T.Normal).eq_bot_or_eq_top with hbot | htop
  · intro x hx
    have hm : f x ∈ T := ⟨x,hx,rfl⟩
    rwa [hbot,Subgroup.mem_bot] at hm
  · have hd : Nat.card T ∣ Nat.card g.ker := g.ker.card_map_dvd f
    rw [htop,Subgroup.card_top] at hd
    exact (hfree (hp.trans hd)).elim

theorem exists_surjective_range_factor
    {L A B : Type} [Group L] [Group A] [Group B]
    (f : L →* A) (hf : Function.Surjective f) (g : L →* B)
    (hker : g.ker ≤ f.ker) :
    ∃ r : g.range →* A, Function.Surjective r ∧ ∀ x : L, r (g.rangeRestrict x) = f x := by
  classical
  let u := g.rangeRestrict
  have hu : Function.Surjective u := g.rangeRestrict_surjective
  have hk : u.ker ≤ f.ker := by
    intro x hx
    apply hker
    exact congrArg Subtype.val hx
  let r : g.range →* A := u.liftOfRightInverse hu.hasRightInverse.choose
    hu.hasRightInverse.choose_spec ⟨f,hk⟩
  have hr (x : L) : r (u x) = f x :=
    u.liftOfRightInverse_comp_apply hu.hasRightInverse.choose hu.hasRightInverse.choose_spec ⟨f,hk⟩ x
  refine ⟨r,?_,hr⟩
  intro a
  obtain ⟨x,hx⟩ := hf a
  exact ⟨u x,(hr x).trans hx⟩

end FiveTransitive.SimplePrimeFreeKernel

end CFSG
