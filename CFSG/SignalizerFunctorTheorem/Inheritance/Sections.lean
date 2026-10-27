module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic
public import Mathlib.Order.CompletePartialOrder

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem

namespace IsSectionOf

variable {X Y Z : Type*} [Group X] [Group Y] [Group Z]

theorem of_surjective (f : Y →* X) (hf : Function.Surjective f) : IsSectionOf X Y :=
  ⟨⊤, f.comp (⊤ : Subgroup Y).subtype, fun x => by
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨⟨y, trivial⟩, rfl⟩⟩

theorem refl (X : Type*) [Group X] : IsSectionOf X X :=
  of_surjective (MonoidHom.id X) Function.surjective_id

theorem of_mulEquiv (e : Y ≃* X) : IsSectionOf X Y :=
  of_surjective e.toMonoidHom e.surjective

theorem of_subgroup (K : Subgroup Y) : IsSectionOf K Y :=
  ⟨K, MonoidHom.id K, Function.surjective_id⟩

theorem of_injective (h : IsSectionOf X Y) (f : Y →* Z) (hf : Function.Injective f) :
    IsSectionOf X Z := by
  obtain ⟨K, g, hg⟩ := h
  refine ⟨K.map f, g.comp (K.equivMapOfInjective f hf).symm.toMonoidHom, fun x => ?_⟩
  obtain ⟨k, rfl⟩ := hg x
  exact ⟨K.equivMapOfInjective f hf k, by simp⟩

theorem trans (h₁ : IsSectionOf X Y) (h₂ : IsSectionOf Y Z) : IsSectionOf X Z := by
  obtain ⟨K₁, f₁, hf₁⟩ := h₁
  obtain ⟨K₂, f₂, hf₂⟩ := h₂
  have hsurj : Function.Surjective (f₂.subgroupComap K₁) := by
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := hf₂ y
    exact ⟨⟨z, hy⟩, rfl⟩
  have h : IsSectionOf X K₂ := ⟨K₁.comap f₂, f₁.comp (f₂.subgroupComap K₁), hf₁.comp hsurj⟩
  exact h.of_injective K₂.subtype K₂.subtype_injective

theorem of_ker_le {K : Type*} [Group K] (f : K →* X) (hf : Function.Surjective f) (g : K →* Y)
    (hg : g.ker ≤ f.ker) : IsSectionOf X Y := by
  have hsurj : Function.Surjective g.rangeRestrict := g.rangeRestrict_surjective
  have hle : g.rangeRestrict.ker ≤ f.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let h : g.range →* X := MonoidHom.liftOfRightInverse g.rangeRestrict (Function.surjInv hsurj)
    (Function.rightInverse_surjInv hsurj) ⟨f, hle⟩
  refine ⟨g.range, h, fun x => ?_⟩
  obtain ⟨k, rfl⟩ := hf x
  exact ⟨g.rangeRestrict k, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩

theorem subsingleton (h : IsSectionOf X Y) [Subsingleton Y] : Subsingleton X := by
  obtain ⟨K, f, hf⟩ := h
  exact hf.subsingleton

theorem commutative (h : IsSectionOf X Y) (hY : ∀ a b : Y, a * b = b * a) (x y : X) :
    x * y = y * x := by
  obtain ⟨K, f, hf⟩ := h
  obtain ⟨k₁, rfl⟩ := hf x
  obtain ⟨k₂, rfl⟩ := hf y
  rw [← map_mul, ← map_mul]
  exact congrArg f (Subtype.ext (hY _ _))

theorem of_hom [IsSimpleGroup X] (h : IsSectionOf X Y) (ρ : Y →* Z) :
    IsSectionOf X ρ.ker ∨ IsSectionOf X Z := by
  obtain ⟨K, f, hf⟩ := h
  let g : K →* Z := ρ.comp K.subtype
  have hnormal : (g.ker.map f).Normal := (MonoidHom.normal_ker g).map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (g.ker.map f) with hbot | htop
  · exact Or.inr (of_ker_le f hf g ((Subgroup.map_eq_bot_iff _).mp hbot))
  · left
    let f₁ : g.ker →* X := f.comp g.ker.subtype
    have hf₁ : Function.Surjective f₁ := by
      intro x
      have hx : x ∈ g.ker.map f := htop ▸ Subgroup.mem_top x
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨⟨k, hk⟩, rfl⟩
    let j : g.ker →* ρ.ker :=
      (K.subtype.comp g.ker.subtype).codRestrict ρ.ker (fun k => MonoidHom.mem_ker.mpr k.2)
    refine of_ker_le f₁ hf₁ j fun k hk => ?_
    have hk1 : ((k : K) : Y) = 1 := congrArg (fun y : ρ.ker => (y : Y)) hk
    have : k = 1 := Subtype.ext (Subtype.ext hk1)
    simp [this]

theorem commutator_eq_top_of_simple [IsSimpleGroup X] (hnc : ∃ x y : X, x * y ≠ y * x) :
    ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hxy hmem
  · exact h

theorem of_pi {ι : Type*} [Finite ι] {S : ι → Type*} [∀ i, Group (S i)] [IsSimpleGroup X]
    (hnc : ∃ x y : X, x * y ≠ y * x) (h : IsSectionOf X (∀ i, S i)) :
    ∃ i, IsSectionOf X (S i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨K, f, hf⟩ := h
  by_contra hcon
  push Not at hcon
  let g : ∀ i, K →* S i := fun i => (Pi.evalMonoidHom S i).comp K.subtype
  have htop : ∀ i, (g i).ker.map f = ⊤ := by
    intro i
    have hnormal : ((g i).ker.map f).Normal := (MonoidHom.normal_ker (g i)).map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((g i).ker.map f) with hbot | htop
    · exact absurd (of_ker_le f hf (g i) ((Subgroup.map_eq_bot_iff _).mp hbot)) (hcon i)
    · exact htop
  have hperf := commutator_eq_top_of_simple (X := X) hnc
  have hfin : ∀ s : Finset ι, (⨅ i ∈ s, (g i).ker).map f = ⊤ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Subgroup.map_top_of_surjective f hf]
    | insert j s hj ih =>
      rw [Finset.iInf_insert]
      have : (⨅ i ∈ s, (g i).ker).Normal :=
        Subgroup.normal_iInf_normal fun i => Subgroup.normal_iInf_normal fun _ =>
          MonoidHom.normal_ker (g i)
      have := MonoidHom.normal_ker (g j)
      have hle : ⁅(g j).ker, ⨅ i ∈ s, (g i).ker⁆ ≤ (g j).ker ⊓ ⨅ i ∈ s, (g i).ker :=
        Subgroup.commutator_le_inf _ _
      have hmap : (⁅(g j).ker, ⨅ i ∈ s, (g i).ker⁆).map f = ⊤ := by
        rw [Subgroup.map_commutator, htop j, ih, hperf]
      exact top_le_iff.mp (hmap ▸ Subgroup.map_mono hle)
  have hbot : (⨅ i ∈ (Finset.univ : Finset ι), (g i).ker) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_iInf] at hk
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    funext i
    have := (Subgroup.mem_iInf.mp (hk i)) (Finset.mem_univ i)
    exact this
  have := hfin Finset.univ
  rw [hbot, Subgroup.map_bot] at this
  obtain ⟨x, y, hxy⟩ := hnc
  have h1 : x ∈ (⊤ : Subgroup X) := Subgroup.mem_top x
  have h2 : y ∈ (⊤ : Subgroup X) := Subgroup.mem_top y
  rw [← this] at h1 h2
  rw [Subgroup.mem_bot] at h1 h2
  exact hxy (by rw [h1, h2])

end IsSectionOf

end CFSG.SignalizerFunctorTheorem
