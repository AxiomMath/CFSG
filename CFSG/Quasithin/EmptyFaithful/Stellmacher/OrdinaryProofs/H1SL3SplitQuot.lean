module

public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type} [Group G]

structure AbelSub (G : Type) [Group G] where
  carrier : Subgroup G
  comm : ∀ x ∈ carrier, ∀ y ∈ carrier, x * y = y * x

instance (S : AbelSub G) : CommGroup S.carrier :=
  { (inferInstance : Group S.carrier) with
    mul_comm := fun a b => Subtype.ext (S.comm a a.2 b b.2) }

abbrev AbelSub.quot (S : AbelSub G) (W : Subgroup G) : Type :=
  Additive (S.carrier ⧸ W.subgroupOf S.carrier)

noncomputable instance (S : AbelSub G) (W : Subgroup G) : AddCommGroup (S.quot W) :=
  inferInstanceAs (AddCommGroup (Additive (S.carrier ⧸ W.subgroupOf S.carrier)))

theorem AbelSub.two_nsmul_quot (S : AbelSub G) (W : Subgroup G)
    (hS2 : ∀ x ∈ S.carrier, x * x = 1) (x : S.quot W) : (2 : ℕ) • x = 0 := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : x = Additive.ofMul (QuotientGroup.mk g : S.carrier ⧸ W.subgroupOf S.carrier) := by
    rw [hg]
    rfl
  have hmem : g * g ∈ W.subgroupOf S.carrier := by
    have h1 : g * g = 1 := Subtype.ext (by simp [hS2 g g.2])
    rw [h1]
    exact Subgroup.one_mem _
  rw [hx, two_nsmul]
  show Additive.ofMul ((QuotientGroup.mk g : S.carrier ⧸ W.subgroupOf S.carrier) *
    (QuotientGroup.mk g)) = 0
  rw [← QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hmem]
  rfl

noncomputable abbrev AbelSub.quotZMod (S : AbelSub G) (W : Subgroup G)
    (hS2 : ∀ x ∈ S.carrier, x * x = 1) : Module (ZMod 2) (S.quot W) :=
  AddCommGroup.zmodModule (S.two_nsmul_quot W hS2)

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
