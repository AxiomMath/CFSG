module

public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin.H13.F431.U42.Am

open CFSG.Quasithin

universe u w

@[expose] def isoSymm {α β : RankTwoAmalgam.{u}} (e : α.Iso β) : β.Iso α where
  φ1 := e.φ1.symm
  φ12 := e.φ12.symm
  φ2 := e.φ2.symm
  comm1 g := by
    apply e.φ1.injective
    rw [MulEquiv.apply_symm_apply, ← e.comm1, MulEquiv.apply_symm_apply]
  comm2 g := by
    apply e.φ2.injective
    rw [MulEquiv.apply_symm_apply, ← e.comm2, MulEquiv.apply_symm_apply]

@[expose] def isoTrans {α β γ : RankTwoAmalgam.{u}} (e : α.Iso β) (e' : β.Iso γ) : α.Iso γ where
  φ1 := e.φ1.trans e'.φ1
  φ12 := e.φ12.trans e'.φ12
  φ2 := e.φ2.trans e'.φ2
  comm1 g := by
    simp only [MulEquiv.trans_apply]
    rw [e'.comm1, e.comm1]
  comm2 g := by
    simp only [MulEquiv.trans_apply]
    rw [e'.comm2, e.comm2]

section OfSubgroups

variable {X X' : Type u} [Group X] [Group X']

@[expose] noncomputable def ofSubgroupsMapInj (f : X →* X') (hf : Function.Injective f)
    (A B : Subgroup X) : (RankTwoAmalgam.ofSubgroups A B).Iso
      (RankTwoAmalgam.ofSubgroups (A.map f) (B.map f)) where
  φ1 := Subgroup.equivMapOfInjective A f hf
  φ12 := (Subgroup.equivMapOfInjective (A ⊓ B) f hf).trans
    (MulEquiv.subgroupCongr (Subgroup.map_inf_eq A B f hf))
  φ2 := Subgroup.equivMapOfInjective B f hf
  comm1 _ := rfl
  comm2 _ := rfl

@[expose] def ofSubgroupsCongr {A A' B B' : Subgroup X} (hA : A = A') (hB : B = B') :
    (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups A' B') where
  φ1 := MulEquiv.subgroupCongr hA
  φ12 := MulEquiv.subgroupCongr (by rw [hA, hB])
  φ2 := MulEquiv.subgroupCongr hB
  comm1 _ := rfl
  comm2 _ := rfl

end OfSubgroups

section Completion

variable {X : Type u} [Group X]

@[expose] def subCompletion (A B : Subgroup X) :
    (RankTwoAmalgam.ofSubgroups A B).Completion ↥(A ⊔ B) :=
  RankTwoAmalgam.inclusionCompletion A B (A ⊔ B) rfl

theorem subCompletion_isFaithful (A B : Subgroup X) : (subCompletion A B).IsFaithful :=
  RankTwoAmalgam.inclusionCompletion_isFaithful A B (A ⊔ B) rfl

theorem range_comp_mulEquiv {A B C : Type*} [Group A] [Group B] [Group C] (f : B →* C)
    (e : A ≃* B) : (f.comp e.toMonoidHom).range = f.range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨e.symm b, by simp⟩

@[expose] def precompIso {α α' : RankTwoAmalgam.{u}} {Y : Type w} [Group Y] (e : α.Iso α')
    (c : α'.Completion Y) : α.Completion Y where
  φ1 := c.φ1.comp e.φ1.toMonoidHom
  φ12 := c.φ12.comp e.φ12.toMonoidHom
  φ2 := c.φ2.comp e.φ2.toMonoidHom
  comm1 g := by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← e.comm1, c.comm1]
  comm2 g := by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← e.comm2, c.comm2]
  inter := by
    rw [range_comp_mulEquiv, range_comp_mulEquiv, range_comp_mulEquiv]
    exact c.inter
  gen := by
    rw [range_comp_mulEquiv, range_comp_mulEquiv]
    exact c.gen

theorem precompIso_isFaithful {α α' : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    (e : α.Iso α') {c : α'.Completion Y} (hc : c.IsFaithful) : (precompIso e c).IsFaithful :=
  ⟨hc.1.comp e.φ1.injective, hc.2.1.comp e.φ12.injective, hc.2.2.comp e.φ2.injective⟩

end Completion

end CFSG.Quasithin.H13.F431.U42.Am
