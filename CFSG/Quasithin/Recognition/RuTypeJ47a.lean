module

public import CFSG.Quasithin.Recognition.F4Main
public import CFSG.Quasithin.Recognition.CertTwoF4Table

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

universe u w

@[expose] def amIsoSymm {α β : RankTwoAmalgam.{u}} (e : α.Iso β) : β.Iso α where
  φ1 := e.φ1.symm
  φ12 := e.φ12.symm
  φ2 := e.φ2.symm
  comm1 g := by
    apply e.φ1.injective
    rw [MulEquiv.apply_symm_apply, ← e.comm1, MulEquiv.apply_symm_apply]
  comm2 g := by
    apply e.φ2.injective
    rw [MulEquiv.apply_symm_apply, ← e.comm2, MulEquiv.apply_symm_apply]

@[expose] def amIsoTrans {α β γ : RankTwoAmalgam.{u}} (e : α.Iso β) (e' : β.Iso γ) :
    α.Iso γ where
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

@[expose] def ofSubgroupsMapIso (f : X ≃* X') (A B : Subgroup X) :
    (RankTwoAmalgam.ofSubgroups A B).Iso
      (RankTwoAmalgam.ofSubgroups (A.map (f : X →* X')) (B.map (f : X →* X'))) where
  φ1 := f.subgroupMap A
  φ12 := (f.subgroupMap (A ⊓ B)).trans
    (MulEquiv.subgroupCongr (Subgroup.map_inf_eq A B (f : X →* X') f.injective))
  φ2 := f.subgroupMap B
  comm1 _ := rfl
  comm2 _ := rfl

@[expose] def ofSubgroupsCongr {A A' B B' : Subgroup X} (hA : A = A') (hB : B = B') :
    (RankTwoAmalgam.ofSubgroups A B).Iso (RankTwoAmalgam.ofSubgroups A' B') where
  φ1 := MulEquiv.subgroupCongr hA
  φ12 := MulEquiv.subgroupCongr (by rw [hA, hB])
  φ2 := MulEquiv.subgroupCongr hB
  comm1 _ := rfl
  comm2 _ := rfl

theorem subgroupOf_inf_eq {A B K : Subgroup X} :
    A.subgroupOf K ⊓ B.subgroupOf K = (A ⊓ B).subgroupOf K := by
  ext x
  simp [Subgroup.mem_subgroupOf]

@[expose] def ofSubgroupsSubgroupOfIso {A B K : Subgroup X} (hA : A ≤ K) (hB : B ≤ K) :
    (RankTwoAmalgam.ofSubgroups (A.subgroupOf K) (B.subgroupOf K)).Iso
      (RankTwoAmalgam.ofSubgroups A B) where
  φ1 := Subgroup.subgroupOfEquivOfLe hA
  φ12 := (MulEquiv.subgroupCongr subgroupOf_inf_eq).trans
    (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA))
  φ2 := Subgroup.subgroupOfEquivOfLe hB
  comm1 _ := rfl
  comm2 _ := rfl

end OfSubgroups

section SubCompletion

variable {X : Type u} [Group X]

@[expose] def subCompletion (A B : Subgroup X) :
    (RankTwoAmalgam.ofSubgroups A B).Completion ↥(A ⊔ B) :=
  RankTwoAmalgam.inclusionCompletion A B (A ⊔ B) rfl

theorem subCompletion_isFaithful (A B : Subgroup X) : (subCompletion A B).IsFaithful :=
  RankTwoAmalgam.inclusionCompletion_isFaithful A B (A ⊔ B) rfl

end SubCompletion

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

@[expose] noncomputable def twoF4Setting :
    LieSetting.{0, 0} where
  α := RankTwoAmalgam.ofSubgroups twoF4H twoF4N
  Yb := ↥(twoF4H ⊔ twoF4N)
  ι := subCompletion twoF4H twoF4N
  hι := subCompletion_isFaithful twoF4H twoF4N
  N := ⊤
  hN := Subgroup.normal_of_characteristic ⊤
  p := 2
  hp := Nat.prime_two
  m := 8
  hm := by norm_num

@[expose] def F45TwoF4 :
    Prop :=
  twoF4Setting.Facts45L

@[expose] def F48TwoF4 :
    Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (β : twoF4Setting.α.Completion Y), β.IsFaithful →
    β.IsSmall twoF4Setting.m → twoF4Setting.F48Concl β

end CFSG.Quasithin.RuType
