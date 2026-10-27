module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.Quasithin.Background.F2Amalgam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

universe u w

inductive RankTwoIndex
  | one
  | two
  | onetwo

namespace RankTwoIndex

@[expose] def le : RankTwoIndex → RankTwoIndex → Prop
  | .one, .one => True
  | .two, .two => True
  | .onetwo, _ => True
  | _, _ => False

instance : Preorder RankTwoIndex where
  le := le
  le_refl a := by cases a <;> trivial
  le_trans a b c hab hbc := by
    cases a <;> cases b <;> cases c <;> simp_all [le]

end RankTwoIndex

structure RankTwoAmalgam where
  G1 : Type u
  G12 : Type u
  G2 : Type u
  [grp1 : Group G1]
  [grp12 : Group G12]
  [grp2 : Group G2]
  α1 : G12 →* G1
  α2 : G12 →* G2

attribute [instance] RankTwoAmalgam.grp1 RankTwoAmalgam.grp12 RankTwoAmalgam.grp2

namespace RankTwoAmalgam

variable (α : RankTwoAmalgam.{u})

@[expose] def X : RankTwoIndex → Type u
  | .one => α.G1
  | .two => α.G2
  | .onetwo => α.G12

instance (d : RankTwoIndex) : Group (α.X d) := by
  cases d
  · exact α.grp1
  · exact α.grp2
  · exact α.grp12

@[expose] def mapHom : ∀ {d e : RankTwoIndex}, d ≤ e → α.X d →* α.X e
  | .one, .one, _ => MonoidHom.id _
  | .two, .two, _ => MonoidHom.id _
  | .onetwo, .onetwo, _ => MonoidHom.id _
  | .onetwo, .one, _ => α.α1
  | .onetwo, .two, _ => α.α2
  | .one, .two, h => h.elim
  | .two, .one, h => h.elim
  | .one, .onetwo, h => h.elim
  | .two, .onetwo, h => h.elim

@[expose] def toAmalgam : Amalgam.{0, u} RankTwoIndex where
  X := α.X
  map := α.mapHom
  map_self d x := by cases d <;> rfl
  map_comp {d e f} h₁ h₂ x := by
    cases d <;> cases e <;> cases f <;> first | rfl | exact h₁.elim | exact h₂.elim

@[expose] def IsInjective : Prop := Function.Injective α.α1 ∧ Function.Injective α.α2

section OfSubgroups

variable {X : Type u} [Group X]

@[expose] def ofSubgroups (P1 P2 : Subgroup X) : RankTwoAmalgam.{u} where
  G1 := P1
  G12 := ↥(P1 ⊓ P2)
  G2 := P2
  α1 := Subgroup.inclusion (inf_le_left : P1 ⊓ P2 ≤ P1)
  α2 := Subgroup.inclusion (inf_le_right : P1 ⊓ P2 ≤ P2)

theorem ofSubgroups_isInjective (P1 P2 : Subgroup X) : (ofSubgroups P1 P2).IsInjective :=
  ⟨Subgroup.inclusion_injective (inf_le_left : P1 ⊓ P2 ≤ P1),
    Subgroup.inclusion_injective (inf_le_right : P1 ⊓ P2 ≤ P2)⟩

end OfSubgroups

structure Hom (α β : RankTwoAmalgam.{u}) where
  φ1 : α.G1 →* β.G1
  φ12 : α.G12 →* β.G12
  φ2 : α.G2 →* β.G2
  comm1 : ∀ g, β.α1 (φ12 g) = φ1 (α.α1 g)
  comm2 : ∀ g, β.α2 (φ12 g) = φ2 (α.α2 g)

abbrev Aut : Type _ := Amalgam.Aut α.toAmalgam

structure Iso (α β : RankTwoAmalgam.{u}) where
  φ1 : α.G1 ≃* β.G1
  φ12 : α.G12 ≃* β.G12
  φ2 : α.G2 ≃* β.G2
  comm1 : ∀ g, β.α1 (φ12 g) = φ1 (α.α1 g)
  comm2 : ∀ g, β.α2 (φ12 g) = φ2 (α.α2 g)

@[expose] def ParabolicIso (α β : RankTwoAmalgam.{u}) : Prop :=
  Nonempty (α.G1 ≃* β.G1) ∧ Nonempty (α.G12 ≃* β.G12) ∧ Nonempty (α.G2 ≃* β.G2)

theorem Iso.parabolicIso {α β : RankTwoAmalgam.{u}} (e : Iso α β) : ParabolicIso α β :=
  ⟨⟨e.φ1⟩, ⟨e.φ12⟩, ⟨e.φ2⟩⟩

structure Completion (α : RankTwoAmalgam.{u}) (Y : Type w) [Group Y] where
  φ1 : α.G1 →* Y
  φ12 : α.G12 →* Y
  φ2 : α.G2 →* Y
  comm1 : ∀ g, φ1 (α.α1 g) = φ12 g
  comm2 : ∀ g, φ2 (α.α2 g) = φ12 g
  inter : φ1.range ⊓ φ2.range = φ12.range
  gen : φ1.range ⊔ φ2.range = ⊤

@[expose] def Completion.IsFaithful {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    (c : Completion α Y) : Prop :=
  Function.Injective c.φ1 ∧ Function.Injective c.φ12 ∧ Function.Injective c.φ2

@[expose] def Completion.homFamily {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    (c : Completion α Y) : ∀ d, α.X d →* Y
  | .one => c.φ1
  | .two => c.φ2
  | .onetwo => c.φ12

@[expose] def Completion.toCompletion {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y]
    (c : Completion α Y) : Amalgam.Completion α.toAmalgam Y where
  toHom := c.homFamily
  comm {d e} h x := by
    cases d <;> cases e <;> first | rfl | exact h.elim | exact c.comm1 x | exact c.comm2 x
  gen := by
    rw [eq_top_iff, ← c.gen]
    exact sup_le (le_iSup (fun d => (c.homFamily d).range) RankTwoIndex.one)
      (le_iSup (fun d => (c.homFamily d).range) RankTwoIndex.two)

section InclusionCompletion

variable {G : Type u} [Group G]

theorem range_inclusion_sup_eq_top (P1 P2 G0 : Subgroup G) (h : P1 ⊔ P2 = G0) :
    (Subgroup.inclusion (le_sup_left.trans h.le) : (P1 : Subgroup G) →* G0).range ⊔
      (Subgroup.inclusion (le_sup_right.trans h.le) : (P2 : Subgroup G) →* G0).range = ⊤ := by
  refine Subgroup.map_injective (f := G0.subtype) G0.subtype_injective ?_
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype]
  have h1 : (Subgroup.inclusion (le_sup_left.trans h.le) : (P1 : Subgroup G) →* G0).range.map
      G0.subtype = P1 := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact a.2
    · intro hz
      exact ⟨_, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  have h2 : (Subgroup.inclusion (le_sup_right.trans h.le) : (P2 : Subgroup G) →* G0).range.map
      G0.subtype = P2 := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact a.2
    · intro hz
      exact ⟨_, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  rw [h1, h2, h]

@[expose] def inclusionCompletion (P1 P2 G0 : Subgroup G) (h : P1 ⊔ P2 = G0) :
    (ofSubgroups P1 P2).Completion ↥G0 where
  φ1 := Subgroup.inclusion (le_sup_left.trans h.le)
  φ12 := Subgroup.inclusion ((inf_le_left : P1 ⊓ P2 ≤ P1).trans (le_sup_left.trans h.le))
  φ2 := Subgroup.inclusion (le_sup_right.trans h.le)
  comm1 _ := rfl
  comm2 _ := rfl
  inter := by
    ext z
    simp only [Subgroup.mem_inf, ofSubgroups]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have h1 : (a : G) = z := congrArg Subtype.val ha
      have h2 : (b : G) = z := congrArg Subtype.val hb
      exact ⟨⟨z, ⟨h1 ▸ a.2, h2 ▸ b.2⟩⟩, rfl⟩
    · rintro ⟨⟨w, hw⟩, hz⟩
      have : (w : G) = z := congrArg Subtype.val hz
      exact ⟨⟨⟨z, this ▸ hw.1⟩, rfl⟩, ⟨⟨z, this ▸ hw.2⟩, rfl⟩⟩
  gen := range_inclusion_sup_eq_top P1 P2 G0 h

theorem inclusionCompletion_isFaithful (P1 P2 G0 : Subgroup G) (h : P1 ⊔ P2 = G0) :
    (inclusionCompletion P1 P2 G0 h).IsFaithful :=
  ⟨fun a b hab => by have h' := congrArg Subtype.val hab; exact Subtype.ext h',
    fun a b hab => by have h' := congrArg Subtype.val hab; exact Subtype.ext h',
    fun a b hab => by have h' := congrArg Subtype.val hab; exact Subtype.ext h'⟩

end InclusionCompletion

end RankTwoAmalgam

section WeakBNPair

variable {G : Type u} [Group G]

structure HypAAt (P B Pstar : Subgroup G) : Prop where
  le : Pstar ≤ P
  normal : (Pstar.subgroupOf P).Normal
  pCore_eq : pCoreOf 2 Pstar = pCoreOf 2 P
  sup_eq : Pstar ⊔ B = P
  charTwo : CharTwo P
  sylow : ∃ T : Subgroup G, IsSylowTwoOf T Pstar ∧ T ≤ B ∧
    Pstar ⊓ B = Pstar ⊓ Subgroup.normalizer (T : Set G)
  listed : IsRankOneListed (oTwoQuot ↥Pstar)

@[expose] def HypothesisA (P1 P2 : Subgroup G) : Prop :=
  (∃ Q : Subgroup G, HypAAt P1 (P1 ⊓ P2) Q) ∧ (∃ Q : Subgroup G, HypAAt P2 (P1 ⊓ P2) Q)

structure IsWeakBNPair (P1 P2 : Subgroup G) : Prop where
  finite1 : Finite ↥P1
  finite2 : Finite ↥P2
  core : coreIn (P1 ⊓ P2) (P1 ⊔ P2) = ⊥
  hypA : HypothesisA P1 P2

end WeakBNPair

section YAmalgam

variable {Y : Type u} [Group Y]

@[expose] def IsMaximalTwoLocal (M : Subgroup Y) : Prop :=
  CFSG.Open.IsMaxTwoLocalSubgroup M

@[expose] def IsYAmalgamPair (T M₁ M₂ : Subgroup Y) : Prop :=
  IsSylowTwoOf T ⊤ ∧ M₁ ≠ M₂ ∧
    ∀ M : Subgroup Y, (IsMaximalTwoLocal M ∧ Subgroup.normalizer (T : Set Y) ≤ M) ↔ (M = M₁ ∨ M = M₂)

@[expose] def IsYAmalgam (α : RankTwoAmalgam.{u}) (T : Subgroup Y) : Prop :=
  ∃ M₁ M₂ : Subgroup Y, IsYAmalgamPair T M₁ M₂ ∧ Nonempty (α.Iso (RankTwoAmalgam.ofSubgroups M₁ M₂))

@[expose] def IsParabolicYAmalgam (α : RankTwoAmalgam.{u}) (T : Subgroup Y) : Prop :=
  ∃ M₁ M₂ : Subgroup Y, IsYAmalgamPair T M₁ M₂ ∧
    α.ParabolicIso (RankTwoAmalgam.ofSubgroups M₁ M₂)

end YAmalgam

end CFSG.Quasithin
