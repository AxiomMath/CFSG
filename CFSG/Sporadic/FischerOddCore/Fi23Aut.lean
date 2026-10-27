module

public import CFSG.Sporadic.Fi23.Rigid
public import CFSG.Fischer.Polar.Facts
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Sporadic.FischerOddCore.AlmostSimple

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.Fi23 CFSG.ComponentClassification.OuterAutomorphisms CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mulAut_eq_conj_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ∀ φ : MulAut H, ∃ g : H, φ = MulAut.conj g) (φ : MulAut G) :
    ∃ g : G, φ = MulAut.conj g := by
  obtain ⟨g, hg⟩ := h (MulAut.congr e φ)
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun ψ : MulAut H => ψ (e x)) hg
  apply e.injective
  simpa [MulAut.congr_apply] using h1

theorem inner_eq_top_of {G : Type*} [Group G] (h : ∀ φ : MulAut G, ∃ g : G, φ = MulAut.conj g) :
    inner G = ⊤ := by
  rw [eq_top_iff]
  intro φ _
  obtain ⟨g, rfl⟩ := h φ
  exact ⟨g, rfl⟩

theorem card_outer_of {G : Type*} [Group G] (h : ∀ φ : MulAut G, ∃ g : G, φ = MulAut.conj g) :
    Nat.card (Outer G) = 1 := by
  change (inner G).index = 1
  rw [Subgroup.index_eq_one]
  exact inner_eq_top_of h

theorem isSolvable_outer_of {G : Type*} [Group G] (h : Nat.card (Outer G) = 1) :
    Group.IsSolvable (Outer G) := by
  have := (Nat.card_eq_one_iff_unique.1 h).1
  infer_instance

@[expose] def autSetPerm {G : Type*} [Group G] (E : Set G)
    (hE : ∀ φ : MulAut G, ∀ x, φ x ∈ E ↔ x ∈ E) : MulAut G →* Equiv.Perm E where
  toFun φ := Equiv.Perm.subtypePerm φ.toEquiv (hE φ)
  map_one' := Equiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := Equiv.ext fun _ => Subtype.ext rfl

theorem autSetPerm_apply {G : Type*} [Group G] (E : Set G)
    (hE : ∀ φ : MulAut G, ∀ x, φ x ∈ E ↔ x ∈ E) (φ : MulAut G) (x : E) :
    (autSetPerm E hE φ x : G) = φ x :=
  rfl

theorem mem_class_iff_of_inner {G : Type*} [Group G]
    (h : ∀ φ : MulAut G, ∃ g : G, φ = MulAut.conj g)
    (d : G) (φ : MulAut G) (x : G) : φ x ∈ {y | IsConj d y} ↔ x ∈ {y | IsConj d y} := by
  obtain ⟨g, rfl⟩ := h φ
  simp only [Set.mem_ofPred_eq, MulAut.conj_apply]
  constructor
  · intro hx
    exact hx.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
  · intro hx
    exact hx.trans (isConj_iff.2 ⟨g, rfl⟩)

theorem fi23_mulAut_eq_conj
    (φ : MulAut Blueprint.NativeSporadic.Fi23) :
    ∃ g : Blueprint.NativeSporadic.Fi23, φ = MulAut.conj g :=
  @mulAut_eq_conj_of_mulEquiv Blueprint.NativeSporadic.Fi23 J Units.instGroup J.toGroup
    fi23EquivJ (fi23_complete polarFacts hyperovalFacts
      (Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts)) φ

theorem inner_fi23_eq_top :
    inner Blueprint.NativeSporadic.Fi23 = ⊤ :=
  @inner_eq_top_of Blueprint.NativeSporadic.Fi23 Units.instGroup fi23_mulAut_eq_conj

theorem card_outer_fi23 :
    Nat.card (Outer Blueprint.NativeSporadic.Fi23) = 1 :=
  @card_outer_of Blueprint.NativeSporadic.Fi23 Units.instGroup fi23_mulAut_eq_conj

theorem center_fi23 :
    Subgroup.center Blueprint.NativeSporadic.Fi23 = ⊥ :=
  @center_eq_bot_of_mulEquiv Blueprint.NativeSporadic.Fi23 J Units.instGroup J.toGroup
    fi23EquivJ center_J

@[expose] def fi23Class :
    Set Blueprint.NativeSporadic.Fi23 := {x | IsConj dFi23 x}

theorem fi23_mulAut_mem_class
    (φ : MulAut Blueprint.NativeSporadic.Fi23)
    (x : Blueprint.NativeSporadic.Fi23) : φ x ∈ fi23Class ↔ x ∈ fi23Class :=
  @mem_class_iff_of_inner Blueprint.NativeSporadic.Fi23 Units.instGroup fi23_mulAut_eq_conj
    dFi23 φ x

@[expose] def fi23AutClassPerm :
    MulAut Blueprint.NativeSporadic.Fi23 →* Equiv.Perm fi23Class :=
  @autSetPerm Blueprint.NativeSporadic.Fi23 Units.instGroup fi23Class fi23_mulAut_mem_class

theorem autSetPerm_conj
    {G : Type} [Group G] (d : G) (hP : CFSG.Blueprint.Fischer.Pair G
    {x | IsConj d x}) (hE : ∀ φ : MulAut G, ∀ x, φ x ∈ {y | IsConj d y} ↔ x ∈ {y | IsConj d y})
    (g : G) : autSetPerm {x | IsConj d x} hE (MulAut.conj g) = Pair.conjPerm hP g :=
  Equiv.ext fun _ => Subtype.ext rfl

theorem all_automorphisms_inner_of {G : Type} [Group G] (d : G)
    (hP : CFSG.Blueprint.Fischer.Pair G {x | IsConj d x}) (hZ : Subgroup.center G = ⊥)
    (h : ∀ φ : MulAut G, ∃ g : G, φ = MulAut.conj g)
    (hE : ∀ φ : MulAut G, ∀ x, φ x ∈ {y | IsConj d y} ↔ x ∈ {y | IsConj d y}) :
    inner G = ⊤ ∧ Nat.card (Outer G) = 1 ∧
      Function.Injective (autSetPerm {x | IsConj d x} hE) ∧
      (autSetPerm {x | IsConj d x} hE).range = (Pair.conjPerm hP).range ∧
      Function.Injective (Pair.conjPerm hP) := by
  have hinj := Pair.conjPerm_injective hP hZ
  refine ⟨inner_eq_top_of h, card_outer_of h, ?_, ?_, hinj⟩
  · intro φ ψ hφψ
    obtain ⟨g, rfl⟩ := h φ
    obtain ⟨k, rfl⟩ := h ψ
    rw [autSetPerm_conj d hP, autSetPerm_conj d hP] at hφψ
    rw [hinj hφψ]
  · ext σ
    constructor
    · rintro ⟨φ, rfl⟩
      obtain ⟨g, rfl⟩ := h φ
      exact ⟨g, (autSetPerm_conj d hP hE g).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨MulAut.conj g, autSetPerm_conj d hP hE g⟩

theorem CTUC_Fi23_all_automorphisms_inner :
    inner Blueprint.NativeSporadic.Fi23 = ⊤ ∧ Nat.card (Outer Blueprint.NativeSporadic.Fi23) = 1 ∧
      Function.Injective fi23AutClassPerm ∧
      fi23AutClassPerm.range = (Pair.conjPerm pair_Fi23).range ∧
      Function.Injective (Pair.conjPerm pair_Fi23) :=
  @all_automorphisms_inner_of Blueprint.NativeSporadic.Fi23 Units.instGroup dFi23 pair_Fi23
    center_fi23 fi23_mulAut_eq_conj fi23_mulAut_mem_class

theorem CTUC_Fi23_Schreier :
    Nat.card (Outer Blueprint.NativeSporadic.Fi23) = 1 ∧
      (∀ φ : MulAut Blueprint.NativeSporadic.Fi23,
        ∃ g : Blueprint.NativeSporadic.Fi23, φ = MulAut.conj g) ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.Fi23) :=
  ⟨card_outer_fi23, fi23_mulAut_eq_conj,
    @isSolvable_outer_of Blueprint.NativeSporadic.Fi23 Units.instGroup card_outer_fi23⟩

end CFSG.Sporadic.FischerOddCore
