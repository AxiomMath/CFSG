module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import CFSG.Quasithin.Background.F3Paths

public section

namespace CFSG.Quasithin.H13.AS91

variable {G : Type*} [Group G]

@[expose] def CInc (A B : Subgroup G) (a : G ⧸ A) (b : G ⧸ B) : Prop :=
  ∃ g : G, (g : G ⧸ A) = a ∧ (g : G ⧸ B) = b

theorem cInc_mk (A B : Subgroup G) (g : G) : CInc A B (g : G ⧸ A) (g : G ⧸ B) :=
  ⟨g, rfl, rfl⟩

theorem CInc.symm' {A B : Subgroup G} {a : G ⧸ A} {b : G ⧸ B} (h : CInc A B a b) :
    CInc B A b a := by
  obtain ⟨g, ha, hb⟩ := h
  exact ⟨g, hb, ha⟩

theorem mk_mul_eq_smul (C : Subgroup G) (x y : G) :
    ((x * y : G) : G ⧸ C) = x • ((y : G) : G ⧸ C) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul]

theorem cInc_smul (A B : Subgroup G) (h : G) (a : G ⧸ A) (b : G ⧸ B) :
    CInc A B (h • a) (h • b) ↔ CInc A B a b := by
  constructor
  · rintro ⟨g, ha, hb⟩
    refine ⟨h⁻¹ * g, ?_, ?_⟩
    · rw [mk_mul_eq_smul, ha, inv_smul_smul]
    · rw [mk_mul_eq_smul, hb, inv_smul_smul]
  · rintro ⟨g, ha, hb⟩
    refine ⟨h * g, ?_, ?_⟩
    · rw [mk_mul_eq_smul, ha]
    · rw [mk_mul_eq_smul, hb]

@[expose] def colGraph (G₁ G₂ : Subgroup G) : SimpleGraph (G ⧸ G₁) where
  Adj x y := x ≠ y ∧ ∃ l : G ⧸ G₂, CInc G₁ G₂ x l ∧ CInc G₁ G₂ y l
  symm := ⟨fun _ _ ⟨hne, l, hx, hy⟩ => ⟨hne.symm, l, hy, hx⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem colGraph_adj {G₁ G₂ : Subgroup G} {x y : G ⧸ G₁} :
    (colGraph G₁ G₂).Adj x y ↔ x ≠ y ∧ ∃ l : G ⧸ G₂, CInc G₁ G₂ x l ∧ CInc G₁ G₂ y l :=
  Iff.rfl

instance instGraphActionColGraph (G₁ G₂ : Subgroup G) :
    CFSG.Quasithin.GraphAction G (colGraph G₁ G₂) where
  adj_smul g a b := by
    rw [colGraph_adj, colGraph_adj]
    constructor
    · rintro ⟨hne, l, ha, hb⟩
      refine ⟨fun h => hne (by rw [h]), g⁻¹ • l, ?_, ?_⟩
      · rw [← cInc_smul G₁ G₂ g, smul_inv_smul]
        exact ha
      · rw [← cInc_smul G₁ G₂ g, smul_inv_smul]
        exact hb
    · rintro ⟨hne, l, ha, hb⟩
      refine ⟨fun h => hne (smul_left_cancel g h), g • l, ?_, ?_⟩
      · rw [cInc_smul]
        exact ha
      · rw [cInc_smul]
        exact hb

@[expose] def objOf (A B : Subgroup G) (b : G ⧸ B) : Set (G ⧸ A) := {a | CInc A B a b}

theorem mem_objOf {A B : Subgroup G} {b : G ⧸ B} {a : G ⧸ A} :
    a ∈ objOf A B b ↔ CInc A B a b :=
  Iff.rfl

theorem objOf_one (A B : Subgroup G) :
    objOf A B ((1 : G) : G ⧸ B) = (fun h : G => (h : G ⧸ A)) '' (B : Set G) := by
  ext a
  constructor
  · rintro ⟨g, ha, hb⟩
    refine ⟨g, ?_, ha⟩
    have : ((g : G ⧸ B)) = ((1 : G) : G ⧸ B) := hb
    rw [QuotientGroup.eq] at this
    simpa using this
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h, rfl, ?_⟩
    show ((h : G) : G ⧸ B) = ((1 : G) : G ⧸ B)
    rw [QuotientGroup.eq]
    simpa using hh

theorem objOf_smul (A B : Subgroup G) (g : G) (b : G ⧸ B) :
    objOf A B (g • b) = (g • ·) '' objOf A B b := by
  ext a
  constructor
  · intro ha
    refine ⟨g⁻¹ • a, ?_, smul_inv_smul g a⟩
    rw [mem_objOf, ← cInc_smul A B g, smul_inv_smul]
    exact ha
  · rintro ⟨a', ha', rfl⟩
    rw [mem_objOf, cInc_smul]
    exact ha'

end CFSG.Quasithin.H13.AS91
