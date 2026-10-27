module

public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Background.G93ApplyRestrict

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace G117

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Accessors

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {X L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem props_irrPlus (h : G116Props B Γ v₁ X L I) : IrrPlus (normalClosure Γ L) I := h.1

theorem props_invariantX (h : G116Props B Γ v₁ X L I) : Invariant X I := h.2.2.1

theorem props_unique (h : G116Props B Γ v₁ X L I) :
    ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → Invariant X J → J = I :=
  h.2.2.2.1

theorem props_homogeneous (h : G116Props B Γ v₁ X L I) : Homogeneous (normalClosure Γ L) :=
  h.2.2.2.2.1

theorem props_selfDual (h : G116Props B Γ v₁ X L I) : SelfDual (normalClosure Γ L) I :=
  h.2.2.2.2.2.2.1

theorem props_faithful (h : G116Props B Γ v₁ X L I) : FaithfulOn (normalClosure Γ L) I :=
  h.2.2.2.2.2.2.2.1

end Accessors

variable [Finite V]

structure Ctx (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (m : ℕ) :
    Prop where
  setup : G11Setup B Γ v₁ W X X₀ L
  props : G116Props B Γ v₁ X L I
  faithful : FaithfulOn X I
  card : Nat.card X = 2 ^ m

@[expose] noncomputable def topK (Γ L X : Subgroup (GLV V)) :
    Subgroup (GLV ↥(⊤ : Submodule (ZMod 2) V)) :=
  restrictRange (normalClosure Γ L ⊔ X) ⊤ (invariant_top _)

@[expose] noncomputable def topH (Γ L : Subgroup (GLV V)) :
    Subgroup (GLV ↥(⊤ : Submodule (ZMod 2) V)) :=
  restrictRange (normalClosure Γ L) ⊤ (invariant_top _)

omit [Finite V] in
theorem selfDual_restrictRange {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hK : Invariant K I) (h : SelfDual K I) : SelfDual (restrictRange K I hK) ⊤ := by
  obtain ⟨f, hnd, hinv⟩ := h
  refine ⟨LinearMap.BilinForm.congr (Submodule.topEquiv (R := ZMod 2) (M := ↥I)).symm f,
    hnd.congr _, ?_⟩
  intro k' hk' i j i' j' hi hj
  obtain ⟨k, hkK, hk⟩ := (mem_restrictRange_iff hK).1 hk'
  simp only [LinearMap.BilinForm.congr_apply]
  exact hinv k hkK (↑i) (↑j) (↑i') (↑j') (by rw [← hk, hi]) (by rw [← hk, hj])

end G117

end G11

end CFSG.Quasithin
