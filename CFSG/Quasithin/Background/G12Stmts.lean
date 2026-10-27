module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsSymplectic (B : LinearMap.BilinForm (ZMod 2) V) : Prop :=
  (∀ x, B x x = 0) ∧ ∀ x, (∀ y, B x y = 0) → x = 0

@[expose] def spSub (B : LinearMap.BilinForm (ZMod 2) V) : Subgroup (GLV V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' := fun {a b} ha hb x y => by
    show B (a (b x)) (a (b y)) = B x y
    rw [ha, hb]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha x y => by
    show B (a.symm x) (a.symm y) = B x y
    rw [← ha (a.symm x) (a.symm y)]
    simp

@[expose] def orthSub (q : V → ZMod 2) : Subgroup (GLV V) where
  carrier := {g | ∀ x, q (g x) = q x}
  mul_mem' := fun {a b} ha hb x => by
    show q (a (b x)) = q x
    rw [ha, hb]
  one_mem' := fun _ => rfl
  inv_mem' := fun {a} ha x => by
    show q (a.symm x) = q x
    rw [← ha (a.symm x)]
    simp

@[expose] def QSub (G : Subgroup (GLV V)) (v : V) (U : Submodule (ZMod 2) V) :
    Subgroup (GLV V) where
  carrier := {g | g ∈ G ∧ g v = v ∧ ∀ x ∈ U, g x ∈ U ∧ g x - x ∈ Submodule.span (ZMod 2) {v}}
  mul_mem' := fun {a b} ha hb => by
    refine ⟨G.mul_mem ha.1 hb.1, ?_, fun x hx => ?_⟩
    · show a (b v) = v
      rw [hb.2.1, ha.2.1]
    · obtain ⟨hbx, hbx'⟩ := hb.2.2 x hx
      obtain ⟨hax, hax'⟩ := ha.2.2 (b x) hbx
      refine ⟨hax, ?_⟩
      have h : (a * b) x - x = (a (b x) - b x) + (b x - x) := by
        show a (b x) - x = _
        abel
      rw [h]
      exact Submodule.add_mem _ hax' hbx'
  one_mem' := ⟨G.one_mem, rfl, fun x hx => ⟨hx, by simp⟩⟩
  inv_mem' := fun {a} ha => by
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    have key : ∀ x ∈ U, a.symm x = a x := by
      intro x hx
      obtain ⟨-, hx'⟩ := ha.2.2 x hx
      obtain ⟨c, hcx⟩ := Submodule.mem_span_singleton.1 hx'
      have h1 : a x = x + c • v := by
        rw [hcx]
        abel
      have h2v : v + v = 0 := by
        rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]
      have h2 : a (a x) = x := by
        rw [h1, map_add, map_smul, ha.2.1, h1]
        rcases hc c with rfl | rfl
        · simp
        · rw [one_smul, add_assoc, h2v, add_zero]
      rw [LinearEquiv.symm_apply_eq]
      exact h2.symm
    refine ⟨G.inv_mem ha.1, ?_, fun x hx => ?_⟩
    · show a.symm v = v
      rw [LinearEquiv.symm_apply_eq, ha.2.1]
    · show a.symm x ∈ U ∧ a.symm x - x ∈ _
      rw [key x hx]
      exact ha.2.2 x hx

@[expose] def IsStarVec (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v : V) :
    Prop :=
  v ≠ 0 ∧ ∃ hv : v ∈ perp B v, FullTransvections (QSub Γ v (perp B v)) (perp B v) v hv

@[expose] def omegaSub (B : LinearMap.BilinForm (ZMod 2) V) (q : V → ZMod 2) : Subgroup (GLV V) :=
  Subgroup.closure {g | ∃ v, v ≠ 0 ∧ q v = 0 ∧ g ∈ QSub (orthSub q) v (perp B v)}

@[expose] def IsL24ModuleFor (A : Subgroup (GLV V)) : Prop :=
  Nonempty (↥A ≃* ↥(alternatingGroup (Fin 5))) ∧
    ∃ ω : GLV V, (∀ x, ω (ω x) + ω x + x = 0) ∧ ∀ a ∈ A, a * ω = ω * a

@[expose] def G121Concl (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v : V) :
    Prop :=
  Γ = spSub B ∨
  (∃ q : V → ZMod 2, (∀ x y, q (x + y) = q x + q y + B x y) ∧
    (Γ = orthSub q ∨ Γ = omegaSub B q) ∧ ∀ w, (∃ g ∈ Γ, w = g v) ↔ (w ≠ 0 ∧ q w = 0)) ∨
  (Module.finrank (ZMod 2) V = 4 ∧ (Γ = ⁅spSub B, spSub B⁆ ∨
    (Nonempty (↥Γ ≃* Equiv.Perm (Fin 5)) ∧
      ∃ A : Subgroup (GLV V), A ≤ Γ ∧ IsL24ModuleFor A)))

@[expose] def G121Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (u v : V),
    IsSymplectic B → Γ ≤ spSub B → IsStarVec B Γ u → IsStarVec B Γ v → B u v ≠ 0 →
    4 ≤ Module.finrank (ZMod 2) V → G121Concl B Γ v

structure G1212Hyp (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V) : Prop where
  dim : 2 < Module.finrank (ZMod 2) V
  le : K ≤ H
  normal : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K
  irr : IsIrr K ⊤
  selfDual : SelfDual K ⊤
  q_le : Q ≤ H
  q_comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  q_sq : ∀ a ∈ Q, a * a = 1
  hyperplane : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) V
  v_mem : v ∈ W
  v_ne : v ≠ 0
  transvections : FullTransvections Q W v v_mem

@[expose] def G1212Concl (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V) : Prop :=
  ∃ f : LinearMap.BilinForm (ZMod 2) V, IsSymplectic f ∧ K ⊔ Q ≤ spSub f ∧ W = perp f v ∧
    (∀ k ∈ K, IsStarVec f (K ⊔ Q) (k v)) ∧ (∃ h ∈ H, h v ∉ W) ∧
    (H ≤ spSub f ∨ ∃ ω : GLV V, (∀ x, ω (ω x) + ω x + x = 0) ∧
      H = Subgroup.normalizer (Subgroup.zpowers ω : Set (GLV V))) ∧
    G121Concl f (K ⊔ Q) v ∧ (H ≤ spSub f → G121Concl f H v)

@[expose] def G1212Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (H K Q : Subgroup (GLV V)) (W : Submodule (ZMod 2) V) (v : V),
    G1212Hyp H K Q W v → G1212Concl H K Q W v

end G11

end CFSG.Quasithin
