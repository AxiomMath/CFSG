module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepWeyl
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def lr6SmallCellA (p N : ℕ) : Prop :=
  (p = 5 ∧ N = 5) ∨ (p = 3 ∧ N = 6) ∨ (p = 7 ∧ N = 7)

@[expose] def lr6Group {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Type}
    (r : ι → (V ≃ₗ[ZMod p] V)) (t : V ≃ₗ[ZMod p] V) : Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure (Set.range r ∪ {t})

@[expose] def LR6JTriangleBalanced {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (S : Finset (Fin n)) (h : Fin n → V) (α : Fin n → Module.Dual (ZMod p) V)
    (r : Fin n → (V ≃ₗ[ZMod p] V)) (R : Subgroup (V ≃ₗ[ZMod p] V)) : Prop :=
  ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' → ∀ ψ ∈ R, ∀ (ht : V) (αt : Module.Dual (ZMod p) V),
    (∀ w, (ψ * r j * ψ⁻¹) w = w - αt w • ht) → αt ht = 2 →
    ψ * r j * ψ⁻¹ * r j' ≠ r j' * (ψ * r j * ψ⁻¹) →
    α j (h j') * α j' ht * αt (h j) = α j' (h j) * αt (h j') * α j ht

@[expose] def lr6ExclGroup {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Type}
    (r : ι → (V ≃ₗ[ZMod p] V)) (t : V ≃ₗ[ZMod p] V) : Subgroup (V ≃ₗ[ZMod p] V) :=
  lr6Group r t

@[expose] def LR6SmallRankPosB : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime], lr6SmallCellA p N →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V], Module.finrank (ZMod p) V = N →
    ∀ (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (ha : V) (αa : Module.Dual (ZMod p) V)
      (t : V ≃ₗ[ZMod p] V),
    GGIndepAFrame p N h α x →
    (∀ i v, r i v = v - α i v • h i) → (∀ v, t v = v - αa v • ha) → αa ha = 2 →
    αa x ≠ 0 → ha ∉ Submodule.span (ZMod p) (Set.range h) →
    (∃ (S : Finset (Fin (N - 1))) (MK : CoxeterMatrix (Option ↥S))
        (CK : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧ GGIsWeylMatrix MK ∧ GGIntCartan MK CK ∧
      (∀ i j : Option ↥S,
        (CK i j : ZMod p) = (i.elim αa fun a => α a) (j.elim ha fun b => h b)) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK none (some j) ≠ 0 ↔ j = c) ∧
      (5 ≤ p → LR6JTriangleBalanced S h α r (lr6Group r t)) ∧
      ∃ f : MK.Group ≃* ↥(lr6Group (fun j : ↥S => r j) t),
        ∀ o : Option ↥S, ((f (MK.simple o) : V ≃ₗ[ZMod p] V)) = o.elim t fun j => r j) →
    (∀ g ∈ lr6Group r t, ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
    Nat.card ↥(lr6Group r t) ≤ p ^ N * (6 * (p - 1) * Nat.factorial N) →
    ZS.LinWeyl p (lr6Group r t)

@[expose] def LR6SmallRankExcl : Prop :=
  ∀ (p N : ℕ) [Fact p.Prime], ((p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7)) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V], Module.finrank (ZMod p) V ≤ N →
    ∀ (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V)
      (r : Fin (N - 1) → (V ≃ₗ[ZMod p] V)) (ha : V) (αa : Module.Dual (ZMod p) V)
      (t : V ≃ₗ[ZMod p] V),
    GGIndepAFrame p N h α x →
    (∀ i v, r i v = v - α i v • h i) → (∀ v, t v = v - αa v • ha) → αa ha = 2 →
    αa x ≠ 0 → ha ∈ Submodule.span (ZMod p) (Set.range h) →
    (∃ (S : Finset (Fin (N - 1))) (MK : CoxeterMatrix (Option ↥S))
        (CK : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∃ s ≤ 2, ∀ i : Fin (N - 1), i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (N - 3)) ∧ GGIsWeylMatrix MK ∧
        GGIntCartan MK CK ∧
      (∀ i j : Option ↥S,
        (CK i j : ZMod p) = (i.elim αa fun a => α a) (j.elim ha fun b => h b)) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK none (some j) ≠ 0 ↔ j = c) ∧
      LR6JTriangleBalanced S h α r (lr6ExclGroup r t) ∧
      ∃ f : MK.Group ≃* ↥(lr6ExclGroup (fun j : ↥S => r j) t),
        ∀ o : Option ↥S, ((f (MK.simple o) : V ≃ₗ[ZMod p] V)) = o.elim t fun j => r j) →
    (∀ g ∈ lr6ExclGroup r t,
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) → False

@[expose] def LR6NineDepPos : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V], Module.finrank (ZMod 3) V ≤ 9 →
    ∀ (h : Fin 8 → V) (α : Fin 8 → Module.Dual (ZMod 3) V) (x : V)
      (r : Fin 8 → (V ≃ₗ[ZMod 3] V)) (ha : V) (αa : Module.Dual (ZMod 3) V)
      (t : V ≃ₗ[ZMod 3] V),
    GGDepAFrame 3 9 h α x →
    (∀ i v, r i v = v - α i v • h i) → (∀ v, t v = v - αa v • ha) → αa ha = 2 → αa x ≠ 0 →
    (∃ (S : Finset (Fin 8)) (MK : CoxeterMatrix (Option ↥S))
        (CK : Matrix (Option ↥S) (Option ↥S) ℤ),
      (∃ s ≤ 2, ∀ i : Fin 8, i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + 6) ∧ GGIsWeylMatrix MK ∧
        GGIntCartan MK CK ∧
      (∀ i j : Option ↥S,
        (CK i j : ZMod 3) = (i.elim αa fun a => α a) (j.elim ha fun b => h b)) ∧
      (∃ c : ↥S, ∀ j : ↥S, CK none (some j) ≠ 0 ↔ j = c) ∧
      ∃ f : MK.Group ≃* ↥(lr6Group (fun j : ↥S => r j) t),
        ∀ o : Option ↥S, ((f (MK.simple o) : V ≃ₗ[ZMod 3] V)) = o.elim t fun j => r j) →
    (∀ g ∈ lr6Group r t,
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w)) →
    Nat.card ↥(lr6Group r t) ≤ 3 ^ 9 * (6 * (3 - 1) * Nat.factorial 9) →
    ZS.LinWeyl 3 (lr6Group r t)

end CFSG.StandardType

end
