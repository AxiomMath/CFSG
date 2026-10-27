module

public import CFSG.LocalAnalysis.StandardType.GGQTwoModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

structure GGQ2Lin (p : ℕ) [Fact p.Prime] where
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  coxeter : CoxeterMatrix ι
  cartan : Matrix ι ι ℤ
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod p) V]
  coroot : ι → V
  root : ι → Dual (ZMod p) V
  a : ι
  b : ι
  a_ne_b : a ≠ b
  a_leaf : ∃! c, c ≠ a ∧ cartan a c ≠ 0
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)

attribute [instance] GGQ2Lin.instFintype GGQ2Lin.instDecEq GGQ2Lin.instAddCommGroup
  GGQ2Lin.instModule

namespace GGQ2Lin

theorem root_coroot_self {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (i : D.ι) :
    D.root i (D.coroot i) = 2 := by
  rw [D.pairing, D.isCartan.1]; norm_num

@[expose] noncomputable def simpleRefl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    D.V ≃ₗ[ZMod p] D.V :=
  Module.reflection (D.root_coroot_self k)

@[expose] noncomputable def parab {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (S : Set D.ι) :
    Subgroup (D.V ≃ₗ[ZMod p] D.V) :=
  Subgroup.closure (D.simpleRefl '' S)

@[expose] noncomputable def weyl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    Subgroup (D.V ≃ₗ[ZMod p] D.V) :=
  D.parab Set.univ

@[expose] def rootPairs {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Set (Dual (ZMod p) D.V × D.V) :=
  {q | ∃ (k : D.ι) (w : D.V ≃ₗ[ZMod p] D.V), w ∈ D.weyl ∧ q.2 = w (D.coroot k) ∧
    q.1 = (D.root k).comp (w.symm : D.V →ₗ[ZMod p] D.V)}

@[expose] def Basis {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Prop :=
  LinearIndependent (ZMod p) D.coroot ∧ Fintype.card D.ι = finrank (ZMod p) D.V

@[expose] def CaseII {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Prop :=
  Fintype.card D.ι = finrank (ZMod p) D.V ∧
    LinearIndependent (ZMod p) (fun k : {k // k ≠ D.a} => D.coroot k) ∧
      ¬ LinearIndependent (ZMod p) D.coroot

end GGQ2Lin

@[expose] def IsReflLin {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (t : V ≃ₗ[ZMod p] V) : Prop :=
  ∃ (c : V) (φ : Dual (ZMod p) V) (h : φ c = 2), t = Module.reflection h

@[expose] def reflGp {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) : Subgroup (V ≃ₗ[ZMod p] V) :=
  Subgroup.closure {t | t ∈ A ∧ IsReflLin t}

@[expose] def GGQ2Lin.FCell {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) : Prop :=
  Fintype.card D.ι = 4 ∧ Nat.card (reflGp A) = 1152

section Model

@[expose] def GGQTwoModel.toLin {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) : GGQ2Lin p where
  ι := M.ι
  coxeter := M.coxeter
  cartan := M.cartan
  V := M.V
  coroot := M.coroot
  root := M.root
  a := M.a
  b := M.b
  a_ne_b := M.a_ne_b
  a_leaf := M.a_leaf
  isWeyl := M.isWeyl
  isCartan := M.isCartan
  pairing := M.pairing

@[expose] noncomputable def GGQTwoModel.parabL {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (S : Set M.ι) : Subgroup (M.V ≃ₗ[ZMod p] M.V) :=
  M.toLin.parab S

@[expose] noncomputable def GGQTwoModel.linGroup {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) :
    Subgroup (M.V ≃ₗ[ZMod p] M.V) :=
  (ggAutomizer ⊤ Bs).map (ggLin (p := p) M.model)

@[expose] noncomputable def GGQTwoModel.xV {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) : M.V :=
  M.model (Additive.ofMul ⟨x, M.hx⟩)

@[expose] noncomputable def GGQTwoModel.yV {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) : M.V :=
  M.model (Additive.ofMul ⟨y, M.hy⟩)

end Model

end CFSG.StandardType

end
