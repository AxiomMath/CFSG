module

public import CFSG.LocalAnalysis.StandardType.GGResIIClassify
public import CFSG.LocalAnalysis.StandardType.GGResIITransport

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure GGResIIHyp (p : ℕ) [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b : Λ)
    (ML : CoxeterMatrix Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (g : Option Λ → (V ≃ₗ[ZMod p] V)) (h : Option Λ → V)
    (α : Option Λ → Module.Dual (ZMod p) V) (x y : V) : Prop where
  hp2 : p ≠ 2
  hCL : GGIntCartan ML CL
  hKt : GGResIINonegType CK
  hconn : GGDeletedConnected ML b
  hg : ∀ o w, g o w = w - α o w • h o
  hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p)
  hK : ∀ o o' : Option {i : Λ // i ≠ b},
    α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod p)
  hLI : LinearIndependent (ZMod p) (fun i : Λ => h (some i))
  hdep : ¬ LinearIndependent (ZMod p) h
  hxL : ∀ i : Λ, α (some i) x = 0
  hfix : ∀ w : V, (∀ i : Λ, α (some i) w = 0) → w ∈ Submodule.span (ZMod p) {x}
  hxa : α none x ≠ 0
  hyK : ∀ o : Option {i : Λ // i ≠ b}, α (o.map Subtype.val) y = 0
  hyx : y ∉ Submodule.span (ZMod p) {x}

@[expose] def GGResIIFConcl (p : ℕ) [Fact p.Prime] {Λ : Type} (b : Λ) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (g : Option Λ → (V ≃ₗ[ZMod p] V)) (h : Option Λ → V)
    (α : Option Λ → Module.Dual (ZMod p) V) : Prop :=
  (∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
    (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Λ, j ≠ b ∧ j' ≠ b ∧
      α (some j') (ψ (h (some j))) * α (some j) (ψ⁻¹ (h (some j'))) ∉
        ({0, 1, 2, 3, 4} : Set (ZMod p))) ∨
    ZS.LinWeyl p (Subgroup.closure (Set.range g))

variable {p : ℕ} [Fact p.Prime] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
  {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
  {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {V : Type}
  [AddCommGroup V] [Module (ZMod p) V] {g : Option Λ → (V ≃ₗ[ZMod p] V)} {h : Option Λ → V}
  {α : Option Λ → Module.Dual (ZMod p) V} {x y : V}

theorem ggResII_dispatch_leaf [Module.Finite (ZMod p) V] (H : GGResIIHyp p b ML CL CK g h α x y)
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    (hCsl : C.IsSimplyLaced) (hCdiag : ∀ i, C i i = 2) {ib : Fin n} (hib : e ib = b)
    (targets : List (ℕ × ℕ × ℕ × ℕ)) (allowed : List (Fin n))
    (htA : 2 ≤ n → ggInv (CartanMatrix.A n) ∈ targets)
    (htD : 5 ≤ n → Odd n → ggInv (CartanMatrix.D n) ∈ targets)
    (htE : ∀ hn : 6 = n, ggInv ((CartanMatrix.E 6).submatrix (Fin.cast hn.symm) (Fin.cast hn.symm))
      ∈ targets)
    (hcert : ∀ r : Fin n → Bool, ggInv (ggKmat C ib r) ∈ targets →
      ∃ ic ∈ allowed, ic ≠ ib ∧ ∀ j, j ≠ ib → r j = decide (j = ic))
    (hshapes : ∀ ic ∈ allowed, GGResIIShapeOK C ib ic) :
    GGResIIFConcl p b g h α := by
  obtain ⟨ic, hic, hbc, hrow, hcol, haa⟩ :=
    ggResII_arow H.hL H.hK H.hKt e hCe hCsl hCdiag hib targets allowed htA htD htE hcert
  exact ggResII_transport H.hp2 H.hg H.hL H.hK H.hLI H.hdep H.hxL H.hfix H.hxa H.hyK H.hyx e hCe
    hCdiag hib (Ne.symm hbc) hrow hcol haa (hshapes ic hic)

theorem ggResII_dispatch_cut (H : GGResIIHyp p b ML CL CK g h α x y) {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ) (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (S : Finset (Fin n)) (j₁ j₂ : Fin n) (h₁ : j₁ ∈ S)
    (h₂ : j₂ ∉ S) (hj₁ : j₁ ≠ ib) (hj₂ : j₂ ≠ ib)
    (hcut : ∀ ac : Fin n × Fin n, ac.1 ∈ S → ac.2 ∉ S → ac.2 ≠ ib → C ac.1 ac.2 = 0) :
    GGResIIFConcl p b g h α :=
  (ggResII_leaf_cut H.hCL H.hconn e hCe hib S j₁ j₂ h₁ h₂ hj₁ hj₂
    fun a ha c hc hcb => hcut (a, c) ha hc hcb).elim

end CFSG.StandardType
