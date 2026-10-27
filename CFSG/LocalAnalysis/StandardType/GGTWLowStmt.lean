module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import Mathlib.GroupTheory.Coxeter.Matrix

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGWeylTypeData (r n c : ℕ) : Prop :=
  (1 ≤ r ∧ n = (r + 1).factorial ∧ c = if r = 1 then 2 else 1) ∨
  (2 ≤ r ∧ n = 2 ^ r * r.factorial ∧ c = 2) ∨
  (4 ≤ r ∧ n = 2 ^ (r - 1) * r.factorial ∧ c = if Even r then 2 else 1) ∨
  (r = 6 ∧ n = 51840 ∧ c = 1) ∨ (r = 7 ∧ n = 2903040 ∧ c = 2) ∨
  (r = 8 ∧ n = 696729600 ∧ c = 2) ∨ (r = 4 ∧ n = 1152 ∧ c = 2) ∨ (r = 2 ∧ n = 12 ∧ c = 2)

@[expose] def ggPZFixRefl {G : Type} [Group G] (p : ℕ) {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) (z : ↥Bs) : Set (MulAut ↥Bs) :=
  {t | t ∈ A ∧ GGIsReflection p t ∧ t z = z}

@[expose] def ggPZOrbit {G : Type} [Group G] (p : ℕ) {Bs : Subgroup G}
    (AJ A : Subgroup (MulAut ↥Bs)) (z : ↥Bs) : Set (MulAut ↥Bs) :=
  {t | ∃ r ∈ AJ, GGIsReflection p r ∧ ∃ g ∈ Subgroup.closure (ggPZFixRefl p A z), t = g * r * g⁻¹}

@[expose] def GGPZInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime]
    (labJ labX : LargeEvenLabel) (X : Subgroup G) (m : ℕ), (X = L ∨ X = K) →
    LargeEvenInLambda2 labJ →
    LargeEvenInLambda2 labX → GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) →
    GGHasLabel labX (↥X ⧸ Subgroup.center ↥X) → ggRowTwoNodeSmall p labJ labX →
    ((labX.tag = .A ∨ labX.tag = .twA) ∧ m = labX.rank) → Nat.card ↥Bs = p ^ m →
    Nat.card ↥(Bs ⊓ J) = p ^ labJ.rank → GGReflGenerated p (ggAutomizer J Bs) →
    ∀ z : ↥Bs, (z : G) ∈ D → (z : G) ∉ Subgroup.zpowers x →
    (z : G) ∉ Subgroup.zpowers y →
      ∃ r n c : ℕ, GGWeylTypeData r n c ∧ labJ.rank ≤ r ∧ r ≤ m ∧
        Nat.card ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
          (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z)) ∣ n ∧
        (Nat.card ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
            (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z)) = n →
          Nat.card ↥(Subgroup.center ↥(Subgroup.closure (ggPZOrbit p (ggAutomizer J Bs)
            (ggAutomizer L Bs ⊔ ggAutomizer K Bs) z))) = c)

@[expose] def ggTWPZFixRefl (p N : ℕ) (gens : Set (Module.End (ZMod p) (GGTWE p N)))
    (z : GGTWE p N) : Set (Module.End (ZMod p) (GGTWE p N)) :=
  {s | s ∈ Submonoid.closure gens ∧ GGTWIsRefl s ∧ s z = z}

@[expose] def ggTWPZJRefl (p N : ℕ) (pos : GGTWPos) : Set (Module.End (ZMod p) (GGTWE p N)) :=
  {s | s ∈ Submonoid.closure ((fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
      ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ) ∧ GGTWIsRefl s}

@[expose] def ggTWPZOrbit (p N : ℕ) (pos : GGTWPos)
    (gens : Set (Module.End (ZMod p) (GGTWE p N))) (z : GGTWE p N) :
    Set (Module.End (ZMod p) (GGTWE p N)) :=
  {t | ∃ r ∈ ggTWPZJRefl p N pos, ∃ g ∈ Submonoid.closure (ggTWPZFixRefl p N gens z),
    ∃ g' ∈ Submonoid.closure (ggTWPZFixRefl p N gens z), g * g' = 1 ∧ t = g * r * g'}

@[expose] noncomputable def ggTWCentreCard {p N : ℕ}
    (M : Submonoid (Module.End (ZMod p) (GGTWE p N))) : ℕ :=
  Nat.card {g : ↥M // ∀ h : ↥M, g * h = h * g}

@[expose] def GGTWPZBadR (p N : ℕ) (pos : GGTWPos)
    (gens : Set (Module.End (ZMod p) (GGTWE p N))) (z : GGTWE p N) (lo hi : ℕ) : Prop :=
  ∀ r n c : ℕ, GGWeylTypeData r n c → lo ≤ r → r ≤ hi →
    ¬ (Nat.card ↥(Submonoid.closure (ggTWPZOrbit p N pos gens z)) ∣ n ∧
      (Nat.card ↥(Submonoid.closure (ggTWPZOrbit p N pos gens z)) = n →
        ggTWCentreCard (Submonoid.closure (ggTWPZOrbit p N pos gens z)) = c))

abbrev GGTWPZBad (p N : ℕ) (pos : GGTWPos)
    (gens : Set (Module.End (ZMod p) (GGTWE p N))) (z : GGTWE p N) : Prop :=
  GGTWPZBadR p N pos gens z (N - 3) (N - 1)

@[expose] def GGTWLowE6Outcome (S : Set (Module.End (ZMod 3) (GGTWE 3 6))) : Prop :=
  51840 ≤ Nat.card ↥(Submonoid.closure S) ∧
    ∃ s : Fin 6 → Module.End (ZMod 3) (GGTWE 3 6), (∀ i, GGTWIsRefl (s i)) ∧
      Submonoid.closure (Set.range s) = Submonoid.closure S ∧
      ∀ i j, (s i * s j) ^ (CoxeterMatrix.E₆.M i j) = 1

@[expose] def GGTWLowE8Outcome (S : Set (Module.End (ZMod 3) (GGTWE 3 9))) : Prop :=
  ∃ h α : Fin 8 → GGTWE 3 9, (∀ i, ggTWdot (α i) (h i) = 2) ∧
    (∀ i j, ggTWdot (α i) (h j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) ∧
    Submonoid.closure (Set.range fun i => ggTWRefl (h i) (α i)) = Submonoid.closure S

@[expose] def GGTWLowSurv1 (p N : ℕ)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) : Prop :=
  ∃ (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ) (ha αa : GGTWE p N) (lam mu : ZMod p),
    GGTWPat1 N pos c0.val m n ∧ GGTWPairs1 p N pos c0 m n ha αa ∧ ggTWdot αa ha = 2 ∧
      ggTWdot αa (ggTWx p N) ≠ 0 ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggTWdot αa (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ¬ GGTWKill .frame p N pos {(ha, αa)} (lam • ggTWx p N + mu • ggTWz p N pos) ∧
      ¬ GGTWKill .other p N pos {(ha, αa)} (lam • ggTWx p N + mu • ggTWz p N pos) ∧
      (∀ c : ZMod p, c ≠ 0 → ¬ GGTWPZBad p N pos (ggTWGens p N {(ha, αa)})
        (ggTWx p N + c • (lam • ggTWx p N + mu • ggTWz p N pos))) ∧
      ¬ Out (ggTWGens p N {(ha, αa)})

@[expose] def GGTWLowSurv2 (p N : ℕ)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) : Prop :=
  ∃ (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))) (ha1 αa1 ha2 αa2 : GGTWE p N)
    (lam mu : ZMod p),
    GGTWPat2 N pos c.val (c₂.map Fin.val) ∧ GGTWPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 ∧
      (ggTWdot αa1 (ggTWx p N) ≠ 0 ∨ ggTWdot αa2 (ggTWx p N) ≠ 0) ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggTWdot αa1 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ggTWdot αa2 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ¬ GGTWKill .frame p N pos {(ha1, αa1), (ha2, αa2)}
        (lam • ggTWx p N + mu • ggTWz p N pos) ∧
      ¬ GGTWKill .other p N pos {(ha1, αa1), (ha2, αa2)}
        (lam • ggTWx p N + mu • ggTWz p N pos) ∧
      (∀ c' : ZMod p, c' ≠ 0 → ¬ GGTWPZBad p N pos (ggTWGens p N {(ha1, αa1), (ha2, αa2)})
        (ggTWx p N + c' • (lam • ggTWx p N + mu • ggTWz p N pos))) ∧
      ¬ Out (ggTWGens p N {(ha1, αa1), (ha2, αa2)})

@[expose] def GGTWLowCells (p N : ℕ) (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) : Prop :=
  ¬ GGTWLowSurv1 p N Out ∧ ¬ GGTWLowSurv2 p N Out

end CFSG.StandardType

end
