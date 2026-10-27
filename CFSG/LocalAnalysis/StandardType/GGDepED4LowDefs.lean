module

public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4Defs
public import CFSG.LocalAnalysis.StandardType.GGDepEDefs
public import CFSG.LocalAnalysis.StandardType.GGHLLines
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4LowCfg {G : Type} [Group G] [Finite G] (p k : ℕ) [Fact p.Prime]
    (Bs L J K : Subgroup G) (x y : G) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (_ : DecidableEq Λ) (b₁ b₂ : Λ) (Λa : Type)
    (_ : Fintype Λa) (_ : DecidableEq Λa)
    (MK : CoxeterMatrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa))
    (CK : Matrix ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) ℤ)
    (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V) (ι : Additive ↥Bs ≃+ V)
    (e : Fin 6 ≃ Λ) (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod p) V) (xV yV : V) (hx : x ∈ Bs) (hy : y ∈ Bs),
    xV = ι (Additive.ofMul ⟨x, hx⟩) ∧ yV = ι (Additive.ofMul ⟨y, hy⟩) ∧
      GGDepED4Core p k Bs L J K b₁ b₂ MK CK ι e φ h α xV ∧
      Module.finrank (ZMod p) V = 6 ∧
      (k = 1 → ∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
        GGLinRefl g → g xV = xV → GGHLLines (ggHLRoots
          (fun i : Λ => ggLin (p := p) ι (φ (Sum.inl i))) (fun i : Λ => h (Sum.inl i))) xV g) ∧
      yV ≠ 0 ∧
      (∀ i : {i : Λ // i ≠ b₁ ∧ i ≠ b₂}, ggLin (p := p) ι (φ (Sum.inl i.1)) yV = yV) ∧
      (∀ a : Λa, ggLin (p := p) ι (φ (Sum.inr a)) yV = yV) ∧
      (k = 1 → ∀ g ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o)),
        GGLinRefl g → g yV = yV → GGHLLines (ggHLRoots
          (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => ggLin (p := p) ι (φ (o.map Subtype.val id)))
          (fun o : {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa => h (o.map Subtype.val id))) yV g)

@[expose] def ggDepELx : GGDepAE 3 6 := ![0, 0, 0, 0, 0, 1]

@[expose] def ggDepELh (i : Fin 6) : GGDepAE 3 6 :=
  ![![1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 0], ![1, 0, 2, 0, 1, 0]] i

@[expose] def ggDepELα (i : Fin 6) : GGDepAE 3 6 :=
  ![![2, 0, 2, 0, 0, 0], ![0, 2, 0, 2, 0, 0], ![2, 0, 2, 2, 0, 0], ![0, 2, 2, 2, 2, 0],
    ![0, 0, 0, 2, 2, 0], ![0, 0, 0, 0, 2, 0]] i

@[expose] def ggDepELz : GGDepAE 3 6 := ![2, 1, 2, 2, 1, 0]

theorem ggDepELpair (i j : Fin 6) :
    ggDepAdot (ggDepELα i) (ggDepELh j) = (((CartanMatrix.E 6) i j : ℤ) : ZMod 3) := by
  rw [CartanMatrix.E_six_eq]
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem ggDepELα_x (i : Fin 6) : ggDepAdot (ggDepELα i) ggDepELx = 0 := by
  fin_cases i <;> decide

theorem ggDepELz_ker (c : Fin 6) (hc : GGDepED4In c) : ggDepAdot (ggDepELα c) ggDepELz = 0 := by
  obtain ⟨h0, h5⟩ := hc
  fin_cases c
  · exact absurd rfl h0
  · decide
  · decide
  · decide
  · decide
  · exact absurd rfl h5

@[expose] noncomputable def ggDepELrefl (i : Fin 6) : Module.End (ZMod 3) (GGDepAE 3 6) :=
  ggDepARefl (ggDepELh i) (ggDepELα i)

@[expose] def GGDepELIsRefl (s : Module.End (ZMod 3) (GGDepAE 3 6)) : Prop :=
  ∃ c f : GGDepAE 3 6, ggDepAdot f c = 2 ∧ s = ggDepARefl c f

@[expose] def GGDepELPairs1 (c0 : Fin 6) (ha αa : GGDepAE 3 6) : Prop :=
  ∀ c : Fin 6, GGDepED4In c →
    ggDepAdot αa (ggDepELh c) = (if c = c0 then (-1 : ZMod 3) else 0) ∧
      ggDepAdot (ggDepELα c) ha = (if c = c0 then (-1 : ZMod 3) else 0)

@[expose] def GGDepELPairs2 (c c' : Fin 6) (ha1 αa1 ha2 αa2 : GGDepAE 3 6) : Prop :=
  (∀ d : Fin 6, GGDepED4In d →
      ggDepAdot αa1 (ggDepELh d) = (if d = c then (-1 : ZMod 3) else 0) ∧
        ggDepAdot (ggDepELα d) ha1 = (if d = c then (-1 : ZMod 3) else 0) ∧
        ggDepAdot αa2 (ggDepELh d) = (if d = c' then (-1 : ZMod 3) else 0) ∧
        ggDepAdot (ggDepELα d) ha2 = (if d = c' then (-1 : ZMod 3) else 0)) ∧
    ggDepAdot αa1 ha2 = 0 ∧ ggDepAdot αa2 ha1 = 0 ∧ ggDepAdot αa1 ha1 = 2 ∧
      ggDepAdot αa2 ha2 = 2

inductive GGDepELMode : Type
  | frame
  | other
  deriving DecidableEq

@[expose] def ggDepELFrameGens : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  Set.range fun i : Fin 6 => ggDepELrefl i

@[expose] def ggDepELGens (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) :
    Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  ggDepELFrameGens ∪ (fun t => ggDepARefl t.1 t.2) '' news

@[expose] def ggDepELOGens (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) :
    Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  (fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) '' Set.univ ∪
    (fun t => ggDepARefl t.1 t.2) '' news

@[expose] def ggDepELOCentres (news : Set (GGDepAE 3 6 × GGDepAE 3 6)) : Set (GGDepAE 3 6) :=
  (fun i : {i : Fin 6 // GGDepED4In i} => ggDepELh i.1) '' Set.univ ∪ Prod.fst '' news

@[expose] def ggDepELRoots (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (cs : Set (GGDepAE 3 6)) : Set (GGDepAE 3 6) :=
  {v | ∃ w ∈ Submonoid.closure gens, ∃ c ∈ cs, v = w c}

@[expose] def GGDepELMovesLine (R : Set (GGDepAE 3 6)) (y : GGDepAE 3 6)
    (s : Module.End (ZMod 3) (GGDepAE 3 6)) : Prop :=
  s y = y ∧ ∃ v ∈ R, ∀ w ∈ R, ∀ c d : ZMod 3, c ≠ 0 → s v ≠ c • w + d • y

@[expose] def GGDepELKill (mode : GGDepELMode) (news : Set (GGDepAE 3 6 × GGDepAE 3 6))
    (y : GGDepAE 3 6) : Prop :=
  (∃ g ∈ Submonoid.closure (ggDepELGens news), GGDepAIsTv g) ∨
    ∃ s ∈ Submonoid.closure (ggDepELGens news), GGDepELIsRefl s ∧
      match mode with
      | .frame => GGDepELMovesLine (ggDepELRoots ggDepELFrameGens (Set.range ggDepELh))
          ggDepELx s
      | .other => GGDepELMovesLine (ggDepELRoots (ggDepELOGens news) (ggDepELOCentres news)) y s

@[expose] def ggDepELPZFixRefl (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (z : GGDepAE 3 6) : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  {s | s ∈ Submonoid.closure gens ∧ GGDepELIsRefl s ∧ s z = z}

@[expose] def ggDepELPZJRefl : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  {s | s ∈ Submonoid.closure ((fun i : {i : Fin 6 // GGDepED4In i} => ggDepELrefl i.1) ''
      Set.univ) ∧ GGDepELIsRefl s}

@[expose] def ggDepELPZOrbit (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (z : GGDepAE 3 6) : Set (Module.End (ZMod 3) (GGDepAE 3 6)) :=
  {t | ∃ r ∈ ggDepELPZJRefl, ∃ g ∈ Submonoid.closure (ggDepELPZFixRefl gens z),
    ∃ g' ∈ Submonoid.closure (ggDepELPZFixRefl gens z), g * g' = 1 ∧ t = g * r * g'}

@[expose] noncomputable def ggDepELCentreCard
    (M : Submonoid (Module.End (ZMod 3) (GGDepAE 3 6))) : ℕ :=
  Nat.card {g : ↥M // ∀ h : ↥M, g * h = h * g}

@[expose] def GGDepELPZBad (gens : Set (Module.End (ZMod 3) (GGDepAE 3 6)))
    (z : GGDepAE 3 6) : Prop :=
  ∀ r n c : ℕ, GGWeylTypeData r n c → 4 ≤ r → r ≤ 6 →
    ¬ (Nat.card ↥(Submonoid.closure (ggDepELPZOrbit gens z)) ∣ n ∧
      (Nat.card ↥(Submonoid.closure (ggDepELPZOrbit gens z)) = n →
        ggDepELCentreCard (Submonoid.closure (ggDepELPZOrbit gens z)) = c))

@[expose] def GGDepED4LowSurv1 : Prop :=
  ∃ (c0 : Fin 6) (ha αa : GGDepAE 3 6) (lam mu : ZMod 3),
    GGDepED4Leaf c0 ∧ GGDepELPairs1 c0 ha αa ∧ ggDepAdot αa ha = 2 ∧
      ggDepAdot αa ggDepELx ≠ 0 ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggDepAdot αa (lam • ggDepELx + mu • ggDepELz) = 0 ∧
      ¬ GGDepELKill .frame {(ha, αa)} (lam • ggDepELx + mu • ggDepELz) ∧
      ¬ GGDepELKill .other {(ha, αa)} (lam • ggDepELx + mu • ggDepELz) ∧
      (∀ c : ZMod 3, c ≠ 0 → ¬ GGDepELPZBad (ggDepELGens {(ha, αa)})
        (ggDepELx + c • (lam • ggDepELx + mu • ggDepELz)))

@[expose] def GGDepED4LowSurv2 : Prop :=
  ∃ (c c' : Fin 6) (ha1 αa1 ha2 αa2 : GGDepAE 3 6) (lam mu : ZMod 3),
    GGDepED4Leaf c ∧ GGDepED4Leaf c' ∧ c ≠ c' ∧ GGDepELPairs2 c c' ha1 αa1 ha2 αa2 ∧
      (ggDepAdot αa1 ggDepELx ≠ 0 ∨ ggDepAdot αa2 ggDepELx ≠ 0) ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggDepAdot αa1 (lam • ggDepELx + mu • ggDepELz) = 0 ∧
      ggDepAdot αa2 (lam • ggDepELx + mu • ggDepELz) = 0 ∧
      (¬ ∃ g ∈ Submonoid.closure (ggDepELGens {(ha1, αa1), (ha2, αa2)}), GGDepAIsTv g) ∧
      (∀ c'' : ZMod 3, c'' ≠ 0 → ¬ GGDepELPZBad (ggDepELGens {(ha1, αa1), (ha2, αa2)})
        (ggDepELx + c'' • (lam • ggDepELx + mu • ggDepELz)))

@[expose] def GGDepED4LowCells : Prop :=
  ¬ GGDepED4LowSurv1 ∧ ¬ GGDepED4LowSurv2

end CFSG.StandardType

end
