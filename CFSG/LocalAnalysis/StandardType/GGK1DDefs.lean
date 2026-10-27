module

public import CFSG.LocalAnalysis.StandardType.GGK1Cover
public import CFSG.LocalAnalysis.StandardType.GGK1Defs
public import CFSG.LocalAnalysis.StandardType.GGK1SigmaAbs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusRootGenIso

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry reciprocalPolynomial isometryCentralizer
  IsOrbitRepresentatives)
open CFSG.RankThree.Classical (IsReciprocalTransversal)

@[expose] noncomputable def ggK1DLin {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) : (ι → K) ≃ₗ[K] (ι → K) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin x)

@[expose] noncomputable def ggK1DOrthEnd {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (x : GL ι K) : Module.End K (ι → K) :=
  (ggK1DLin x : Module.End K (ι → K))

@[expose] noncomputable def ggK1DSelfDualFactors {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (x : GL ι K) : Finset K[X] := by
  classical
  exact (primaryFactors (ggK1DOrthEnd x)).filter (fun h => h ≠ X - 1)

structure GGK1DMultOf (p nf d r : ℕ) (K : Type) [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (x : GL ι K) (m : List ℕ) : Prop where
  length_eq : m.length = (p - 1) / 2 + 1
  sum_eq : m.sum = r
  head_eq : m.headD 0 = Module.finrank K (primaryComponent (ggK1DOrthEnd x) (X - 1)) / 2
  blocks_eq : (d = 1 ∧ ∃ P : Finset K[X], IsReciprocalTransversal (ggK1DOrthEnd x) P ∧
      Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
        P.val.map (primaryMultiplicity (ggK1DOrthEnd x))) ∨
    (d = 2 ∧ Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      (ggK1DSelfDualFactors x).val.map (primaryMultiplicity (ggK1DOrthEnd x)))

inductive ggK1DCo_Kind where
  | om (eps : Bool) (m : ℕ)
  | sl (m : ℕ)
  | su (m : ℕ)
  deriving DecidableEq

@[expose] def ggK1DCo_dummyOrbit (nf : ℕ) : GGKacOrbit := ⟨⟨.A, 0, nf⟩, false⟩

@[expose] def ggK1DCo_kindOrbits (nf : ℕ) : ggK1DCo_Kind → List GGKacOrbit
  | .om eps m => if m ≤ 1 then [ggK1DCo_dummyOrbit nf] else ggMultV0 m eps nf
  | .sl m => if m ≤ 1 then [ggK1DCo_dummyOrbit nf] else [ggMultBlockA (m - 1) nf 1]
  | .su m => if m ≤ 1 then [ggK1DCo_dummyOrbit nf] else [ggMultBlockA (m - 1) nf 2]

@[expose] def ggK1DCo_Kind.hasOrbit : ggK1DCo_Kind → Bool
  | .om _ m => decide (2 ≤ m)
  | .sl m => decide (2 ≤ m)
  | .su m => decide (2 ≤ m)

@[expose] def ggK1DCo_expectedKindList (p nf d : ℕ) (tw : Bool) (m : List ℕ) : List ggK1DCo_Kind :=
  [ggK1DCo_Kind.om (ggMultEps0 p d tw m) (m.headD 0)] ++
    (((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0))).map
        (fun j => if d = 1 then ggK1DCo_Kind.sl (m.getD j 0)
          else ggK1DCo_Kind.su (m.getD j 0)))

@[expose] def ggK1DCo_expectedOrbits (p nf d : ℕ) (tw : Bool) (m : List ℕ) : List GGKacOrbit :=
  (((ggK1DCo_expectedKindList p nf d tw m).filter
      (fun k => ggK1DCo_Kind.hasOrbit k)).map (ggK1DCo_kindOrbits nf)).flatten

@[expose] def ggK1DCo_expectedKinds (p nf d : ℕ) (tw : Bool) (m : List ℕ) : Multiset ggK1DCo_Kind :=
  ↑(ggK1DCo_expectedKindList p nf d tw m)

@[expose] def ggK1DCo_OrbitModel (nf : ℕ) (K : Type) [Field K] (o : GGKacOrbit)
    (H : Type) [Group H] : Prop :=
  match o.lab.tag with
  | .A =>
      if o.lab.rank = 1 ∧ o.lab.n = 2 * nf then
        ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (Nat.card K) ^ 2 ∧
          Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin 2) E)
      else Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin (o.lab.rank + 1)) K)
  | .twA =>
      ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (Nat.card K) ^ 2 ∧
        Nonempty (H ≃* ↥(StatedSU (o.lab.rank + 1) (Nat.card K) E))
  | .D => Nonempty (H ≃* StatedOmega (StatedQuadPlus o.lab.rank K))
  | .twD =>
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (H ≃* StatedOmega (StatedQuadMinus o.lab.rank K b c))
  | _ => False

open Classical in
structure OrthPrimaryBlocks (K : Type) [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (nf p : ℕ) (x : V ≃ₗ[K] V) where
  ι : Type
  [fintype : Fintype ι]
  A : ι → Subgroup (V ≃ₗ[K] V)
  kind : ι → ggK1DCo_Kind
  blk : ι → List GGKacOrbit
  blk_eq : ∀ i, blk i = ggK1DCo_kindOrbits nf (kind i)
  rep : ∃ (Rep : Finset K[X]) (e : ι ≃ ↥Rep), IsOrbitRepresentatives x Rep ∧
    ∀ i, kind i =
      if (e i : K[X]) = X - 1 then
        ggK1DCo_Kind.om (if CFSG.GroupTheory.WeirSylow.IsPlusType
              (Q.restrict (primaryComponent x.toLinearMap (X - 1))) then true else false)
          (Module.finrank K (primaryComponent x.toLinearMap (X - 1)) / 2)
      else if reciprocalPolynomial (e i : K[X]) = (e i : K[X]) then
        ggK1DCo_Kind.su (primaryMultiplicity x.toLinearMap (e i : K[X]))
      else ggK1DCo_Kind.sl (primaryMultiplicity x.toLinearMap (e i : K[X]))
  sub : (i : ι) → Fin (blk i).length → Subgroup (V ≃ₗ[K] V)
  hsub_le : ∀ i j, sub i j ≤ A i
  hcomm : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b
  sub_join : ∀ i : ι, ⨆ j : Fin (blk i).length, sub i j = A i
  hcomm_sub : ∀ (i : ι) (j j' : Fin (blk i).length), j ≠ j' →
    ∀ a ∈ sub i j, ∀ b ∈ sub i j', Commute a b
  hjoin : ⨆ q : Σ i, Fin (blk i).length, sub q.1 q.2 =
    isometryCentralizer Q x ⊓
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  hindep : iSupIndep fun q : Σ i, Fin (blk i).length => sub q.1 q.2
  htame : ∀ q : Σ i, Fin (blk i).length,
    CFSG.IsQuasisimple ↥⁅sub q.1 q.2, sub q.1 q.2⁆ ∨ Group.IsSolvable ↥(sub q.1 q.2)
  isInternal : iSupIndep (fun h : primaryFactors x.toLinearMap =>
      primaryComponent x.toLinearMap (h : K[X])) ∧
    (⨆ h : primaryFactors x.toLinearMap, primaryComponent x.toLinearMap (h : K[X])) = ⊤
  fixed_eq : primaryComponent x.toLinearMap (X - 1) = LinearMap.ker (x.toLinearMap - 1)
  fixed_nondegenerate :
    (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) (primaryComponent x.toLinearMap (X -
        1))).Nondegenerate
  nontrivial : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
    orderOf (AdjoinRoot.root h) = p
  rank : ∃ s : ℕ, Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * s
  paired_model : ∀ i m, kind i = .sl m →
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (h : K[X]),
      h ∈ primaryFactors x.toLinearMap ∧ h ≠ reciprocalPolynomial h ∧
      Fintype.card E = (Nat.card K) ^ h.natDegree ∧
      m = primaryMultiplicity x.toLinearMap h ∧
      Nonempty (↥(A i) ≃* Matrix.GeneralLinearGroup (Fin m) E)
  selfDual_model : ∀ i m, kind i = .su m →
    ∃ (E : Type) (_ : Field E) (_ : Fintype E)
      (hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf E)
      (W : Type) (_ : AddCommGroup W) (_ : Module E W) (_ : FiniteDimensional E W)
      (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E),
      Hf.IsSymm ∧ Hf.SeparatingLeft ∧ Module.finrank E W = m ∧
        Nonempty (↥(A i) ≃* CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup Hf)
  fixed_model : ∀ i eps m, kind i = .om eps m →
    Module.finrank K (primaryComponent x.toLinearMap (X - 1)) = 2 * m ∧
    (eps = true ↔
      CFSG.GroupTheory.WeirSylow.IsPlusType
        (Q.restrict (primaryComponent x.toLinearMap (X - 1)))) ∧
    (3 ≤ m → if eps then Nonempty (↥(A i) ≃* StatedOmega (StatedQuadPlus m K))
      else ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (↥(A i) ≃* StatedOmega (StatedQuadMinus m K b c))) ∧
    (m = 2 → eps = true → ∀ j : Fin (blk i).length,
      Nonempty (↥(sub i j) ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
    (m = 2 → eps = false → ∃ (E : Type) (_ : Field E) (_ : Fintype E),
      Fintype.card E = (Nat.card K) ^ 2 ∧
        Nonempty (↥(A i) ≃* Matrix.SpecialLinearGroup (Fin 2) E)) ∧
    (m ≤ 1 → ∀ a ∈ A i, ∀ b ∈ A i, Commute a b)

structure ggK1DCo_Family (p nf d : ℕ) (tw : Bool) (r : ℕ) (m : List ℕ) (K : Type) [Field K] {ι :
    Type} [Fintype ι]
    [DecidableEq ι] (Q : (ι → K) → K) (x : ↥(LargeEvenOmega Q)) where
  blkIdx : Type
  [fintype : Fintype blkIdx]
  blk : blkIdx → List GGKacOrbit
  kind : blkIdx → ggK1DCo_Kind
  blk_eq : ∀ i, blk i = ggK1DCo_kindOrbits nf (kind i)
  A : (i : blkIdx) → Fin (blk i).length → Subgroup (LargeEvenProj (LargeEvenOmega Q))
  hcomm : ∀ q q' : Σ i, Fin (blk i).length, q ≠ q' →
    ∀ a ∈ A q.1 q.2, ∀ b ∈ A q'.1 q'.2, Commute a b
  hjoin : ⨆ q : Σ i, Fin (blk i).length, A q.1 q.2 =
    Subgroup.centralizer ({LargeEvenProjMk (LargeEvenOmega Q) x} :
      Set (LargeEvenProj (LargeEvenOmega Q)))
  hindep : iSupIndep fun q : Σ i, Fin (blk i).length => A q.1 q.2
  htame : ∀ q : Σ i, Fin (blk i).length,
    CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ ∨ Group.IsSolvable ↥(A q.1 q.2)
  kind_multiset : (Finset.univ : Finset blkIdx).val.map kind =
    ggK1DCo_expectedKinds p nf d tw m
  hmem : ∀ q : Σ i, Fin (blk i).length,
    CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ →
      (blk q.1).get q.2 ∈ (ggMultDatumD p nf d tw m).orbits
  hqs : ∀ q : Σ i, Fin (blk i).length,
    CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ → ((blk q.1).get q.2).qs = true
  hlab : ∀ (q : Σ i, Fin (blk i).length),
    (hq : CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆) →
      GGHasLabel ((blk q.1).get q.2).lab
        (↥⁅A q.1 q.2, A q.1 q.2⁆ ⧸ Subgroup.center ↥⁅A q.1 q.2, A q.1 q.2⁆)
  hreal : ∀ o ∈ (ggMultDatumD p nf d tw m).orbits, o.qs = true →
    ∃ q : Σ i, Fin (blk i).length,
      CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆ ∧ (blk q.1).get q.2 = o
  hbij : ∃ g : {q : Σ i, Fin (blk i).length //
        CFSG.IsQuasisimple ↥⁅A q.1 q.2, A q.1 q.2⁆} ≃
      {k : Fin (ggMultDatumD p nf d tw m).orbits.length //
        ((ggMultDatumD p nf d tw m).orbits.get k).qs = true},
    ∀ q, (ggMultDatumD p nf d tw m).orbits.get (g q).1 = (blk q.1.1).get q.1.2
  hsolv : ∀ o ∈ (ggMultDatumD p nf d tw m).orbits, o.qs = false →
    ∃ q : Σ i, Fin (blk i).length, (blk q.1).get q.2 = o ∧
      ∃ t ∈ A q.1 q.2, t ^ p = 1 ∧ ∃ a ∈ A q.1 q.2, a * t ≠ t * a

end CFSG.StandardType

end
