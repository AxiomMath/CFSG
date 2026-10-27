module

public import CFSG.LocalAnalysis.StandardType.GGK1Defs
public import CFSG.LocalAnalysis.StandardType.GGK1Cover
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldLangSL
public import CFSG.LieType.SemisimpleCentralizers.HeldLinearComponents
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.LocalAnalysis.StandardType.GGK1SigmaAbs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

@[expose] noncomputable def ggK1A_glEnd {N : ℕ} {K : Type} [Field K] (g : GL (Fin N) K) :
    Module.End K (Fin N → K) :=
  Matrix.toLin' (g : Matrix (Fin N) (Fin N) K)

@[expose] noncomputable def ggK1A_selfDualFactors {N : ℕ} {K : Type} [Field K]
    (g : GL (Fin N) K) : Finset K[X] := by
  classical
  exact (primaryFactors (ggK1A_glEnd g)).filter (fun a => a ≠ X - 1)

structure GGK1AMultOf (p nf N : ℕ) (tw : Bool) (K : Type) [Field K]
    (g : GL (Fin N) K) (m : List ℕ) : Prop where
  length_eq : m.length = p
  sum_eq : m.sum = N
  head_eq : m.getD 0 0 = Module.finrank K (primaryComponent (ggK1A_glEnd g) (X - 1))
  blocks_eq :
    (((ggMultOrd p nf = 2 ∧ tw = false) ∧
        (∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) ∧
        Multiset.ofList (((List.range ((p - 1) / 2)).map (fun j => m.getD (j + 1) 0)).filter
            (fun j => decide (j ≠ 0))) =
          (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g))) ∨
      (¬ (ggMultOrd p nf = 2 ∧ tw = false) ∧
        (ggMultOrd p nf = 1 ∧ tw = true →
          ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) ∧
        Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
          (ggK1A_selfDualFactors g).val.map (primaryMultiplicity (ggK1A_glEnd g))))

inductive ggK1ACo_Kind where
  | sl (m : ℕ) (e : ℕ)
  | su (m : ℕ) (e : ℕ)
  deriving DecidableEq

@[expose] def ggK1ACo_Kind.hasOrbit : ggK1ACo_Kind → Bool
  | .sl 1 _ => false
  | .su 1 _ => false
  | _ => true

@[expose] def ggK1ACo_kindOrbit (nf : ℕ) : ggK1ACo_Kind → GGKacOrbit
  | .sl 1 _ => ⟨⟨.A, 0, nf⟩, false⟩
  | .su 1 _ => ⟨⟨.A, 0, nf⟩, false⟩
  | .sl m e => ggMultBlockA (m - 1) (e * nf) 1
  | .su m e => ggMultBlockA (m - 1) (e * nf) 2

@[expose] def ggK1ACo_expectedKindList (p nf : ℕ) (tw : Bool) (m : List ℕ) : List ggK1ACo_Kind :=
  let d := ggMultOrd p nf
  let trivial := (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  if trivial then
    ((List.range p).filter (fun j => decide (0 < m.getD j 0))).map
      (fun j => if tw then .su (m.getD j 0) 1 else .sl (m.getD j 0) 1)
  else
    ((if 0 < m.headD 0 then [if tw then .su (m.headD 0) 1 else .sl (m.headD 0) 1] else []) ++
      ((List.range ((p - 1) / 2 + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).map
        (fun j => .sl (m.getD j 0) 2))

@[expose] def ggK1ACo_expectedKinds (p nf : ℕ) (tw : Bool) (m : List ℕ) :
    Multiset ggK1ACo_Kind :=
  ↑(ggK1ACo_expectedKindList p nf tw m)

@[expose] def ggK1ACo_orbitKindList (p nf : ℕ) (tw : Bool) (m : List ℕ) : List ggK1ACo_Kind :=
  (ggK1ACo_expectedKindList p nf tw m).filter (fun k => ggK1ACo_Kind.hasOrbit k)

@[expose] def ggK1ACo_Kind.Model (nf : ℕ) (K : Type) [Field K] (kind : ggK1ACo_Kind)
    (H : Type) [Group H] : Prop :=
  match kind with
  | .sl m e =>
      ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (2 ^ nf) ^ e ∧
        Nonempty (H ≃* Matrix.SpecialLinearGroup (Fin m) E)
  | .su m e =>
      ∃ (E : Type) (_ : Field E) (_ : Fintype E), Fintype.card E = (2 ^ nf) ^ (2 * e) ∧
        Nonempty (H ≃* ↥(StatedSU m ((2 ^ nf) ^ e) E))

structure ggK1ACo_Blocks (p nf : ℕ) (tw : Bool) (K : Type) [Field K] (N : ℕ)
    (G : Type) [Group G] (xhat : G) (m : List ℕ) where
  ι : Type
  [fintype : Fintype ι]
  A : ι → Subgroup G
  kind : ι → ggK1ACo_Kind
  hcomm : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b
  hle : ∀ i : ι, A i ≤ Subgroup.centralizer ({xhat} : Set G)
  kind_multiset : (Finset.univ : Finset ι).val.map kind = ggK1ACo_expectedKinds p nf tw m
  hmodel : ∀ i : ι, ggK1ACo_Kind.Model nf K (kind i) ↥(A i)
  hqsKind : ∀ i : ι, CFSG.IsQuasisimple ↥(A i) ↔ (ggK1ACo_kindOrbit nf (kind i)).qs = true
  hsolv : ∀ i : ι, (ggK1ACo_Kind.hasOrbit (kind i)) = true →
    (ggK1ACo_kindOrbit nf (kind i)).qs = false →
    ∃ t ∈ A i, t ^ p = 1 ∧ ∃ a ∈ A i, a * t ≠ t * a
  hcomp : ∀ J : Subgroup G, CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj xhat)) →
    ∃ i : ι, A i = J
  hfactor : ∀ i : ι, CFSG.IsQuasisimple ↥(A i) →
    CFSG.Assembly.IsComponentOf (A i) (ggFixSub (MulAut.conj xhat))

structure ggK1ACo_Family (p : ℕ) (R : Type) [Group R] (x : R) (D : GGKacDatum) where
  ι : Type
  [fin : Finite ι]
  A : ι → Subgroup R
  blk : ι → GGKacOrbit
  hcomm : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b
  htame : ∀ i : ι, CFSG.IsQuasisimple ↥(A i) ∨ Group.IsSolvable ↥(A i)
  hmem : ∀ i : ι, CFSG.IsQuasisimple ↥(A i) → blk i ∈ D.orbits
  hqs : ∀ i : ι, CFSG.IsQuasisimple ↥(A i) → (blk i).qs = true
  hlab : ∀ i : ι, (hq : CFSG.IsQuasisimple ↥(A i)) →
    GGHasLabel (blk i).lab (↥(A i) ⧸ Subgroup.center ↥(A i))
  hreal : ∀ o ∈ D.orbits, o.qs = true → ∃ i : ι, CFSG.IsQuasisimple ↥(A i) ∧ blk i = o
  hbij : ∃ g : {i : ι // CFSG.IsQuasisimple ↥(A i)} ≃
      {k : Fin D.orbits.length // D.orbits[k].qs = true},
    ∀ i, D.orbits[(g i).1] = blk i.1
  hcomp : ∀ J : Subgroup R, CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj x)) →
    ∃ i : ι, CFSG.IsQuasisimple ↥(A i) ∧ J = A i
  hfactor : ∀ i : ι, CFSG.IsQuasisimple ↥(A i) →
    CFSG.Assembly.IsComponentOf (A i) (ggFixSub (MulAut.conj x))

end CFSG.StandardType

end
