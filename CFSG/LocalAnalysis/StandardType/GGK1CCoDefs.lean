module

public import CFSG.LocalAnalysis.StandardType.GGK1CDefs
public import CFSG.LocalAnalysis.StandardType.GGK1Defs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

inductive ggK1CCo_Kind where
  | sp (s : ℕ)
  | sl (m : ℕ)
  | su (m : ℕ)
  deriving DecidableEq

@[expose] def ggK1CCo_Kind.hasOrbit : ggK1CCo_Kind → Bool
  | .sl 1 => false
  | .su 1 => false
  | _ => true

@[expose] def ggK1CCo_kindOrbit (nf : ℕ) : ggK1CCo_Kind → GGKacOrbit
  | .sp s =>
      if s = 1 then ⟨⟨.A, 1, nf⟩, decide (nf ≠ 1)⟩
      else if s = 2 ∧ nf = 1 then ⟨⟨.B2der, 0, 1⟩, true⟩
      else ⟨⟨.C, s, nf⟩, true⟩
  | .sl 1 => ⟨⟨.A, 0, nf⟩, false⟩
  | .sl m => ggMultBlockA (m - 1) nf 1
  | .su 1 => ⟨⟨.A, 0, nf⟩, false⟩
  | .su m => ggMultBlockA (m - 1) nf 2

@[expose] def ggK1CCo_expectedKindList (p nf d : ℕ) (m : List ℕ) : List ggK1CCo_Kind :=
  (if m.headD 0 = 0 then [] else [ggK1CCo_Kind.sp (m.headD 0)]) ++
    (((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 1 ≤ m.getD j 0))).map
        (fun j => if d = 1 then ggK1CCo_Kind.sl (m.getD j 0)
          else ggK1CCo_Kind.su (m.getD j 0)))

@[expose] def ggK1CCo_expectedKinds (p nf d : ℕ) (m : List ℕ) : Multiset ggK1CCo_Kind :=
  ↑(ggK1CCo_expectedKindList p nf d m)

@[expose] def ggK1CCo_orbitKindList (p nf d : ℕ) (m : List ℕ) : List ggK1CCo_Kind :=
  (ggK1CCo_expectedKindList p nf d m).filter (fun k => ggK1CCo_Kind.hasOrbit k)

@[expose] def ggK1CCo_Kind.Model {K : Type} [Field K] {r : ℕ} (nf : ℕ) (kind : ggK1CCo_Kind)
    (H : Subgroup (StatedSp r K)) : Prop :=
  match kind with
  | .sp s =>
      if s = 1 then Nonempty (↥H ≃* StatedSp 1 K)
      else if s = 2 ∧ nf = 1 then Nonempty (↥H ≃* ↥(commutator (StatedSp 2 K)))
      else Nonempty (↥H ≃* StatedSp s K)
  | .sl m => Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin m) K)
  | .su m => ∃ (E : Type) (_ : Field E) (_ : Fintype E),
      Fintype.card E = (Nat.card K) ^ 2 ∧
        Nonempty (↥H ≃* ↥(StatedSU m (Nat.card K) E))

structure ggK1CCo_Blocks (p nf d r : ℕ) (K : Type) [Field K]
    (x : ↥(StatedSp r K)) (m : List ℕ) where
  ι : Type
  [fintype : Fintype ι]
  A : ι → Subgroup (StatedSp r K)
  kind : ι → ggK1CCo_Kind
  hcomm : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b
  hjoin : ⨆ i : ι, A i = Subgroup.centralizer ({x} : Set (StatedSp r K))
  hindep : iSupIndep A
  htame : ∀ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i)
  kind_multiset : (Finset.univ : Finset ι).val.map kind = ggK1CCo_expectedKinds p nf d m
  hqsKind : ∀ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ↔
    (ggK1CCo_kindOrbit nf (kind i)).qs = true
  hmodel : ∀ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ →
    ggK1CCo_Kind.Model nf (kind i) ⁅A i, A i⁆
  hsolv : ∀ i : ι, (kind i).hasOrbit = true → (ggK1CCo_kindOrbit nf (kind i)).qs = false →
    ∃ t ∈ A i, t ^ p = 1 ∧ ∃ a ∈ A i, a * t ≠ t * a

structure ggK1CCo_Family (p nf d r : ℕ) (K : Type) [Field K]
    (x : ↥(StatedSp r K)) (m : List ℕ) where
  ι : Type
  [fin : Finite ι]
  A : ι → Subgroup (StatedSp r K)
  blk : ι → GGKacOrbit
  hcomm : ∀ i j : ι, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b
  hjoin : ⨆ i : ι, A i = Subgroup.centralizer ({x} : Set (StatedSp r K))
  hindep : iSupIndep A
  htame : ∀ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∨ Group.IsSolvable ↥(A i)
  hmem : ∀ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ →
    blk i ∈ (ggMultDatumC p nf d m).orbits
  hqs : ∀ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ → (blk i).qs = true
  hlab : ∀ i : ι, (hq : CFSG.IsQuasisimple ↥⁅A i, A i⁆) →
    GGHasLabel (blk i).lab
      ((⁅A i, A i⁆).map (proj r K) ⧸ Subgroup.center ((⁅A i, A i⁆).map (proj r K)))
  hreal : ∀ o ∈ (ggMultDatumC p nf d m).orbits, o.qs = true →
    ∃ i : ι, CFSG.IsQuasisimple ↥⁅A i, A i⁆ ∧ blk i = o
  hbij : ∃ g : {i : ι // CFSG.IsQuasisimple ↥⁅A i, A i⁆} ≃
      {k : Fin (ggMultDatumC p nf d m).orbits.length //
        (ggMultDatumC p nf d m).orbits[k].qs = true},
    ∀ i, (ggMultDatumC p nf d m).orbits[(g i).1] = blk i.1
  hsolv : ∀ o ∈ (ggMultDatumC p nf d m).orbits, o.qs = false →
    ∃ i : ι, blk i = o ∧ ∃ t ∈ A i, t ^ p = 1 ∧ ∃ a ∈ A i, a * t ≠ t * a

end CFSG.StandardType

end
