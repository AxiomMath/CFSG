module

public import Mathlib
public import CFSG.Milestones.ASVolI.F4
public import CFSG.Open.StatedDefs
public import CFSG.Open.MatrixModelCore
public import CFSG.Quasithin.Recognition.UniquenessSystemDefs
public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.SimsF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

abbrev GL6 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)

abbrev V6 : Type := Fin 6 → ZMod 3

abbrev Sub6 : Type := Submodule (ZMod 3) V6

@[expose] def qV (v : V6) : ZMod 3 := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 - v 5 ^ 2

@[expose] def bil (u v : V6) : ZMod 3 := qV (u + v) - qV u - qV v

@[expose] def xvec (i : Fin 6) : V6 := Pi.single i 1

@[expose] def x1 : V6 := xvec 0
@[expose] def x2 : V6 := xvec 1
@[expose] def x3 : V6 := xvec 2
@[expose] def x4 : V6 := xvec 3
@[expose] def x5 : V6 := xvec 4
@[expose] def x6 : V6 := xvec 5

@[expose] def Iset : Finset (Fin 6) := {0, 1, 2, 3, 4}

@[expose] def commSp (g : GL6) : Sub6 :=
  LinearMap.range (Matrix.mulVecLin ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1))

@[expose] def fixSp (g : GL6) : Sub6 :=
  LinearMap.ker (Matrix.mulVecLin ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) - 1))

@[expose] def IsNondegSub (W : Sub6) : Prop :=
  ∀ w ∈ W, (∀ w' ∈ W, bil w w' = 0) → w = 0

@[expose] def SignPlus (W : Sub6) : Prop :=
  IsNondegSub W ∧ Even (Module.finrank (ZMod 3) W) ∧
    ∃ U : Sub6, U ≤ W ∧ (∀ u ∈ U, qV u = 0) ∧ 2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) W

@[expose] def SignMinus (W : Sub6) : Prop :=
  IsNondegSub W ∧ Even (Module.finrank (ZMod 3) W) ∧
    ¬ ∃ U : Sub6, U ≤ W ∧ (∀ u ∈ U, qV u = 0) ∧ 2 * Module.finrank (ZMod 3) U = Module.finrank (ZMod 3) W

@[expose] def OVq : Subgroup GL6 := CFSG.MatrixModel.isometryCore qV

@[expose] def MDot : Subgroup GL6 := StatedOmega qV

@[expose] def eJd (J : Finset (Fin 6)) : Fin 6 → ZMod 3 := fun i => if i ∈ J then -1 else 1

theorem eJ_mat_sq (J : Finset (Fin 6)) :
    Matrix.diagonal (eJd J) * Matrix.diagonal (eJd J) = (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  unfold eJd
  split_ifs <;> decide

@[expose] def eJ (J : Finset (Fin 6)) : GL6 :=
  ⟨Matrix.diagonal (eJd J), Matrix.diagonal (eJd J), eJ_mat_sq J, eJ_mat_sq J⟩

@[expose] def fMat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![0, 1, 0, 0, 0, 0; 1, 0, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1]

theorem fMat_sq : fMat * fMat = 1 := by
  decide

@[expose] def fDot : GL6 := ⟨fMat, fMat, fMat_sq, fMat_sq⟩

@[expose] noncomputable def zDot : GL6 := eJ {0, 1, 2, 3}

@[expose] noncomputable def tDot : GL6 := eJ {0, 1}

@[expose] def spn (s : Set V6) : Sub6 := Submodule.span (ZMod 3) s

@[expose] def V2minus : Sub6 := spn {x1 - x2, x6}

@[expose] def V4minus : Sub6 := spn {x1 + x2, x3, x4, x5}

@[expose] def V4plus : Sub6 := spn {x1, x2, x3, x4}

@[expose] def V3plus : Sub6 := spn {x1, x2, x6}

@[expose] def Lambda : Set Sub6 := {S | ∃ i : Fin 6, S = spn {xvec i}}

@[expose] def M0Dot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 (spn {x6})

@[expose] def GDot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 x6

@[expose] def DDot : Subgroup GL6 := GDot ⊓ Subgroup.centralizer ({fDot} : Set GL6)

@[expose] def CGDot12 : Subgroup GL6 := GDot ⊓ MulAction.stabilizer GL6 (x1 - x2)

@[expose] noncomputable def M1Dot : Subgroup GL6 := MDot ⊓ Subgroup.centralizer ({zDot} : Set GL6)

@[expose] def M2Dot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 Lambda

@[expose] noncomputable def Q2Dot : Subgroup GL6 :=
  Subgroup.closure {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J}

@[expose] noncomputable def Q1Dot : Subgroup GL6 := pCoreOf 2 M1Dot

@[expose] def SDot : Subgroup GL6 := pCoreOf 2 (M2Dot ⊓ MulAction.stabilizer GL6 (spn {x5}))

@[expose] def TDot : Subgroup GL6 := SDot ⊔ Subgroup.zpowers fDot

@[expose] def EDot (Mi : Subgroup GL6) : Subgroup GL6 := Mi ⊓ Subgroup.centralizer ({fDot} : Set GL6)

@[expose] def ADot (Mi : Subgroup GL6) : Subgroup GL6 := pCoreOf 2 (EDot Mi)

@[expose] def IsEn (n : ℕ) (H : Type) [Group H] : Prop :=
  (∀ a b : H, a * b = b * a) ∧ (∀ a : H, a * a = 1) ∧ Nat.card H = 2 ^ n

@[expose] def Q8SqK : Subgroup (QuaternionGroup 2 × QuaternionGroup 2) :=
  Subgroup.zpowers (QuaternionGroup.a 2, QuaternionGroup.a 2)

theorem Q8SqK_le_center : Q8SqK ≤ Subgroup.center (QuaternionGroup 2 × QuaternionGroup 2) := by
  rw [Q8SqK, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  rintro ⟨g1, g2⟩
  have h : ∀ g : QuaternionGroup 2, g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g := by decide
  exact Prod.ext (h g1) (h g2)

instance Q8SqK.normal : Q8SqK.Normal := Subgroup.normal_of_le_center Q8SqK_le_center

abbrev Q8Sq : Type := (QuaternionGroup 2 × QuaternionGroup 2) ⧸ Q8SqK

@[expose] def IsAutU42 (H : Type) [Group H] : Prop :=
  ∃ (G : Type) (_ : Group G), IsGenLie G GLKind.U4 2 1 ∧ Nonempty (H ≃* MulAut G)

@[expose] def qV5 (v : Fin 5 → ZMod 3) : ZMod 3 := ∑ i, v i ^ 2

@[expose] def qV4m (c : Fin 4 → ZMod 3) : ZMod 3 := -(c 0 ^ 2) + c 1 ^ 2 + c 2 ^ 2 + c 3 ^ 2

@[expose] def bvec : Fin 4 → V6 := ![x1 + x2, x3, x4, x5]

@[expose] def bidx : Fin 4 → Fin 6 := ![0, 2, 3, 4]

@[expose] def blk4 (g : GL6) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)).mulVec (bvec j)) (bidx i)

theorem qV_smul_of_mem_isometryCore {g : GL6} (hg : g ∈ CFSG.MatrixModel.isometryCore qV) :
    ∀ v : V6, qV (g • v) = qV v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => intro v; exact hx v
  | one => intro v; simp
  | mul x y _ _ hx hy => intro v; rw [mul_smul, hx, hy]
  | inv x _ hx =>
    intro v
    have := hx (x⁻¹ • v)
    rw [smul_inv_smul] at this
    exact this.symm

theorem commutator_le_self' (H : Subgroup GL6) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem MDot_le_OVq : MDot ≤ OVq := commutator_le_self' _

theorem qV_smul_of_mem_MDot {g : GL6} (hg : g ∈ MDot) (v : V6) : qV (g • v) = qV v :=
  qV_smul_of_mem_isometryCore (MDot_le_OVq hg) v

@[expose] def PtsMinusSet : Set Sub6 := {S | ∃ v : V6, qV v = -1 ∧ S = spn {v}}

@[expose] def PtsMinus : SubMulAction ↥MDot Sub6 where
  carrier := PtsMinusSet
  smul_mem' := by
    rintro g S ⟨v, hv, rfl⟩
    refine ⟨(g : GL6) • v, ?_, ?_⟩
    · rw [qV_smul_of_mem_MDot g.2, hv]
    · change ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) • Submodule.span (ZMod 3) {v} =
        Submodule.span (ZMod 3) {((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) • v}
      rw [Submodule.smul_span, Set.smul_set_singleton]

abbrev PtX : Type := ↥PtsMinus

theorem qV_x6 : qV x6 = -1 := by
  decide

@[expose] def xDot : PtX := ⟨spn {x6}, x6, qV_x6, rfl⟩

theorem qV_x1_sub_x2 : qV (x1 - x2) = -1 := by
  decide

@[expose] def yDot : PtX := ⟨spn {x1 - x2}, x1 - x2, qV_x1_sub_x2, rfl⟩

@[expose] def DeltaDot : SimpleGraph PtX :=
  SimpleGraph.fromRel fun S S' => ∀ v ∈ S.1, ∀ w ∈ S'.1, bil v w = 0

@[expose] def DeltaDotH : Set PtX := {S | S.1 ≤ V3plus}

@[expose] def DeltaDotSub : DeltaDot.Subgraph := (⊤ : DeltaDot.Subgraph).induce DeltaDotH

@[expose] def HDot : Subgroup ↥MDot := (MDot ⊓ MulAction.stabilizer GL6 V3plus).subgroupOf MDot

@[expose] def F51 : Prop :=
  (IsL43 ↥MDot ∧
    ∀ J : Finset (Fin 6), J ⊆ Iset → Even J.card →
      eJ J ∈ OVq ∧ eJ J * eJ J = 1 ∧ commSp (eJ J) = spn {w | ∃ j ∈ J, w = xvec j} ∧
      fixSp (eJ J) = spn ({x6} ∪ {w | ∃ i ∈ Iset \ J, w = xvec i}) ∧
      ∀ g ∈ OVq, g * g = 1 → commSp g = spn {w | ∃ j ∈ J, w = xvec j} → g = eJ J) ∧
  (M0Dot = GDot ⊔ Subgroup.zpowers fDot ∧
    Nonempty (↥GDot ≃* ↥(StatedOmega qV5)) ∧ IsGenLie ↥GDot GLKind.U4 2 1 ∧
    (fDot ∈ MDot ∧ fDot * fDot = 1 ∧ fDot • x3 = x3 ∧ fDot • x4 = x4 ∧ fDot • x5 = x5 ∧
      fDot • x6 = -x6 ∧ fDot • x1 = x2) ∧
    ∀ g ∈ MDot, g * g = 1 → g • x3 = x3 → g • x4 = x4 → g • x5 = x5 → g • x6 = -x6 →
      g • x1 = x2 → g = fDot) ∧
  (Nonempty (↥M0Dot ≃* StatedProj (CFSG.MatrixModel.isometryCore qV5)) ∧ IsAutU42 ↥M0Dot) ∧
  (commSp fDot = V2minus ∧ Module.finrank (ZMod 3) V2minus = 2 ∧ SignMinus V2minus ∧
    fixSp fDot = V4minus ∧ Module.finrank (ZMod 3) V4minus = 4 ∧ SignMinus V4minus) ∧
  (DDot = CGDot12 ⊔ Subgroup.zpowers zDot ∧
    (∀ g ∈ CGDot12, ∀ h ∈ CGDot12, blk4 g = blk4 h → g = h) ∧
    (∀ B : Matrix (Fin 4) (Fin 4) (ZMod 3), (∃ g ∈ CGDot12, blk4 g = B) ↔
      ∃ u ∈ StatedOmega qV4m, (u : Matrix (Fin 4) (Fin 4) (ZMod 3)) = B) ∧
    (zDot ∈ GDot ∧ zDot * zDot = 1 ∧ commSp zDot = V4plus ∧ Module.finrank (ZMod 3) V4plus = 4 ∧
      SignPlus V4plus) ∧
    (∃ v ∈ V4minus, qV v ≠ 0 ∧ ∀ w ∈ V4minus, -(zDot • w) = w - (bil w v * (qV v)⁻¹) • v) ∧
    Nonempty (↥DDot ≃* Equiv.Perm (Fin 6)))

@[expose] def F52 : Prop :=
  M1Dot = MDot ⊓ MulAction.stabilizer GL6 V4plus ∧
  (((Q2Dot : Set GL6) = {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J}) ∧
    IsEn 4 ↥Q2Dot ∧ Q2Dot ≤ M2Dot ∧ (Q2Dot.subgroupOf M2Dot).Normal ∧
    (∃ K : Subgroup GL6, K ≤ M2Dot ∧ K ⊓ Q2Dot = ⊥ ∧ Q2Dot ⊔ K = M2Dot ∧
      Nonempty (↥K ≃* Equiv.Perm (Fin 5))) ∧
    (Nonempty (↥Q1Dot ≃* Q8Sq) ∧
      ∃ K : Subgroup GL6, K ≤ M1Dot ∧ K ⊓ Q1Dot = ⊥ ∧ Q1Dot ⊔ K = M1Dot ∧
        Nonempty (↥K ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) ∧
  (IsAutU42 ↥M0Dot ∧ M1Dot ≤ M0Dot ∧ M2Dot ≤ M0Dot ∧ M1Dot ≠ M2Dot ∧
    TDot = SDot ⊔ Subgroup.zpowers fDot ∧
    IsSylowOf 2 TDot (M1Dot ⊓ M2Dot) ∧ IsSylowOf 2 TDot MDot ∧
    ∀ Q : Subgroup GL6,
      (TDot ≤ Q ∧ Q ≤ M0Dot ∧ Q ≠ M0Dot ∧ ∀ R' : Subgroup GL6, Q < R' → R' ≤ M0Dot → R' = M0Dot) ↔
        (Q = M1Dot ∨ Q = M2Dot))

@[expose] def F53Model : Prop :=
  (∀ Mi : Subgroup GL6, (Mi = M1Dot ∨ Mi = M2Dot) →
      Nonempty (↥(EDot Mi) ≃* Multiplicative (ZMod 2 × ZMod 2) × Equiv.Perm (Fin 4)) ∧
        IsEn 4 ↥(ADot Mi)) ∧
    (ADot M1Dot = Subgroup.zpowers fDot ⊔ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ∧
      Subgroup.zpowers fDot ⊓ (Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥ ∧
      ADot M2Dot = Subgroup.zpowers fDot ⊔ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) ∧
      Subgroup.zpowers fDot ⊓ (Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6)) = ⊥) ∧
    (((Q2Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) : Subgroup GL6) : Set GL6) =
      {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ ((0 : Fin 6) ∈ J ↔ (1 : Fin 6) ∈ J) ∧
        g = eJ J}) ∧
    ({u : GL6 | u ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ∧ u ≠ 1} =
      {zDot} ∪ {u : GL6 | u ∈ Q1Dot ⊓ Subgroup.centralizer ({fDot} : Set GL6) ∧ u ≠ 1 ∧ u * u = 1 ∧
        commSp u ≤ V4plus ∧ Module.finrank (ZMod 3) (commSp u) = 2 ∧ SignMinus (commSp u)}) ∧
    ((∀ w : GL6, w ∈ MDot → w ≠ 1 → w * w = 1 →
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 4 ∧ SignPlus (commSp w))) ∧
        ((∃ g ∈ MDot, g * fDot * g⁻¹ = w) ↔
          (Module.finrank (ZMod 3) (commSp w) = 2 ∧ SignMinus (commSp w))) ∧
        ((∃ g ∈ MDot, g * zDot * g⁻¹ = w) ∨ (∃ g ∈ MDot, g * fDot * g⁻¹ = w))) ∧
      ¬ ∃ g ∈ MDot, g * zDot * g⁻¹ = fDot) ∧
    (⁅Q2Dot, Subgroup.zpowers fDot⁆ = Subgroup.zpowers tDot ∧ tDot ≠ 1)

end

end CFSG.Quasithin.SimsF5
