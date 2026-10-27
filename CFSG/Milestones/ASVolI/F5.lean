module

public import Mathlib
public import CFSG.Milestones.ASVolI.F4
public import CFSG.Open.StatedDefs
public import CFSG.Open.MatrixModelCore
public import CFSG.Quasithin.Recognition.UniquenessSystemDefs
public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation
public import CFSG.Quasithin.Background.SimsF5Main
public import CFSG.Quasithin.Background.SimsF5Asm7

public section

namespace CFSG.ASVolI.ChF5

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

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5

@[expose] def F_5_1 : Prop :=
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

theorem as_F_5_1 : F_5_1 :=
  CFSG.Quasithin.SimsF5.f51

@[expose] def F_5_2 : Prop :=
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

section F52

theorem as_F_5_2 : F_5_2 :=
  CFSG.Quasithin.SimsF5.f52

end F52

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section Abstract

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] def fOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) : M := bM β ε fb

@[expose] def TOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (Tb : Subgroup E) : Subgroup M := imB β ε Tb

@[expose] def M0Of (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M := MiOne β ε ⊔ MiTwo β ε

@[expose] def EOf (Mi : Subgroup M) (f : M) : Subgroup M := Mi ⊓ Subgroup.centralizer ({f} : Set M)

@[expose] def AOf (Mi : Subgroup M) (f : M) : Subgroup M := pCoreOf 2 (EOf Mi f)

@[expose] def QTwoOf (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) : Subgroup M :=
  pCoreOf 2 (oPPrime 2 (GiTwo Gp β ε))

@[expose] def IsTInv (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) (t : M) :
    Prop :=
  t ≠ 1 ∧ ⁅QTwoOf Gp β ε, Subgroup.zpowers (fOf β ε fb)⁆ = Subgroup.zpowers t

@[expose] def DOne (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) :
    Subgroup M :=
  (((cenIn (Gp ⊓ M₁) (fb : E)).subgroupOf M₁).map (f1 (c := β))).map (epsG β ε)

@[expose] def DTwo (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) :
    Subgroup M :=
  (((cenIn (Gp ⊓ M₂) (fb : E)).subgroupOf M₂).map (f2 (c := β))).map (epsG β ε)

end Abstract

@[expose] def IsTransvection {A : Type} [Group A] (τ : MulAut A) : Prop :=
  τ ≠ 1 ∧ Nat.card ↥(Subgroup.closure {x : A | ∃ a : A, x = τ a * a⁻¹}) = 2

@[expose] def U42Hermitian (K : Type) [Field K] (vectors other : Fin 4 → K) : K :=
  ∑ coordinate : Fin 4, vectors coordinate ^ 2 * other coordinate

@[expose] def U42ParabolicAt {E K : Type} [Group E] [Field K] (Gp parabolic : Subgroup E)
    (marking : ↥Gp ≃* StatedProj (StatedSU 4 2 K))
    (space : Submodule K (Fin 4 → K)) : Prop :=
  parabolic ≤ Gp ∧ ∀ element : ↥Gp, (element : E) ∈ parabolic ↔
    ∃ matrix : ↥(StatedSU 4 2 K),
      marking element = (QuotientGroup.mk matrix : StatedProj (StatedSU 4 2 K)) ∧
      ∀ vector : Fin 4 → K,
        ((matrix : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec
          vector ∈ space ↔ vector ∈ space

@[expose] def U42MarkedGraphAmalgam {E : Type} [Group E]
    (Gp M₁ M₂ : Subgroup E) (actor : E) : Prop :=
  actor ∉ Gp ∧ actor * actor = 1 ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      ∃ (frobenius : K →+* K) (changeBasis : Matrix.GeneralLinearGroup (Fin 4) K),
        (∀ scalar : K, frobenius scalar = scalar ^ 2) ∧
        ((Matrix.transpose ((changeBasis : Matrix (Fin 4) (Fin 4) K).map frobenius)) *
          (changeBasis : Matrix (Fin 4) (Fin 4) K)) =
            Matrix.of (fun row column : Fin 4 =>
              if (row.val, column.val) = (0, 2) ∨ (row.val, column.val) = (1, 3) ∨
                (row.val, column.val) = (2, 0) ∨ (row.val, column.val) = (3, 1) then 1 else 0) ∧
        ∃ (marking : ↥Gp ≃* StatedProj (StatedSU 4 2 K))
            (point plane : Submodule K (Fin 4 → K)),
          Module.finrank K point = 1 ∧ Module.finrank K plane = 2 ∧ point ≤ plane ∧
          (∀ vector ∈ plane, ∀ other ∈ plane, U42Hermitian K vector other = 0) ∧
          U42ParabolicAt Gp (Gp ⊓ M₁) marking point ∧
          U42ParabolicAt Gp (Gp ⊓ M₂) marking plane ∧
          ∀ element : ↥Gp, ∃ conjugate : ↥Gp,
            (conjugate : E) = actor * (element : E) * actor⁻¹ ∧
            ∀ matrix : ↥(StatedSU 4 2 K),
              marking element = (QuotientGroup.mk matrix : StatedProj (StatedSU 4 2 K)) →
                ∃ image : ↥(StatedSU 4 2 K),
                  marking conjugate = (QuotientGroup.mk image : StatedProj (StatedSU 4 2 K)) ∧
                  (image : Matrix.GeneralLinearGroup (Fin 4) K) =
                    changeBasis * (Matrix.GeneralLinearGroup.map frobenius changeBasis)⁻¹ *
                      Matrix.GeneralLinearGroup.map frobenius
                        (matrix : Matrix.GeneralLinearGroup (Fin 4) K) *
                          Matrix.GeneralLinearGroup.map frobenius changeBasis * changeBasis⁻¹

structure F5Amalgam {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) (actor : E) : Prop where
  finite : Finite E
  normal : Gp.Normal
  centralizer_trivial : Subgroup.centralizer (Gp : Set E) = ⊥
  gen : M₁ ⊔ M₂ = ⊤
  native : U42MarkedGraphAmalgam Gp M₁ M₂ actor
  split : ∀ element : E, ∃ inside ∈ Gp, ∃ localElement ∈ M₁ ⊓ M₂,
    element = inside * localElement
  dynkin : ∀ element : E,
    element ∈ Subgroup.normalizer ((Gp ⊓ (M₁ ⊓ M₂) : Subgroup E) : Set E) →
      element ∈ Subgroup.normalizer ((Gp ⊓ M₁ : Subgroup E) : Set E)

structure F5Completion {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (z : M) (actor : E) : Prop where
  amalgam : F5Amalgam Gp M₁ M₂ actor
  faithful : β.IsFaithful
  finite_M : Finite M
  inj : Function.Injective (epsG β ε)
  z_inv : z ≠ 1 ∧ z * z = 1
  z_mem : z ∈ ctr (oPPrime 2 (GiOne Gp β ε))
  ha : Subgroup.normalizer ((ctr (pCoreOf 2 (GiOne Gp β ε)) : Subgroup M) : Set M) =
      MiOne β ε ∧
    Subgroup.normalizer ((ctr (pCoreOf 2 (GiTwo Gp β ε)) : Subgroup M) : Set M) = MiTwo β ε
  hb : Subgroup.centralizer ({z} : Set M) ≤ MiOne β ε
  he : oTwoRes (⊤ : Subgroup M) = ⊤

structure HypF5 {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (z : M)
    (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) : Prop where
  f431 : F5Completion Gp M₁ M₂ β ε z (fb : E)
  Tb_syl : IsSylowOf 2 Tb (M₁ ⊓ M₂)
  fb_mem : (fb : E) ∈ Tb
  fb_syl : IsSylowOf 2
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ Subgroup.centralizer ({(fb : E)} : Set E))
      (cenIn Gp (fb : E))
  not_i : ¬ IsSylowOf 2 (imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M))
    (Subgroup.centralizer ({bM β ε fb} : Set M))

@[expose] def IsRSylow {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) {M : Type} [Group M] (ε : Y →* M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂))
    (R : Subgroup M) : Prop :=
  IsSylowOf 2 R (Subgroup.centralizer ({bM β ε fb} : Set M)) ∧
    imB β ε Tb ⊓ Subgroup.centralizer ({bM β ε fb} : Set M) ≤ R

structure IsMuIso {E : Type} [Group E] {M₁ M₂ : Subgroup E} (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁)
    (fb : ↥(M₁ ⊓ M₂)) : Prop where
  faithful : μ.IsFaithful
  img1 : μ.φ1.range.map M0Dot.subtype = M1Dot
  img2 : μ.φ2.range.map M0Dot.subtype = M2Dot
  img12 : μ.φ12.range.map M0Dot.subtype = M1Dot ⊓ M2Dot
  z_eq : ((μ.φ1 zb : ↥M0Dot) : GL6) = zDot
  f_eq : ((μ.φ12 fb : ↥M0Dot) : GL6) = fDot

@[expose] def IsMarkedMuIso {E : Type} [Group E] {M₁ M₂ : Subgroup E}
    (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁) (fb : ↥(M₁ ⊓ M₂)) (Tb : Subgroup E) : Prop :=
  IsMuIso μ zb fb ∧
    ((Tb.subgroupOf (M₁ ⊓ M₂)).map μ.φ12).map M0Dot.subtype = TDot

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def F_5_3 : Prop :=
  ((∀ Mi : Subgroup GL6, (Mi = M1Dot ∨ Mi = M2Dot) →
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
    (⁅Q2Dot, Subgroup.zpowers fDot⁆ = Subgroup.zpowers tDot ∧ tDot ≠ 1)) ∧
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)),
    HypF5 Gp M₁ M₂ β ε z Tb fb →
    (∃ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z ∧ IsMarkedMuIso μ zb fb Tb) ∧
    (∀ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁), ε (β.φ1 zb) = z → IsMarkedMuIso μ zb fb Tb →
      ∀ a : ↥(M₁ ⊓ M₂),
        (((∃ g ∈ MDot, g * zDot * g⁻¹ = ((μ.φ12 a : ↥M0Dot) : GL6)) ∧
            ((μ.φ12 a : ↥M0Dot) : GL6) ∈ TDot) ↔
          (IsConj z (bM β ε a) ∧ bM β ε a ∈ TOf β ε Tb)) ∧
        (((∃ g ∈ MDot, g * fDot * g⁻¹ = ((μ.φ12 a : ↥M0Dot) : GL6)) ∧
            ((μ.φ12 a : ↥M0Dot) : GL6) ∈ TDot) ↔
          (IsConj (fOf β ε fb) (bM β ε a) ∧ bM β ε a ∈ TOf β ε Tb))) ∧
    (∀ t : M, IsTInv Gp β ε fb t → IsConj z (fOf β ε fb * t * z)) ∧
    (({x : M | IsConj z x} ∩ (AOf (MiOne β ε) (fOf β ε fb) : Set M)).ncard = 5 ∧
      ({x : M | IsConj z x} ∩ (QTwoOf Gp β ε : Set M)).ncard = 5 ∧
      ({x : M | IsConj z x} ∩ (AOf (MiTwo β ε) (fOf β ε fb) : Set M)).ncard = 9)

section F53

theorem as_F_5_3 : F_5_3 := by
  have h := CFSG.Quasithin.SimsF5.f53
  refine ⟨h.1, ?_⟩
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb hyp
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18,
    h19⟩ := hyp
  obtain ⟨⟨μ, zb, hz, ⟨⟨m1, m2, m3, m4, m5, m6⟩, m7⟩⟩, h5', h7', h8'⟩ :=
    h.2 E Gp M₁ M₂ Y β M ε z Tb fb
      ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩
  refine ⟨⟨μ, zb, hz, ⟨⟨m1, m2, m3, m4, m5, m6⟩, m7⟩⟩, ?_, h7', h8'⟩
  intro μ' zb' hz' hμ'
  obtain ⟨⟨n1, n2, n3, n4, n5, n6⟩, n7⟩ := hμ'
  exact h5' μ' zb' hz' ⟨⟨n1, n2, n3, n4, n5, n6⟩, n7⟩

end F53

@[expose] def F_5_4 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M),
    HypF5 Gp M₁ M₂ β ε z Tb fb → IsRSylow β ε Tb fb R →
    ∀ t : M, IsTInv Gp β ε fb t →
      (AOf (MiOne β ε) (fOf β ε fb) =
          Subgroup.centralizer ((AOf (MiOne β ε) (fOf β ε fb) : Subgroup M) : Set M) ∧
        AOf (MiTwo β ε) (fOf β ε fb) =
          Subgroup.centralizer ((AOf (MiTwo β ε) (fOf β ε fb) : Subgroup M) : Set M)) ∧
      (Nonempty (↥R ≃* ↥(TOf β ε Tb ⊓ Subgroup.centralizer ({t} : Set M))) ∧
        Nonempty (↥(TOf β ε Tb ⊓ Subgroup.centralizer ({t} : Set M)) ≃*
          DihedralGroup 4 × DihedralGroup 4)) ∧
      (∀ Mi : Subgroup M, (Mi = MiOne β ε ∨ Mi = MiTwo β ε) →
        R ≤ Subgroup.normalizer (EOf Mi (fOf β ε fb) : Set M) ∧
        Nonempty (↥(EOf Mi (fOf β ε fb) ⊔ R) ≃* DihedralGroup 4 × Equiv.Perm (Fin 4))) ∧
      ((∀ y : M, y ∈ TOf β ε Tb → y ∉ Subgroup.centralizer ({t} : Set M) →
          {A : Subgroup M | IsMaxElemAbelian (TOf β ε Tb) A} =
            {AOf (MiOne β ε) (fOf β ε fb), AOf (MiTwo β ε) (fOf β ε fb),
              cj y⁻¹ (AOf (MiTwo β ε) (fOf β ε fb)), QTwoOf Gp β ε}) ∧
        Nonempty (↥(Subgroup.normalizer (QTwoOf Gp β ε : Set M)) ⧸
          (QTwoOf Gp β ε).subgroupOf (Subgroup.normalizer (QTwoOf Gp β ε : Set M)) ≃*
            Equiv.Perm (Fin 5)) ∧
        Nonempty (↥(Subgroup.normalizer (AOf (MiOne β ε) (fOf β ε fb) : Set M)) ⧸
          (AOf (MiOne β ε) (fOf β ε fb)).subgroupOf
            (Subgroup.normalizer (AOf (MiOne β ε) (fOf β ε fb) : Set M)) ≃* Equiv.Perm (Fin 5)) ∧
        Nonempty (↥(Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M)) ⧸
          (AOf (MiTwo β ε) (fOf β ε fb)).subgroupOf
            (Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M)) ≃*
              Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      (∀ Mi : Subgroup M, (Mi = MiOne β ε ∨ Mi = MiTwo β ε) →
        ∃ τ ∈ autOn (⊤ : Subgroup M) (AOf Mi (fOf β ε fb)), IsTransvection τ)

section F54

theorem as_F_5_4 : F_5_4 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb R hyp hR
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18,
    h19⟩ := hyp
  exact CFSG.Quasithin.SimsF5.f54 E Gp M₁ M₂ Y β M ε z Tb fb R
    ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩ hR

end F54

@[expose] def F_5_5 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M),
    HypF5 Gp M₁ M₂ β ε z Tb fb → IsRSylow β ε Tb fb R →
    (Nonempty (↥(DOne Gp β ε fb) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (↥(DTwo Gp β ε fb) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) ∧
    Nonempty (↥(DOne Gp β ε fb ⊔ DTwo Gp β ε fb) ≃* Equiv.Perm (Fin 6)) ∧
    Nonempty (↥(R ⊓ Subgroup.centralizer
      ((oTwoRes (DOne Gp β ε fb ⊔ DTwo Gp β ε fb) : Subgroup M) : Set M)) ≃*
        Multiplicative (ZMod 4)) ∧
    ((R : Set M) * ((DOne Gp β ε fb ⊔ DTwo Gp β ε fb : Subgroup M) : Set M) =
      ((Subgroup.centralizer ({fOf β ε fb} : Set M) : Subgroup M) : Set M)) ∧
    (Nonempty (↥(M0Of β ε) ≃* E) ∧ Nonempty (E ≃* ↥M0Dot) ∧ IsAutU42 ↥M0Dot)

section F55

theorem as_F_5_5 : F_5_5 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb R hyp hR
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18,
    h19⟩ := hyp
  exact CFSG.Quasithin.SimsF5.f55 E Gp M₁ M₂ Y β M ε z Tb fb R
    ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩ hR

end F55

@[expose] def F_5_6 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)),
    HypF5 Gp M₁ M₂ β ε z Tb fb →
    M0Of β ε ⊔ Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M) = ⊤

section F56

theorem as_F_5_6 : F_5_6 := by
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb hyp
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18,
    h19⟩ := hyp
  exact CFSG.Quasithin.SimsF5.f56 E Gp M₁ M₂ Y β M ε z Tb fb
    ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩

end F56

end CFSG.ASVolI

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

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

section AbstractGraph

variable {M : Type} [Group M]

@[expose] def DeltaGraph (M0 R Tf : Subgroup M) : SimpleGraph (M ⧸ M0) :=
  SimpleGraph.fromRel fun u v => ∃ a b : M, (a : M ⧸ M0) = u ∧ (b : M ⧸ M0) = v ∧
    ∃ r ∈ R, r ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, a⁻¹ * b = m₁ * r * m₂

end AbstractGraph

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI.ChF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

section AbstractUS

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {M : Type} [Group M]

@[expose] def TfOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) : Subgroup M :=
  TOf β ε Tb ⊓ Subgroup.centralizer ({fOf β ε fb} : Set M)

@[expose] def HOf (β : Cpl M₁ M₂ Y) (ε : Y →* M) (fb : ↥(M₁ ⊓ M₂)) : Subgroup M :=
  Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M)

@[expose] def xOf (M0 : Subgroup M) : M ⧸ M0 := ((1 : M) : M ⧸ M0)

@[expose] def yOf (M0 : Subgroup M) (r : M) : M ⧸ M0 := (r : M ⧸ M0)

@[expose] def DeltaSub (β : Cpl M₁ M₂ Y) (ε : Y →* M) (Tb : Subgroup E)
    (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M) :
    (DeltaGraph (M0Of β ε) R (TfOf β ε Tb fb)).Subgraph :=
  (⊤ : (DeltaGraph (M0Of β ε) R (TfOf β ε Tb fb)).Subgraph).induce
    ((fun h : M => h • xOf (M0Of β ε)) '' (HOf β ε fb : Set M))

end AbstractUS

end

end CFSG.ASVolI.ChF5

namespace CFSG.ASVolI

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.ASVolI.ChF5 CFSG.Quasithin.Asc94
open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

@[expose] def F_5_7 : Prop :=
  (IsNondegSub V3plus ∧ Module.finrank (ZMod 3) V3plus = 3 ∧
    Matrix.det (Matrix.of fun i j : Fin 3 => bil (![x1, x2, x6] i) (![x1, x2, x6] j)) = 1 ∧
    DeltaDotH = {S : PtX | S.1 = spn {x6} ∨ S.1 = spn {x1 - x2} ∨ S.1 = spn {x1 + x2}} ∧
    MDot ⊓ MulAction.stabilizer GL6 V3plus =
      MDot ⊓ Subgroup.normalizer ((ADot M2Dot : Subgroup GL6) : Set GL6)) ∧
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)) (R : Subgroup M),
    HypF5 Gp M₁ M₂ β ε z Tb fb → IsRSylow β ε Tb fb R →
    ∀ r : M, r ∈ R → r ∉ TfOf β ε Tb fb →
      ∃ (μ : Cpl M₁ M₂ ↥M0Dot) (zb : ↥M₁),
        ε (β.φ1 zb) = z ∧ IsMarkedMuIso μ zb fb Tb ∧
      ∃ σ : ↥M0Dot ≃* ↥(M0Of β ε),
        ((∀ a : ↥M₁, ((σ (μ.φ1 a) : ↥(M0Of β ε)) : M) = ε (β.φ1 a)) ∧
          (∀ a : ↥M₂, ((σ (μ.φ2 a) : ↥(M0Of β ε)) : M) = ε (β.φ2 a)) ∧
          (∀ a : ↥(M₁ ⊓ M₂), ((σ (μ.φ12 a) : ↥(M0Of β ε)) : M) = bM β ε a)) ∧
        ∃ ζ : ↥HDot ≃* ↥(HOf β ε fb),
          ((∀ (g : ↥HDot) (g0 : ↥M0Dot), ((g : ↥MDot) : GL6) = (g0 : GL6) →
              ((ζ g : ↥(HOf β ε fb)) : M) = ((σ g0 : ↥(M0Of β ε)) : M)) ∧
            ((MulAction.stabilizer ↥MDot ({xDot, yDot} : Set PtX)).subgroupOf HDot).map
                ζ.toMonoidHom =
              (MulAction.stabilizer M
                ({xOf (M0Of β ε), yOf (M0Of β ε) r} : Set (M ⧸ M0Of β ε))).subgroupOf
                  (HOf β ε fb)) ∧
          ((FaithfulSMul M (M ⧸ M0Of β ε) ∧
            IsUniquenessSystem (DeltaGraph (M0Of β ε) R (TfOf β ε Tb fb))
              (HOf β ε fb) (DeltaSub β ε Tb fb R)
              (xOf (M0Of β ε)) (yOf (M0Of β ε) r)) ∧
            (FaithfulSMul ↥MDot PtX ∧ IsUniquenessSystem DeltaDot HDot DeltaDotSub xDot yDot) ∧
            ∃ β' : ↥(MulAction.stabilizer ↥MDot xDot) ≃* ↥(MulAction.stabilizer M (xOf (M0Of β ε))),
              (∀ (g : ↥(MulAction.stabilizer ↥MDot xDot)) (g0 : ↥M0Dot),
                ((g : ↥MDot) : GL6) = (g0 : GL6) →
                  ((β' g : ↥(MulAction.stabilizer M (xOf (M0Of β ε)))) : M) =
                    ((σ g0 : ↥(M0Of β ε)) : M)) ∧
              IsEquivalence HDot xDot yDot (HOf β ε fb) (xOf (M0Of β ε)) (yOf (M0Of β ε) r) β' ζ)

section F57

theorem as_F_5_7 : F_5_7 := by
  have h := CFSG.Quasithin.SimsF5.f57
  refine ⟨h.1, ?_⟩
  intro E _ Gp M₁ M₂ Y _ β M _ ε z Tb fb R hyp hR r hr hrT
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18,
    h19⟩ := hyp
  obtain ⟨μ, zb, hz, ⟨⟨m1, m2, m3, m4, m5, m6⟩, m7⟩, rest⟩ := h.2 E Gp M₁ M₂ Y β M ε z Tb fb R
    ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12, h13, h14, h15⟩, h16, h17, h18, h19⟩
    hR r hr hrT
  exact ⟨μ, zb, hz, ⟨⟨m1, m2, m3, m4, m5, m6⟩, m7⟩, rest⟩

end F57

@[expose] def F_5_8 : Prop :=
  (DeltaDot.IsClique DeltaDotH ∧ DeltaDotH.ncard = 3) ∧
  (∀ θ : Set PtX, DeltaDot.IsClique θ → θ.ncard = 3 → ∃ g : ↥MDot, g • θ = DeltaDotH) ∧
  (DeltaDot.Connected ∧ Triangulable DeltaDot) ∧
  IsBase ↥MDot DeltaDot DeltaDotSub

namespace ChF5S

open CFSG.ASVolI.ChF5 Matrix
open scoped commutatorElement
open scoped Pointwise

private abbrev T5 := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

private def qT (t : T5) : ZMod 3 :=
  t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2.1 ^ 2 + t.2.2.2.2 ^ 2

private def dT (t s : T5) : ZMod 3 :=
  t.1 * s.1 + t.2.1 * s.2.1 + t.2.2.1 * s.2.2.1 + t.2.2.2.1 * s.2.2.2.1 + t.2.2.2.2 * s.2.2.2.2

private def neg5 (t : T5) : T5 := (-t.1, -t.2.1, -t.2.2.1, -t.2.2.2.1, -t.2.2.2.2)

private def L3 : List (ZMod 3) := [0, 1, 2]

private def all5 : List T5 :=
  L3.flatMap fun a => L3.flatMap fun b => L3.flatMap fun c => L3.flatMap fun d =>
    L3.map fun e => (a, b, c, d, e)

private theorem mem_all5 (t : T5) : t ∈ all5 := by
  obtain ⟨a, b, c, d, e⟩ := t
  revert a b c d e
  decide

set_option maxRecDepth 100000 in
private theorem C1_bool : all5.all (fun y =>
    !(qT y == 0 && y != (0, 0, 0, 0, 0)) ||
      all5.any (fun t => qT t == 2 && dT t y == 0)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem C2_bool : all5.all (fun y =>
    !(qT y == 0 && y != (0, 0, 0, 0, 0)) ||
      ((all5.filter (fun t => qT t == 2 && dT t y == 0)).all (fun a =>
        (all5.filter (fun t => qT t == 2 && dT t y == 0)).all (fun b =>
          !(dT a b != 0 && a != b && a != neg5 b) ||
            (all5.filter (fun t => qT t == 2 && dT t y == 0)).any (fun c =>
              dT c a == 0 && dT c b == 0))))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem C3_bool : all5.all (fun y => all5.all (fun z =>
    !(qT y == 0 && qT z == 0 && dT y z != 0) ||
      all5.any (fun t => qT t == 2 && dT t y == 0 && dT t z == 0))) = true := by
  decide +kernel

private theorem diam5 (y : T5) (hy : qT y = 0) (hne : y ≠ (0, 0, 0, 0, 0)) :
    ∃ t : T5, qT t = 2 ∧ dT t y = 0 := by
  have h := List.all_eq_true.mp C1_bool y (mem_all5 y)
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨t, _, ht⟩
  · exfalso
    simp [hy, hne] at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨t, ht.1, ht.2⟩

private theorem h2_5 (y : T5) (hy : qT y = 0) (hne : y ≠ (0, 0, 0, 0, 0)) (a b : T5)
    (ha : qT a = 2) (hay : dT a y = 0) (hb : qT b = 2) (hby : dT b y = 0)
    (hab : dT a b ≠ 0) (hne' : a ≠ b) (hneg : a ≠ neg5 b) :
    ∃ c : T5, qT c = 2 ∧ dT c y = 0 ∧ dT c a = 0 ∧ dT c b = 0 := by
  have h := List.all_eq_true.mp C2_bool y (mem_all5 y)
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exfalso
    simp [hy, hne] at h
  have hA := List.all_eq_true.mp h a (List.mem_filter.mpr ⟨mem_all5 a, by simp [ha, hay]⟩)
  have hB := List.all_eq_true.mp hA b (List.mem_filter.mpr ⟨mem_all5 b, by simp [hb, hby]⟩)
  rw [Bool.or_eq_true] at hB
  rcases hB with hB | hB
  · exfalso
    simp [hab, hne', hneg] at hB
  · rw [List.any_eq_true] at hB
    obtain ⟨c, hc, hc'⟩ := hB
    rw [List.mem_filter] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc hc'
    exact ⟨c, hc.2.1, hc.2.2, hc'.1, hc'.2⟩

private theorem h3_5 (y z : T5) (hy : qT y = 0) (hz : qT z = 0) (hyz : dT y z ≠ 0) :
    ∃ t : T5, qT t = 2 ∧ dT t y = 0 ∧ dT t z = 0 := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp C3_bool y (mem_all5 y)) z (mem_all5 z)
  rw [Bool.or_eq_true, List.any_eq_true] at h
  rcases h with h | ⟨t, _, ht⟩
  · exfalso
    simp [hy, hz, hyz] at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at ht
    exact ⟨t, ht.1.1, ht.1.2, ht.2⟩

open scoped commutatorElement
open scoped Pointwise

private theorem bil_coord (u v : V6) : bil u v =
    2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4) - 2 * (u 5 * v 5) := by
  simp only [bil, qV, Pi.add_apply, Fin.sum_univ_six]
  ring

private theorem bil_self (a : V6) : bil a a = 2 * qV a := by
  rw [bil_coord]; simp only [qV]; ring

private def wv (z : V6) : V6 := ![2 * z 0, 2 * z 1, 2 * z 2, 2 * z 3, 2 * z 4, 0 - 2 * z 5]

private theorem dot_wv (z x : V6) : wv z ⬝ᵥ x = bil x z := by
  rw [bil_coord]; simp [dotProduct, Fin.sum_univ_six, wv]; ring

private theorem dot_wv_self (z : V6) : wv z ⬝ᵥ z = 2 * qV z := by
  rw [dot_wv, bil_self]

private def reflM (z : V6) : Matrix (Fin 6) (Fin 6) (ZMod 3) := 1 - (qV z)⁻¹ • vecMulVec z (wv z)

private theorem reflM_mulVec (z x : V6) : reflM z *ᵥ x = x - ((qV z)⁻¹ * bil x z) • z := by
  unfold reflM
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, one_mulVec, vecMulVec_mulVec, dot_wv]
  simp [op_smul_eq_smul, smul_smul]

private theorem reflM_mul_self (z : V6) (hz : qV z ≠ 0) : reflM z * reflM z = 1 := by
  have hμ : (qV z)⁻¹ * qV z = 1 := inv_mul_cancel₀ hz
  have hAA : vecMulVec z (wv z) * vecMulVec z (wv z) = (2 * qV z) • vecMulVec z (wv z) := by
    rw [vecMulVec_mul_vecMulVec, dot_wv_self, vecMulVec_smul]
  have hc : (qV z)⁻¹ * (qV z)⁻¹ * (2 * qV z) - (qV z)⁻¹ - (qV z)⁻¹ = 0 := by
    linear_combination (2 * (qV z)⁻¹) * hμ
  unfold reflM
  simp only [sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hAA, smul_smul]
  linear_combination (norm := module) hc • vecMulVec z (wv z)

private theorem qV_add (u v : V6) : qV (u + v) = qV u + qV v + bil u v := by
  unfold bil; ring

private theorem qV_sub (u v : V6) : qV (u - v) = qV u + qV v - bil u v := by
  rw [bil_coord]
  simp only [qV, Pi.sub_apply]
  ring

private theorem bil_add_right (u v w : V6) : bil u (v + w) = bil u v + bil u w := by
  simp only [bil_coord, Pi.add_apply]; ring

private theorem qV_sub_smul (x z : V6) (c : ZMod 3) :
    qV (x - c • z) = qV x - c * bil x z + c ^ 2 * qV z := by
  rw [bil_coord]
  simp only [qV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem qV_reflM (z x : V6) (hz : qV z ≠ 0) : qV (reflM z *ᵥ x) = qV x := by
  rw [reflM_mulVec, qV_sub_smul]
  have hμ : (qV z)⁻¹ * qV z = 1 := inv_mul_cancel₀ hz
  set b := bil x z
  linear_combination ((qV z)⁻¹ * b ^ 2) * hμ

private def reflU (z : V6) (hz : qV z ≠ 0) : GL6 :=
  ⟨reflM z, reflM z, reflM_mul_self z hz, reflM_mul_self z hz⟩

private theorem reflU_val (z : V6) (hz : qV z ≠ 0) :
    ((reflU z hz : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) = reflM z := rfl

private theorem reflU_mem (z : V6) (hz : qV z ≠ 0) :
    reflU z hz ∈ CFSG.MatrixModel.isometryCore qV :=
  Subgroup.subset_closure fun v => qV_reflM z v hz

private theorem qV_mulVec_of_mem {g : GL6} (hg : g ∈ CFSG.MatrixModel.isometryCore qV) (v : V6) :
    qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = qV v :=
  qV_smul_of_mem_isometryCore hg v

private theorem bil_mulVec_of_mem {g : GL6} (hg : g ∈ CFSG.MatrixModel.isometryCore qV) (u v : V6) :
    bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u) ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v)
      = bil u v := by
  unfold bil
  rw [← Matrix.mulVec_add, qV_mulVec_of_mem hg, qV_mulVec_of_mem hg, qV_mulVec_of_mem hg]

private theorem mat_eq_of_mulVec {A B : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ x : V6, A *ᵥ x = B *ᵥ x) :
    A = B :=
  Matrix.toLin'.injective (LinearMap.ext fun x => h x)

private theorem qV_neg (w : V6) : qV (-w) = qV w := by
  have key : ∀ (K : Type) [CommRing K] (w : Fin 6 → K),
      (-w) 0 ^ 2 + (-w) 1 ^ 2 + (-w) 2 ^ 2 + (-w) 3 ^ 2 + (-w) 4 ^ 2 - (-w) 5 ^ 2 =
        w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 + w 3 ^ 2 + w 4 ^ 2 - w 5 ^ 2 := by
    intro K _ w
    simp only [Pi.neg_apply]
    ring
  exact key (ZMod 3) w

private theorem bil_sub_right (u v w : V6) : bil u (v - w) = bil u v - bil u w := by
  rw [bil_coord, bil_coord, bil_coord]
  simp only [Pi.sub_apply]
  ring

private theorem reflU_fix (z : V6) (hz : qV z ≠ 0) (f : V6) (hf : bil f z = 0) :
    (reflU z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ f = f := by
  rw [reflU_val, reflM_mulVec, hf, mul_zero, zero_smul]
  simp

private theorem reflU_sub_apply (a c : V6) (hq : qV a = qV c) (h : qV (a - c) ≠ 0) :
    (reflU (a - c) h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = c := by
  rw [reflU_val, reflM_mulVec]
  have hb : bil a (a - c) = qV (a - c) := by
    rw [bil_sub_right, bil_self, qV_sub, ← hq]
    ring
  rw [hb, inv_mul_cancel₀ h, one_smul]
  abel

private theorem reflU_add_apply (a c : V6) (hq : qV a = qV c) (h : qV (a + c) ≠ 0) :
    (reflU (a + c) h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = -c := by
  rw [reflU_val, reflM_mulVec]
  have hb : bil a (a + c) = qV (a + c) := by
    rw [bil_add_right, bil_self, qV_add, ← hq]
    ring
  rw [hb, inv_mul_cancel₀ h, one_smul]
  abel

private theorem four_mul_zmod (x : ZMod 3) : 4 * x = x := by
  revert x; decide

private theorem exists_refl_pair (a c : V6) (hq : qV a = qV c) (ha : qV a ≠ 0) :
    ∃ g ∈ CFSG.MatrixModel.isometryCore qV,
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = c ∨
        (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = -c) ∧
      ∀ f : V6, bil f a = 0 → bil f c = 0 → (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ f = f := by
  by_cases h1 : qV (a - c) = 0
  · have hbil : bil a c = qV a + qV c := by
      have := (qV_sub a c).symm.trans h1
      exact (sub_eq_zero.mp this).symm
    have h2 : qV (a + c) ≠ 0 := by
      rw [qV_add, hbil, ← hq]
      have h4 : qV a + qV a + (qV a + qV a) = 4 * qV a := by ring
      rw [h4, four_mul_zmod]
      exact ha
    refine ⟨reflU (a + c) h2, reflU_mem _ h2, Or.inr (reflU_add_apply a c hq h2), ?_⟩
    intro f hfa hfc
    apply reflU_fix
    rw [bil_add_right, hfa, hfc]
    simp
  · refine ⟨reflU (a - c) h1, reflU_mem _ h1, Or.inl (reflU_sub_apply a c hq h1), ?_⟩
    intro f hfa hfc
    apply reflU_fix
    rw [bil_sub_right, hfa, hfc]
    simp

private def negM : Matrix (Fin 6) (Fin 6) (ZMod 3) := Matrix.scalar (Fin 6) (-1)

private theorem negM_mul : negM * negM = 1 := by
  unfold negM
  rw [← map_mul, show (-1 : ZMod 3) * -1 = 1 from by decide, map_one]

private def negU : GL6 := ⟨negM, negM, negM_mul, negM_mul⟩

private theorem negU_mulVec (v : V6) : (negU : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v = -v := by
  show negM *ᵥ v = -v
  ext i
  simp [negM, Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  exact (neg_one_mul _)

private theorem negU_mem : negU ∈ CFSG.MatrixModel.isometryCore qV :=
  Subgroup.subset_closure fun v => by
    rw [negU_mulVec, qV_neg]

private theorem exists_mulVec_eq (a c : V6) (hq : qV a = qV c) (ha : qV a ≠ 0) :
    ∃ g ∈ CFSG.MatrixModel.isometryCore qV, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = c := by
  obtain ⟨g, hg, hga, -⟩ := exists_refl_pair a c hq ha
  rcases hga with h | h
  · exact ⟨g, hg, h⟩
  · refine ⟨negU * g, Subgroup.mul_mem _ negU_mem hg, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h, negU_mulVec]
    exact neg_neg c

private theorem mdot_eq_comm :
    MDot = ⁅CFSG.MatrixModel.isometryCore qV, CFSG.MatrixModel.isometryCore qV⁆ :=
  rfl

private theorem conj_reflU (g : GL6) (hg : g ∈ CFSG.MatrixModel.isometryCore qV) (z : V6)
    (hz : qV z ≠ 0)
    (hgz : qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z) ≠ 0) :
    g * reflU z hz * g⁻¹ = reflU ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z) hgz := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, reflU_val, reflU_val]
  apply mat_eq_of_mulVec
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hGGi : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *
      ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3))
      = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hy : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]
  have hb : bil (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x) z = bil x
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z) := by
    rw [← bil_mulVec_of_mem hg (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x) z, hy]
  rw [reflM_mulVec, reflM_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hy, hb,
    qV_mulVec_of_mem hg z]

private theorem reflU_congr (z w : V6) (hz : qV z ≠ 0) (hw : qV w ≠ 0) (h : z = w) :
    reflU z hz = reflU w hw := by
  subst h
  rfl

private theorem reflU_mul_reflU_mem_MDot (z w : V6) (hz : qV z ≠ 0) (hw : qV w ≠ 0)
    (h : qV z = qV w) :
    reflU z hz * reflU w hw ∈ MDot := by
  obtain ⟨g, hg, hgz⟩ := exists_mulVec_eq z w h hz
  have hgz' : qV ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z) ≠ 0 := by
    rw [qV_mulVec_of_mem hg, h]; exact hw
  have hconj : g * reflU z hz * g⁻¹ = reflU w hw := by
    rw [conj_reflU g hg z hz hgz']
    exact reflU_congr _ _ _ _ hgz
  have hRR : reflU z hz * reflU z hz = 1 := by
    apply Units.ext
    rw [Units.val_mul, reflU_val, Units.val_one, reflM_mul_self z hz]
  have hcomm : (⁅(reflU z hz : GL6), (g : GL6)⁆ : GL6) = reflU z hz * reflU w hw := by
    rw [commutatorElement_def, ← hconj, inv_eq_of_mul_eq_one_right hRR]
    simp only [mul_assoc]
  rw [mdot_eq_comm, ← hcomm]
  exact Subgroup.commutator_mem_commutator (reflU_mem z hz) hg

private theorem conj_mem_MDot {g : GL6} (hg : g ∈ CFSG.MatrixModel.isometryCore qV) {m : GL6}
    (hm : m ∈ MDot) : g * m * g⁻¹ ∈ MDot := by
  rw [mdot_eq_comm] at hm ⊢
  have hc : ∀ x ∈ CFSG.MatrixModel.isometryCore qV,
      g * x * g⁻¹ ∈ CFSG.MatrixModel.isometryCore qV := fun x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hx) (Subgroup.inv_mem _ hg)
  have hle : ⁅CFSG.MatrixModel.isometryCore qV, CFSG.MatrixModel.isometryCore qV⁆ ≤
      (⁅CFSG.MatrixModel.isometryCore qV, CFSG.MatrixModel.isometryCore qV⁆).comap
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap]
    show g * (⁅(a : GL6), (b : GL6)⁆ : GL6) * g⁻¹ ∈ _
    rw [show g * (⁅(a : GL6), (b : GL6)⁆ : GL6) * g⁻¹ =
      (⁅(g * a * g⁻¹ : GL6), (g * b * g⁻¹ : GL6)⁆ : GL6) from by
      rw [commutatorElement_def, commutatorElement_def]; group]
    exact Subgroup.commutator_mem_commutator (hc a ha) (hc b hb)
  exact hle hm

private theorem bil_smul_left (c : ZMod 3) (u v : V6) : bil (c • u) v = c * bil u v := by
  rw [bil_coord, bil_coord]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem bil_comm' (u v : V6) : bil u v = bil v u := by
  rw [bil_coord, bil_coord]; ring

private theorem bil_smul_right (c : ZMod 3) (u v : V6) : bil u (c • v) = c * bil u v := by
  rw [bil_comm', bil_smul_left, bil_comm']

private def ptOf (v : V6) (hv : qV v = -1) : PtX := ⟨spn {v}, v, hv, rfl⟩

private theorem mul_two_neg_one_eq (a : ZMod 3) (h : a * (2 * -1) = 0) : a = 0 := by
  revert a; decide

private theorem zmod_two_ne (a : ZMod 3) (h : a * (2 * -1) = 0) : a = 0 := mul_two_neg_one_eq a h

private theorem qV_zero : qV 0 = 0 := by simp [qV]

private theorem ptOf_eq_iff (v w : V6) (hv : qV v = -1) (hw : qV w = -1) :
    ptOf v hv = ptOf w hw ↔ spn {v} = spn {w} := by
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

private theorem mem_spn_singleton (v w : V6) : w ∈ spn {v} ↔ ∃ a : ZMod 3, a • v = w :=
  Submodule.mem_span_singleton

private theorem adj_ptOf (v w : V6) (hv : qV v = -1) (hw : qV w = -1) :
    DeltaDot.Adj (ptOf v hv) (ptOf w hw) ↔ bil v w = 0 := by
  unfold DeltaDot
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h v (Submodule.mem_span_singleton_self v) w (Submodule.mem_span_singleton_self w)
    · rw [bil_comm']
      exact h w (Submodule.mem_span_singleton_self w) v (Submodule.mem_span_singleton_self v)
  · intro h
    refine ⟨?_, Or.inl ?_⟩
    · intro heq
      have hsp := (ptOf_eq_iff v w hv hw).mp heq
      have hwmem : w ∈ spn {v} := by
        rw [hsp]; exact Submodule.mem_span_singleton_self w
      rw [mem_spn_singleton] at hwmem
      obtain ⟨a, rfl⟩ := hwmem
      rw [bil_smul_right, bil_self, hv] at h
      have ha : a = 0 := zmod_two_ne a h
      rw [ha, zero_smul, qV_zero] at hw
      exact absurd hw (by decide)
    · intro x hx y hy
      change x ∈ spn {v} at hx
      change y ∈ spn {w} at hy
      rw [mem_spn_singleton] at hx hy
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      rw [bil_smul_left, bil_smul_right, h, mul_zero, mul_zero]

private theorem smul_spn_mat (M : Matrix (Fin 6) (Fin 6) (ZMod 3)) (v : V6) :
    M • spn {v} = spn {M *ᵥ v} := by
  change M • Submodule.span (ZMod 3) {v} = Submodule.span (ZMod 3) {M • v}
  rw [Submodule.smul_span, Set.smul_set_singleton]

private theorem smul_ptOf (g : ↥MDot) (v : V6) (hv : qV v = -1) :
    g • ptOf v hv = ptOf ((g : GL6) *ᵥ v) (by rw [qV_mulVec_of_mem (MDot_le_OVq g.2), hv]) := by
  apply Subtype.ext
  show ((g : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) • spn {v} = spn {(g : GL6) *ᵥ v}
  exact smul_spn_mat _ v

private theorem mem_V3plus_of_coords (v : V6) (h2 : v 2 = 0) (h3 : v 3 = 0) (h4 : v 4 = 0) :
    v ∈ V3plus := by
  have hv : v = v 0 • x1 + v 1 • x2 + v 5 • x6 := by
    funext i
    fin_cases i <;> simp [x1, x2, x6, xvec, Pi.single_apply, h2, h3, h4]
  rw [hv]
  unfold V3plus spn
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_) <;>
    exact Submodule.subset_span (by simp)

private theorem V3plus_coords (v : V6) (hv : v ∈ V3plus) : v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 := by
  unfold V3plus spn at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp [x1, x2, x6, xvec, Pi.single_apply]
  | zero => simp
  | add x y _ _ hx hy => exact ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1],
      by simp [hx.2.2, hy.2.2]⟩
  | smul c x _ hx => exact ⟨by simp [hx.1], by simp [hx.2.1], by simp [hx.2.2]⟩

private theorem mem_V3plus_iff (v : V6) : v ∈ V3plus ↔ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 :=
  ⟨V3plus_coords v, fun h => mem_V3plus_of_coords v h.1 h.2.1 h.2.2⟩

private theorem spn_smul_eq (a : ZMod 3) (ha : a ≠ 0) (w : V6) : spn {a • w} = spn {w} := by
  unfold spn
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) w

private theorem pt_eq_of_smul (v w : V6) (hv : qV v = -1) (hw : qV w = -1) (a : ZMod 3) (ha : a ≠ 0)
    (h : v = a • w) : ptOf v hv = ptOf w hw := by
  rw [ptOf_eq_iff, h, spn_smul_eq a ha]

private def PA : PtX := ptOf x6 qV_x6

private theorem qV_x1_add_x2 : qV (x1 + x2) = -1 := by decide

private def PB : PtX := ptOf (x1 - x2) qV_x1_sub_x2

private def PC : PtX := ptOf (x1 + x2) qV_x1_add_x2

private theorem spn_le_iff (v : V6) (W : Sub6) : spn {v} ≤ W ↔ v ∈ W :=
  Submodule.span_singleton_le_iff_mem v W

private theorem mem_DeltaDotH_iff (S : PtX) : S ∈ DeltaDotH ↔ ∃ v : V6, ∃ hv : qV v = -1,
    S = ptOf v hv ∧ v ∈ V3plus := by
  obtain ⟨v, hv, hSv⟩ := S.2
  constructor
  · intro h
    have h' : S.1 ≤ V3plus := h
    rw [hSv, spn_le_iff] at h'
    exact ⟨v, hv, Subtype.ext hSv, h'⟩
  · rintro ⟨w, hw, hS, hwV⟩
    have h' : S.1 = spn {w} := by rw [hS]; rfl
    show S.1 ≤ V3plus
    rw [h', spn_le_iff]
    exact hwV

private theorem three_cases (a b c : ZMod 3) (h : a ^ 2 + b ^ 2 - c ^ 2 = -1) :
    (a = 0 ∧ b = 0 ∧ c ≠ 0) ∨ (a = b ∧ a ≠ 0 ∧ c = 0) ∨ (a = -b ∧ a ≠ 0 ∧ c = 0) := by
  revert a b c
  decide

private theorem DeltaDotH_eq : DeltaDotH = {PA, PB, PC} := by
  ext S
  rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff, mem_DeltaDotH_iff]
  constructor
  · rintro ⟨v, hv, rfl, hVv⟩
    obtain ⟨h2, h3, h4⟩ := (mem_V3plus_iff v).mp hVv
    have hq : (v 0) ^ 2 + (v 1) ^ 2 - (v 5) ^ 2 = -1 := by
      rw [← hv]
      simp [qV, h2, h3, h4]
    rcases three_cases (v 0) (v 1) (v 5) hq with ⟨ha, hb, hc⟩ | ⟨hab, ha, hc⟩ | ⟨hab, ha, hc⟩
    · left
      refine pt_eq_of_smul v x6 hv qV_x6 (v 5) hc ?_
      funext i
      fin_cases i <;> simp [x6, xvec, Pi.single_apply, h2, h3, h4, ha, hb]
    · right; right
      refine pt_eq_of_smul v (x1 + x2) hv qV_x1_add_x2 (v 0) ha ?_
      funext i
      fin_cases i <;> simp [x1, x2, xvec, Pi.single_apply, h2, h3, h4, hc, hab]
    · right; left
      refine pt_eq_of_smul v (x1 - x2) hv qV_x1_sub_x2 (v 0) ha ?_
      funext i
      fin_cases i <;> simp [x1, x2, xvec, Pi.single_apply, h2, h3, h4, hc, hab] <;>
        first | exact (neg_neg _).symm | norm_num | simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨x6, qV_x6, rfl, (mem_V3plus_iff x6).mpr (by simp [x6, xvec, Pi.single_apply])⟩
    · exact ⟨x1 - x2, qV_x1_sub_x2, rfl,
        (mem_V3plus_iff _).mpr (by simp [x1, x2, xvec, Pi.single_apply])⟩
    · exact ⟨x1 + x2, qV_x1_add_x2, rfl,
        (mem_V3plus_iff _).mpr (by simp [x1, x2, xvec, Pi.single_apply])⟩

private theorem PA_ne_PB : PA ≠ PB := by
  intro h
  have hsp := (ptOf_eq_iff _ _ _ _).mp h
  have hmem : x1 - x2 ∈ spn {x6} := by
    rw [hsp]; exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := (mem_spn_singleton x6 (x1 - x2)).mp hmem
  have h0 := congrFun ha 0
  simp [x6, x1, x2, xvec, Pi.single_apply] at h0 <;> exact absurd h0 (by decide)

private theorem PA_ne_PC : PA ≠ PC := by
  intro h
  have hsp := (ptOf_eq_iff _ _ _ _).mp h
  have hmem : x1 + x2 ∈ spn {x6} := by
    rw [hsp]; exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := (mem_spn_singleton x6 (x1 + x2)).mp hmem
  have h0 := congrFun ha 0
  simp [x6, x1, x2, xvec, Pi.single_apply] at h0 <;> exact absurd h0 (by decide)

private theorem PB_ne_PC : PB ≠ PC := by
  intro h
  have hsp := (ptOf_eq_iff _ _ _ _).mp h
  have hmem : x1 + x2 ∈ spn {x1 - x2} := by
    rw [hsp]; exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := (mem_spn_singleton (x1 - x2) (x1 + x2)).mp hmem
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [x1, x2, xvec, Pi.single_apply] at h0 h1
  revert h0 h1
  generalize a = b
  revert b
  decide

private theorem bil_PA_PB : bil x6 (x1 - x2) = 0 := by
  rw [bil_coord]; simp [x6, x1, x2, xvec, Pi.single_apply] <;> decide

private theorem bil_PA_PC : bil x6 (x1 + x2) = 0 := by
  rw [bil_coord]; simp [x6, x1, x2, xvec, Pi.single_apply] <;> decide

private theorem bil_PB_PC : bil (x1 - x2) (x1 + x2) = 0 := by
  rw [bil_coord]; simp [x1, x2, xvec, Pi.single_apply] <;> decide

private theorem DeltaDotH_isClique : DeltaDot.IsClique DeltaDotH := by
  rw [DeltaDotH_eq]
  intro S hS T hT hST
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS hT
  rcases hS with rfl | rfl | rfl <;> rcases hT with rfl | rfl | rfl
  · exact absurd rfl hST
  · exact (adj_ptOf _ _ _ _).mpr bil_PA_PB
  · exact (adj_ptOf _ _ _ _).mpr bil_PA_PC
  · exact (adj_ptOf _ _ _ _).mpr (by rw [bil_comm']; exact bil_PA_PB)
  · exact absurd rfl hST
  · exact (adj_ptOf _ _ _ _).mpr bil_PB_PC
  · exact (adj_ptOf _ _ _ _).mpr (by rw [bil_comm']; exact bil_PA_PC)
  · exact (adj_ptOf _ _ _ _).mpr (by rw [bil_comm']; exact bil_PB_PC)
  · exact absurd rfl hST

private theorem DeltaDotH_ncard : DeltaDotH.ncard = 3 :=
  Set.ncard_eq_three.mpr ⟨PA, PB, PC, PA_ne_PB, PA_ne_PC, PB_ne_PC, DeltaDotH_eq⟩

private theorem reflU_mul_self (z : V6) (hz : qV z ≠ 0) : reflU z hz * reflU z hz = 1 := by
  apply Units.ext
  rw [Units.val_mul, reflU_val, Units.val_one, reflM_mul_self z hz]

private theorem reflU_inv (z : V6) (hz : qV z ≠ 0) : (reflU z hz)⁻¹ = reflU z hz :=
  inv_eq_of_mul_eq_one_right (reflU_mul_self z hz)

private theorem negU_inv : negU⁻¹ = negU := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  exact negM_mul

private theorem zmod_ne_zero_cases (x : ZMod 3) (hx : x ≠ 0) : x = 1 ∨ x = -1 := by
  revert x
  decide

private theorem bil_neg_left (u v : V6) : bil (-u) v = -bil u v := by
  have key : ∀ (K : Type) [CommRing K] (a b : Fin 6 → K),
      2 * (-a 0 * b 0 + -a 1 * b 1 + -a 2 * b 2 + -a 3 * b 3 + -a 4 * b 4) - 2 * (-a 5 * b 5)
        = -(2 * (a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 + a 4 * b 4) - 2 * (a 5 * b 5)) := by
    intro K _ a b
    ring
  rw [bil_coord, bil_coord]
  simp only [Pi.neg_apply]
  exact key (ZMod 3) u v

private theorem bil_apply_pair (g : GL6) (hg : g ∈ CFSG.MatrixModel.isometryCore qV) (u v : V6) :
    bil ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u) ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v)
      = bil u v :=
  bil_mulVec_of_mem hg u v

private def Tv : Set V6 := {x6, x1 - x2, x1 + x2}

private def Tpm : Set V6 := {y | ∃ x ∈ Tv, y = x ∨ y = -x}

private theorem Tpm_neg {y : V6} (hy : y ∈ Tpm) : -y ∈ Tpm := by
  obtain ⟨x, hx, h⟩ := hy
  rcases h with h1 | h1
  · exact ⟨x, hx, Or.inr (by rw [h1])⟩
  · exact ⟨x, hx, Or.inl (by rw [h1]; exact neg_neg x)⟩

private theorem mem_Tpm_of_mem {x : V6} (hx : x ∈ Tv) : x ∈ Tpm := ⟨x, hx, Or.inl rfl⟩

private theorem Tv_sub_V3plus {x : V6} (hx : x ∈ Tv) : x ∈ V3plus := by
  simp only [Tv, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact (mem_V3plus_iff _).mpr (by simp [x6, xvec, Pi.single_apply])
  · exact (mem_V3plus_iff _).mpr (by simp [x1, x2, xvec, Pi.single_apply])
  · exact (mem_V3plus_iff _).mpr (by simp [x1, x2, xvec, Pi.single_apply])

private theorem Tpm_sub_V3plus {y : V6} (hy : y ∈ Tpm) : y ∈ V3plus := by
  obtain ⟨x, hx, h⟩ := hy
  rcases h with rfl | rfl
  · exact Tv_sub_V3plus hx
  · exact V3plus.neg_mem (Tv_sub_V3plus hx)

private theorem ptOf_mem_DeltaDotH {y : V6} (hy : qV y = -1) (hyT : y ∈ Tpm) :
    ptOf y hy ∈ DeltaDotH :=
  (mem_DeltaDotH_iff _).mpr ⟨y, hy, by rfl, Tpm_sub_V3plus hyT⟩

private def GoodH (h : GL6) : Prop :=
  h ∈ CFSG.MatrixModel.isometryCore qV ∧ ∀ y ∈ Tpm,
    (h : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ y ∈ Tpm ∧
      ((h⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ y ∈ Tpm

private theorem GoodH_mul {h k : GL6} (hh : GoodH h) (hk : GoodH k) : GoodH (h * k) := by
  refine ⟨Subgroup.mul_mem _ hh.1 hk.1, fun y hy => ⟨?_, ?_⟩⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hh.2 _ (hk.2 y hy).1).1
  · rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hk.2 _ (hh.2 y hy).2).2

private theorem GoodH_refl (z : V6) (hz : qV z ≠ 0)
    (h : ∀ x ∈ Tv, (reflU z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x ∈ Tpm) :
    GoodH (reflU z hz) := by
  refine ⟨reflU_mem z hz, fun y hy => ?_⟩
  rw [reflU_inv z hz]
  obtain ⟨x, hx, hyx⟩ := hy
  have key : (reflU z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ y ∈ Tpm := by
    rcases hyx with hyx | hyx
    · rw [hyx]
      exact h x hx
    · have e : (reflU z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (-x) =
          -((reflU z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x) := Matrix.mulVec_neg _ _
      rw [hyx, e]
      exact Tpm_neg (h x hx)
  exact ⟨key, key⟩

private theorem GoodH_negU : GoodH negU := by
  refine ⟨negU_mem, fun y hy => ?_⟩
  rw [negU_inv]
  rw [negU_mulVec]
  exact ⟨Tpm_neg hy, Tpm_neg hy⟩

private theorem reflU_self (z : V6) (hz : qV z ≠ 0) :
    (reflU z hz : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ z = -z := by
  have hμ : (qV z)⁻¹ * qV z = 1 := inv_mul_cancel₀ hz
  have hb : (qV z)⁻¹ * bil z z = 2 := by
    rw [bil_self]
    linear_combination (2 : ZMod 3) * hμ
  rw [reflU_val, reflM_mulVec, hb]
  have key : ∀ (K : Type) [CommRing K] (a : K), a - 2 * a = -a := by
    intro K _ a
    ring
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact key (ZMod 3) (z i)

private theorem qV_x3 : qV x3 = 1 := by decide

private theorem qV_x3_ne : qV x3 ≠ 0 := by
  rw [qV_x3]; decide

private theorem qV_x6_ne : qV x6 ≠ 0 := by
  rw [qV_x6]; decide

private theorem GoodH_R3 : GoodH (reflU x3 qV_x3_ne) := by
  apply GoodH_refl x3 qV_x3_ne
  intro x hx
  have hfix : bil x x3 = 0 := by
    simp only [Tv, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;>
    (rw [bil_coord]; simp [x6, x1, x2, x3, xvec, Pi.single_apply])
  rw [reflU_fix x3 qV_x3_ne x hfix]
  exact mem_Tpm_of_mem hx

private theorem GoodH_R6 : GoodH (reflU x6 qV_x6_ne) := by
  apply GoodH_refl x6 qV_x6_ne
  intro x hx
  simp only [Tv, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · rw [reflU_self x6 qV_x6_ne]
    exact Tpm_neg (mem_Tpm_of_mem (by simp [Tv]))
  · have hfix : bil (x1 - x2) x6 = 0 := by
      rw [bil_coord]; simp [x6, x1, x2, xvec, Pi.single_apply]
    rw [reflU_fix x6 qV_x6_ne _ hfix]
    exact mem_Tpm_of_mem (by simp [Tv])
  · have hfix : bil (x1 + x2) x6 = 0 := by
      rw [bil_coord]; simp [x6, x1, x2, xvec, Pi.single_apply]
    rw [reflU_fix x6 qV_x6_ne _ hfix]
    exact mem_Tpm_of_mem (by simp [Tv])

private def XSet : Set GL6 := {g | ∃ h : GL6, GoodH h ∧ ∃ m ∈ MDot, g = h * m}

private theorem XSet_mem_O {g : GL6} (hg : g ∈ XSet) : g ∈ CFSG.MatrixModel.isometryCore qV := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  exact Subgroup.mul_mem _ hh.1 (MDot_le_OVq hm)

private theorem XSet_mul {g k : GL6} (hg : g ∈ XSet) (hk : k ∈ XSet) : g * k ∈ XSet := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hg
  obtain ⟨h', hh', m', hm', rfl⟩ := hk
  refine ⟨h * h', GoodH_mul hh hh', (h'⁻¹ * m * h') * m', ?_, ?_⟩
  · have hc := conj_mem_MDot (g := h'⁻¹) (Subgroup.inv_mem _ hh'.1) hm
    exact Subgroup.mul_mem _ (by simpa using hc) hm'
  · group

private theorem XSet_of_good {h : GL6} (hh : GoodH h) : h ∈ XSet := ⟨h, hh, 1, one_mem _, by simp⟩

private theorem XSet_negU : negU ∈ XSet := XSet_of_good GoodH_negU

private theorem XSet_refl (z : V6) (hz : qV z ≠ 0) : reflU z hz ∈ XSet := by
  rcases zmod_ne_zero_cases (qV z) hz with h1 | h1
  · have hx3 : qV x3 = qV z := by rw [qV_x3, h1]
    refine ⟨reflU x3 qV_x3_ne, GoodH_R3, reflU x3 qV_x3_ne * reflU z hz,
      reflU_mul_reflU_mem_MDot x3 z qV_x3_ne hz hx3, ?_⟩
    rw [← mul_assoc, reflU_mul_self, one_mul]
  · have hx6 : qV x6 = qV z := by rw [qV_x6, h1]
    refine ⟨reflU x6 qV_x6_ne, GoodH_R6, reflU x6 qV_x6_ne * reflU z hz,
      reflU_mul_reflU_mem_MDot x6 z qV_x6_ne hz hx6, ?_⟩
    rw [← mul_assoc, reflU_mul_self, one_mul]

private theorem exists_refl_pair_X (a c : V6) (hq : qV a = qV c) (ha : qV a ≠ 0) :
    ∃ g ∈ XSet,
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = c ∨
        (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = -c) ∧
      ∀ f : V6, bil f a = 0 → bil f c = 0 → (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ f = f := by
  by_cases h1 : qV (a - c) = 0
  · have hbil : bil a c = qV a + qV c := by
      have := (qV_sub a c).symm.trans h1
      exact (sub_eq_zero.mp this).symm
    have h2 : qV (a + c) ≠ 0 := by
      rw [qV_add, hbil, ← hq]
      have h4 : qV a + qV a + (qV a + qV a) = 4 * qV a := by ring
      rw [h4, four_mul_zmod]
      exact ha
    refine ⟨reflU (a + c) h2, XSet_refl _ h2, Or.inr (reflU_add_apply a c hq h2), ?_⟩
    intro f hfa hfc
    apply reflU_fix
    rw [bil_add_right, hfa, hfc]
    simp
  · refine ⟨reflU (a - c) h1, XSet_refl _ h1, Or.inl (reflU_sub_apply a c hq h1), ?_⟩
    intro f hfa hfc
    apply reflU_fix
    rw [bil_sub_right, hfa, hfc]
    simp

private theorem exists_mulVec_eq_X (a c : V6) (hq : qV a = qV c) (ha : qV a ≠ 0) :
    ∃ g ∈ XSet, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = c := by
  obtain ⟨g, hg, hga, -⟩ := exists_refl_pair_X a c hq ha
  rcases hga with h | h
  · exact ⟨g, hg, h⟩
  · refine ⟨negU * g, XSet_mul XSet_negU hg, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h, negU_mulVec]
    exact neg_neg c

private theorem pt_rep (S : PtX) : ∃ (v : V6) (hv : qV v = -1), S = ptOf v hv := by
  obtain ⟨v, hv, hSv⟩ := S.2
  exact ⟨v, hv, Subtype.ext hSv⟩

private theorem triangle_smul (θ : Set PtX) (hθ : DeltaDot.IsClique θ) (h3 : θ.ncard = 3) :
    ∃ g : ↥MDot, g • θ = DeltaDotH := by
  obtain ⟨S1, S2, S3, h12, h13, h23, rfl⟩ := Set.ncard_eq_three.mp h3
  obtain ⟨v1, hv1, rfl⟩ := pt_rep S1
  obtain ⟨v2, hv2, rfl⟩ := pt_rep S2
  obtain ⟨v3, hv3, rfl⟩ := pt_rep S3
  have b12 : bil v1 v2 = 0 := (adj_ptOf v1 v2 hv1 hv2).mp (hθ (by simp) (by simp) h12)
  have b13 : bil v1 v3 = 0 := (adj_ptOf v1 v3 hv1 hv3).mp (hθ (by simp) (by simp) h13)
  have b23 : bil v2 v3 = 0 := (adj_ptOf v2 v3 hv2 hv3).mp (hθ (by simp) (by simp) h23)
  obtain ⟨g1, hg1, hg1v⟩ := exists_mulVec_eq_X v1 x6 (by rw [hv1, qV_x6])
    (by rw [hv1]; decide)
  have hO1 := XSet_mem_O hg1
  have hx6 : bil x6 ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2) = 0 := by
    rw [← hg1v, bil_apply_pair g1 hO1, b12]
  have hq2 : qV ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2) = qV (x1 - x2) := by
    rw [qV_mulVec_of_mem hO1, hv2, qV_x1_sub_x2]
  obtain ⟨g2, hg2, hg2s, hg2f⟩ := exists_refl_pair_X ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2)
    (x1 - x2) hq2 (by rw [hq2, qV_x1_sub_x2]; decide)
  have hO2 := XSet_mem_O hg2
  have hg2x6 : (g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := hg2f x6 hx6 bil_PA_PB
  have hq3 : qV ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v3)) = qV (x1 + x2) := by
    rw [qV_mulVec_of_mem hO2, qV_mulVec_of_mem hO1, hv3, qV_x1_add_x2]
  have e1 : bil x6 ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v3)) = 0 := by
    rw [← hg2x6, bil_apply_pair g2 hO2, ← hg1v, bil_apply_pair g1 hO1, b13]
  have e2 : bil ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2))
      ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
        ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v3)) = 0 := by
    rw [bil_apply_pair g2 hO2, bil_apply_pair g1 hO1, b23]
  have e3 : bil ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2)) (x1 + x2) = 0 := by
    rcases hg2s with h | h
    · rw [h]; exact bil_PB_PC
    · rw [h, bil_neg_left, bil_PB_PC]
      exact neg_zero
  obtain ⟨g3, hg3, hg3s, hg3f⟩ := exists_refl_pair_X
    ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v3))
    (x1 + x2) hq3 (by rw [hq3, qV_x1_add_x2]; decide)
  have hg3x6 : (g3 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = x6 := hg3f x6 e1 bil_PA_PC
  have hg3w2 : (g3 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2))
      = (g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2) :=
    hg3f _ e2 e3
  have hg0 : ∀ v : V6, (((g3 * g2 * g1 : GL6)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v =
      (g3 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ ((g2 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
        ((g1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v)) := by
    intro v
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hg0mem : g3 * g2 * g1 ∈ XSet := XSet_mul (XSet_mul hg3 hg2) hg1
  obtain ⟨h, hh, m, hm, hgeq⟩ := hg0mem
  have hm_eq : ∀ v : V6, (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v =
      ((h⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
        (((g3 * g2 * g1 : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) := by
    intro v
    rw [hgeq, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hT : ∀ v : V6, (((g3 * g2 * g1 : GL6)) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v ∈ Tpm →
      (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v ∈ Tpm := by
    intro v hv
    rw [hm_eq v]
    exact (hh.2 _ hv).2
  have hT1 : (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v1 ∈ Tpm := by
    apply hT
    rw [hg0, hg1v, hg2x6, hg3x6]
    exact mem_Tpm_of_mem (by simp [Tv])
  have hT2 : (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v2 ∈ Tpm := by
    apply hT
    rw [hg0, hg3w2]
    rcases hg2s with h | h
    · rw [h]; exact mem_Tpm_of_mem (by simp [Tv])
    · rw [h]; exact Tpm_neg (mem_Tpm_of_mem (by simp [Tv]))
  have hT3 : (m : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v3 ∈ Tpm := by
    apply hT
    rw [hg0]
    rcases hg3s with h | h
    · rw [h]; exact mem_Tpm_of_mem (by simp [Tv])
    · rw [h]; exact Tpm_neg (mem_Tpm_of_mem (by simp [Tv]))
  have hsub : ((⟨m, hm⟩ : ↥MDot) • ({ptOf v1 hv1, ptOf v2 hv2, ptOf v3 hv3} : Set PtX))
      ⊆ DeltaDotH := by
    rintro _ ⟨S, hS, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hS
    dsimp only
    rcases hS with rfl | rfl | rfl
    · rw [smul_ptOf]; exact ptOf_mem_DeltaDotH _ hT1
    · rw [smul_ptOf]; exact ptOf_mem_DeltaDotH _ hT2
    · rw [smul_ptOf]; exact ptOf_mem_DeltaDotH _ hT3
  have hcard : ((⟨m, hm⟩ : ↥MDot) • ({ptOf v1 hv1, ptOf v2 hv2, ptOf v3 hv3} : Set PtX)).ncard
      = 3 := by
    rw [← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective _)]
    exact Set.ncard_eq_three.mpr ⟨_, _, _, h12, h13, h23, rfl⟩
  refine ⟨⟨m, hm⟩, ?_⟩
  exact Set.eq_of_subset_of_ncard_le hsub (by rw [DeltaDotH_ncard, hcard])
    (by rw [DeltaDotH_eq]; exact Set.toFinite _)

private theorem mulVec_inv_mulVec (g : GL6) (v : V6) :
    ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem mulVec_mulVec_inv (g : GL6) (v : V6) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
      (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

private theorem bil_pull (g : GL6) (hg : g ∈ CFSG.MatrixModel.isometryCore qV) (t u : V6) :
    bil (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ t) u =
      bil t ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ u) := by
  have h := bil_apply_pair g hg (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ t) u
  rw [mulVec_mulVec_inv] at h
  exact h.symm

private theorem qV_pull (g : GL6) (hg : g ∈ CFSG.MatrixModel.isometryCore qV) (t : V6) :
    qV (((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ t) = qV t :=
  qV_mulVec_of_mem (Subgroup.inv_mem _ hg) t

private def tup5 (u : V6) : T5 := (u 0, u 1, u 2, u 3, u 4)

private def tup6 (C : T5) : V6 := ![C.1, C.2.1, C.2.2.1, C.2.2.2.1, C.2.2.2.2, 0]

private theorem tup6_five (C : T5) : tup6 C 5 = 0 := rfl

private theorem tup5_tup6 (C : T5) : tup5 (tup6 C) = C := rfl

private theorem qV_tup6 (C : T5) : qV (tup6 C) = qT C := by
  simp only [qV, qT, tup6]
  simp

private theorem qV_tup5 (u : V6) : qT (tup5 u) = qV u + u 5 ^ 2 := by
  simp only [qT, qV, tup5]
  ring

private theorem bil_tup5 (u v : V6) : bil u v = 2 * dT (tup5 u) (tup5 v) - 2 * (u 5 * v 5) := by
  rw [bil_coord]
  simp only [dT, tup5]

private theorem bil_tup6 (C : T5) (v : V6) : bil (tup6 C) v = 2 * dT C (tup5 v) := by
  rw [bil_tup5, tup5_tup6, tup6_five]
  ring

private theorem bil_tup5_zero5 (u v : V6) (hu : u 5 = 0) : bil u v = 2 * dT (tup5 u) (tup5 v) := by
  rw [bil_tup5, hu]
  simp

private theorem neg_one_smul_V6 (a : V6) : (-1 : ZMod 3) • a = -a := by
  funext i
  show (-1 : ZMod 3) * a i = -a i
  exact neg_one_mul (a i)

private theorem mulVec_neg_gen (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) (z : V6) :
    g *ᵥ (-z) = -(g *ᵥ z) :=
  Matrix.mulVec_neg _ _

private theorem two_mul_eq_zero_key :
    ∀ x y : ZMod 3, 2 * 0 - 2 * (x * y) = 0 → x ≠ 0 → y ≠ 0 → False := by
  decide

private theorem bil_x6_left (w : V6) : bil x6 w = w 5 := by
  rw [bil_coord]
  simp only [x6, xvec, Pi.single_apply]
  simp
  generalize w 5 = x
  revert x
  decide

private theorem vec_eq_of_tup (u v : V6) (hu : u 5 = 0) (hv : v 5 = 0) (h : tup5 u = tup5 v) :
    u = v := by
  simp only [tup5, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4, hu, hv]

private theorem tup5_neg (u : V6) : tup5 (-u) = neg5 (tup5 u) := by
  simp [tup5, neg5]

private theorem zmod_sq_of_ne (x : ZMod 3) (hx : x ≠ 0) : x ^ 2 = 1 := by
  revert x
  decide

private theorem two_ne_zero_z3 : (2 : ZMod 3) ≠ 0 := by decide

private theorem tup5_x6 : tup5 x6 = (0, 0, 0, 0, 0) := by
  simp [tup5, x6, xvec, Pi.single_apply]

private theorem dT_zero_right (C : T5) : dT C (0, 0, 0, 0, 0) = 0 := by
  simp [dT]

private theorem exists_perp_pair (vu vv : V6) (hu : qV vu = -1) (hv : qV vv = -1)
    (hb : bil vu vv ≠ 0)
    (hne : ∀ c : ZMod 3, vv ≠ c • vu) :
    ∃ t : V6, qV t = -1 ∧ bil t vu = 0 ∧ bil t vv = 0 := by
  obtain ⟨g, hg, hgu⟩ := exists_mulVec_eq vu x6 (by rw [hu, qV_x6]) (by rw [hu]; decide)
  obtain ⟨w, hw⟩ : ∃ w : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ vv = w := ⟨_, rfl⟩
  have hwq : qV w = -1 := by rw [← hw, qV_mulVec_of_mem hg, hv]
  have hbw : bil x6 w = bil vu vv := by
    rw [← hgu, ← hw, bil_apply_pair g hg]
  have hw5 : w 5 ≠ 0 := fun h => hb (by rw [← hbw, bil_x6_left, h])
  have hy : tup5 w ≠ (0, 0, 0, 0, 0) := by
    intro h0
    have hi : tup5 w = (0, 0, 0, 0, 0) := h0
    simp only [tup5, Prod.mk.injEq] at hi
    obtain ⟨h0', h1', h2', h3', h4'⟩ := hi
    have hwx : w = w 5 • x6 := by
      funext i
      fin_cases i <;> simp [x6, xvec, Pi.single_apply, h0', h1', h2', h3', h4']
    have e1 : vv = ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w := by
      rw [← hw, mulVec_inv_mulVec]
    have e2 : ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = vu := by
      rw [← hgu, mulVec_inv_mulVec]
    have e3 : ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w =
        ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (w 5 • x6) := congrArg _ hwx
    rw [Matrix.mulVec_smul, e2] at e3
    have hvv : vv = w 5 • vu := by
      rw [e1, e3]
    exact hne (w 5) hvv
  have hw5sq : w 5 ^ 2 = 1 := zmod_sq_of_ne _ hw5
  have hqT : qT (tup5 w) = 0 := by
    rw [qV_tup5, hwq, hw5sq]
    decide
  obtain ⟨t5, ht5q, ht5y⟩ := diam5 (tup5 w) hqT hy
  have htq : qV (tup6 t5) = -1 := by
    rw [qV_tup6, ht5q]
    decide
  have htx : bil (tup6 t5) x6 = 0 := by
    rw [bil_tup6, tup5_x6, dT_zero_right, mul_zero]
  have htw : bil (tup6 t5) w = 0 := by
    rw [bil_tup6, ht5y, mul_zero]
  refine ⟨((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ tup6 t5, ?_, ?_, ?_⟩
  · rw [qV_pull g hg, htq]
  · rw [bil_pull g hg, hgu, htx]
  · rw [bil_pull g hg, hw, htw]

private theorem tup5_ne_zero_of (vu vw : V6) (hu : qV vu = -1) (hqw : qV vw = -1)
    (hnew : ∀ c : ZMod 3, vw ≠ c • vu) (g : GL6) (hg : g ∈ CFSG.MatrixModel.isometryCore qV)
    (hgu : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ vu = x6) (w : V6)
    (hwd : (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ vw = w) (hw5 : w 5 ≠ 0) :
    tup5 w ≠ (0, 0, 0, 0, 0) := by
  intro h0
  have hi : tup5 w = (0, 0, 0, 0, 0) := h0
  simp only [tup5, Prod.mk.injEq] at hi
  obtain ⟨h0', h1', h2', h3', h4'⟩ := hi
  have hwx : w = w 5 • x6 := by
    funext i
    fin_cases i <;> simp [x6, xvec, Pi.single_apply, h0', h1', h2', h3', h4']
  have e1 : vw = ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w := by
    rw [← hwd, mulVec_inv_mulVec]
  have e2 : ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x6 = vu := by
    rw [← hgu, mulVec_inv_mulVec]
  have e3 : ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ w =
      ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (w 5 • x6) := congrArg _ hwx
  rw [Matrix.mulVec_smul, e2] at e3
  have hvv : vw = w 5 • vu := by
    rw [e1, e3]
  exact hnew (w 5) hvv

private theorem exists_perp_common (vu vw a b : V6) (hu : qV vu = -1) (hqw : qV vw = -1)
    (hbuw : bil vu vw ≠ 0) (hnew : ∀ c : ZMod 3, vw ≠ c • vu)
    (hqa : qV a = -1) (hqb : qV b = -1) (hau : bil a vu = 0) (haw : bil a vw = 0)
    (hbu : bil b vu = 0) (hbw : bil b vw = 0) (hab : bil a b ≠ 0)
    (hneab : ∀ c : ZMod 3, b ≠ c • a) :
    ∃ c : V6, qV c = -1 ∧ bil c vu = 0 ∧ bil c vw = 0 ∧ bil c a = 0 ∧ bil c b = 0 := by
  obtain ⟨g, hg, hgu⟩ := exists_mulVec_eq vu x6 (by rw [hu, qV_x6]) (by rw [hu]; decide)
  obtain ⟨w, hwd⟩ : ∃ w : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ vw = w := ⟨_, rfl⟩
  obtain ⟨a', had⟩ : ∃ a' : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a = a' := ⟨_, rfl⟩
  obtain ⟨b', hbd⟩ : ∃ b' : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ b = b' := ⟨_, rfl⟩
  have hqw' : qV w = -1 := by rw [← hwd, qV_mulVec_of_mem hg, hqw]
  have hqa' : qV a' = -1 := by rw [← had, qV_mulVec_of_mem hg, hqa]
  have hqb' : qV b' = -1 := by rw [← hbd, qV_mulVec_of_mem hg, hqb]
  have hbw' : bil x6 w = bil vu vw := by
    rw [← hgu, ← hwd, bil_apply_pair g hg]
  have hw5 : w 5 ≠ 0 := fun h => hbuw (by rw [← hbw', bil_x6_left, h])
  have ha5 : a' 5 = 0 := by
    have e2 : bil x6 a' = bil vu a := by rw [← hgu, ← had, bil_apply_pair g hg]
    have e3 : a' 5 = bil vu a := (bil_x6_left a').symm.trans e2
    rw [e3, bil_comm', hau]
  have hb5 : b' 5 = 0 := by
    have e2 : bil x6 b' = bil vu b := by rw [← hgu, ← hbd, bil_apply_pair g hg]
    have e3 : b' 5 = bil vu b := (bil_x6_left b').symm.trans e2
    rw [e3, bil_comm', hbu]
  have hwy : tup5 w ≠ (0, 0, 0, 0, 0) :=
    tup5_ne_zero_of vu vw hu hqw hnew g hg hgu w hwd hw5
  have hqT : qT (tup5 w) = 0 := by
    rw [qV_tup5, hqw', zmod_sq_of_ne _ hw5]
    decide
  have hdA : dT (tup5 a') (tup5 w) = 0 := by
    have e : bil a' w = bil a vw := by rw [← had, ← hwd, bil_apply_pair g hg]
    rw [bil_tup5_zero5 a' w ha5, haw] at e
    exact (mul_eq_zero.mp e).resolve_left two_ne_zero_z3
  have hdB : dT (tup5 b') (tup5 w) = 0 := by
    have e : bil b' w = bil b vw := by rw [← hbd, ← hwd, bil_apply_pair g hg]
    rw [bil_tup5_zero5 b' w hb5, hbw] at e
    exact (mul_eq_zero.mp e).resolve_left two_ne_zero_z3
  have hdAB : dT (tup5 a') (tup5 b') ≠ 0 := by
    intro h0
    have e : bil a' b' = bil a b := by rw [← had, ← hbd, bil_apply_pair g hg]
    apply hab
    rw [← e, bil_tup5_zero5 a' b' ha5, h0, mul_zero]
  have hqA : qT (tup5 a') = 2 := by
    rw [qV_tup5, hqa', ha5]
    decide
  have hqB : qT (tup5 b') = 2 := by
    rw [qV_tup5, hqb', hb5]
    decide
  have hAB : tup5 a' ≠ tup5 b' := by
    intro h
    have heq : a' = b' := vec_eq_of_tup a' b' ha5 hb5 h
    have hab' : a = b := by
      calc a = ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
            ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a) := (mulVec_inv_mulVec g a).symm
        _ = ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
            ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ b) := by rw [had, hbd, heq]
        _ = b := mulVec_inv_mulVec g b
    exact hneab 1 (by simp [hab'])
  have hABn : tup5 a' ≠ neg5 (tup5 b') := by
    intro h
    have heq : a' = -b' := by
      apply vec_eq_of_tup a' (-b') ha5 (by show -(b' 5) = 0; rw [hb5]; exact neg_zero)
      rw [tup5_neg]
      exact h
    have hab' : a = -b := by
      calc a = ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
            ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ a) := (mulVec_inv_mulVec g a).symm
        _ = ((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ
            ((g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ (-b)) := by
          rw [mulVec_neg_gen, had, hbd, heq]
        _ = -b := mulVec_inv_mulVec g (-b)
    exact hneab (-1) (by rw [neg_one_smul_V6, hab']; exact (neg_neg b).symm)
  obtain ⟨C5, hC5q, hC5y, hC5a, hC5b⟩ :=
    h2_5 (tup5 w) hqT hwy (tup5 a') (tup5 b') hqA hdA hqB hdB hdAB hAB hABn
  have hc'q : qV (tup6 C5) = -1 := by
    rw [qV_tup6, hC5q]
    decide
  have hc'x : bil (tup6 C5) x6 = 0 := by
    rw [bil_tup6, tup5_x6, dT_zero_right, mul_zero]
  have hc'w : bil (tup6 C5) w = 0 := by
    rw [bil_tup6, hC5y, mul_zero]
  have hc'a : bil (tup6 C5) a' = 0 := by
    rw [bil_tup6, hC5a, mul_zero]
  have hc'b : bil (tup6 C5) b' = 0 := by
    rw [bil_tup6, hC5b, mul_zero]
  refine ⟨((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ tup6 C5, ?_, ?_, ?_, ?_, ?_⟩
  · rw [qV_pull g hg, hc'q]
  · rw [bil_pull g hg, hgu, hc'x]
  · rw [bil_pull g hg, hwd, hc'w]
  · rw [bil_pull g hg, had, hc'a]
  · rw [bil_pull g hg, hbd, hc'b]

private theorem exists_perp_triple (x0 x2 x3 : V6) (h0 : qV x0 = -1) (h2 : qV x2 = -1)
    (h3 : qV x3 = -1) (b02 : bil x0 x2 ≠ 0) (b03 : bil x0 x3 ≠ 0) (b23 : bil x2 x3 = 0) :
    ∃ c : V6, qV c = -1 ∧ bil c x0 = 0 ∧ bil c x2 = 0 ∧ bil c x3 = 0 := by
  obtain ⟨g, hg, hg0⟩ := exists_mulVec_eq x0 x6 (by rw [h0, qV_x6]) (by rw [h0]; decide)
  obtain ⟨p, hpd⟩ : ∃ p : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x2 = p := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r : V6, (g : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ x3 = r := ⟨_, rfl⟩
  have hpq : qV p = -1 := by rw [← hpd, qV_mulVec_of_mem hg, h2]
  have hrq : qV r = -1 := by rw [← hrd, qV_mulVec_of_mem hg, h3]
  have hbp : bil x6 p = bil x0 x2 := by
    rw [← hg0, ← hpd, bil_apply_pair g hg]
  have hbr : bil x6 r = bil x0 x3 := by
    rw [← hg0, ← hrd, bil_apply_pair g hg]
  have hp5 : p 5 ≠ 0 := fun h => b02 (by rw [← hbp, bil_x6_left, h])
  have hr5 : r 5 ≠ 0 := fun h => b03 (by rw [← hbr, bil_x6_left, h])
  have hpr : bil p r = 0 := by
    rw [← hpd, ← hrd, bil_apply_pair g hg]
    exact b23
  have hqp : qT (tup5 p) = 0 := by
    rw [qV_tup5, hpq, zmod_sq_of_ne _ hp5]
    decide
  have hqr : qT (tup5 r) = 0 := by
    rw [qV_tup5, hrq, zmod_sq_of_ne _ hr5]
    decide
  have hdpr : dT (tup5 p) (tup5 r) ≠ 0 := by
    intro h0
    have e := hpr
    rw [bil_tup5, h0] at e
    exact two_mul_eq_zero_key (p 5) (r 5) e hp5 hr5
  obtain ⟨t5, ht5q, ht5p, ht5r⟩ := h3_5 (tup5 p) (tup5 r) hqp hqr hdpr
  have htq : qV (tup6 t5) = -1 := by
    rw [qV_tup6, ht5q]
    decide
  have htx : bil (tup6 t5) x6 = 0 := by
    rw [bil_tup6, tup5_x6, dT_zero_right, mul_zero]
  have htp : bil (tup6 t5) p = 0 := by
    rw [bil_tup6, ht5p, mul_zero]
  have htr : bil (tup6 t5) r = 0 := by
    rw [bil_tup6, ht5r, mul_zero]
  refine ⟨((g⁻¹ : GL6) : Matrix (Fin 6) (Fin 6) (ZMod 3)) *ᵥ tup6 t5, ?_, ?_, ?_, ?_⟩
  · rw [qV_pull g hg, htq]
  · rw [bil_pull g hg, hg0, htx]
  · rw [bil_pull g hg, hpd, htp]
  · rw [bil_pull g hg, hrd, htr]

private theorem ne_smul_of_pt_ne (vu vv : V6) (hu : qV vu = -1) (hv : qV vv = -1)
    (h : ptOf vu hu ≠ ptOf vv hv) : ∀ c : ZMod 3, vv ≠ c • vu := by
  intro c hc
  apply h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    rw [hc, qV_zero] at hv
    exact absurd hv (by decide)
  exact (pt_eq_of_smul vv vu hv hu c hc0 hc).symm

private theorem dist_two_facts (u w : PtX) (h : DeltaDot.dist u w = 2) :
    u ≠ w ∧ ¬ DeltaDot.Adj u w := by
  constructor
  · rintro rfl
    rw [SimpleGraph.dist_self] at h
    exact absurd h (by decide)
  · intro hadj
    have h1 := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    rw [h] at h1
    simp at h1

private theorem common_nbr (u v : PtX) (huv : u ≠ v) (hnadj : ¬ DeltaDot.Adj u v) :
    ∃ w : PtX, DeltaDot.Adj u w ∧ DeltaDot.Adj w v := by
  obtain ⟨vu, hu, rfl⟩ := pt_rep u
  obtain ⟨vv, hv, rfl⟩ := pt_rep v
  have hb : bil vu vv ≠ 0 := fun h => hnadj ((adj_ptOf vu vv hu hv).mpr h)
  obtain ⟨t, ht, ht1, ht2⟩ := exists_perp_pair vu vv hu hv hb (ne_smul_of_pt_ne vu vv hu hv huv)
  refine ⟨ptOf t ht, (adj_ptOf vu t hu ht).mpr (by rw [bil_comm']; exact ht1),
    (adj_ptOf t vv ht hv).mpr ht2⟩

private theorem dist_le_two_pt (u v : PtX) : DeltaDot.dist u v ≤ 2 := by
  by_cases huv : u = v
  · subst huv
    rw [SimpleGraph.dist_self]
    exact Nat.zero_le _
  by_cases hadj : DeltaDot.Adj u v
  · have h1 := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h1
    omega
  · obtain ⟨w, h1, h2⟩ := common_nbr u v huv hadj
    have h3 := SimpleGraph.dist_le
      (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h3
    omega

private theorem reachable_pt (u v : PtX) : DeltaDot.Reachable u v := by
  by_cases huv : u = v
  · subst huv
    exact SimpleGraph.Reachable.refl _
  by_cases hadj : DeltaDot.Adj u v
  · exact hadj.reachable
  · obtain ⟨w, h1, h2⟩ := common_nbr u v huv hadj
    exact h1.reachable.trans h2.reachable

private theorem DeltaDot_connected : DeltaDot.Connected := by
  rw [SimpleGraph.connected_iff]
  exact ⟨fun u v => reachable_pt u v, ⟨xDot⟩⟩

private theorem h3_point (x0 x1 x2 x3 : PtX) (h01 : DeltaDot.Adj x0 x1) (h12 : DeltaDot.Adj x1 x2)
    (h23 : DeltaDot.Adj x2 x3) (d02 : DeltaDot.dist x0 x2 = 2) (d03 : DeltaDot.dist x0 x3 = 2)
    (d13 : DeltaDot.dist x1 x3 = 2) :
    ∃ v : PtX, DeltaDot.Adj v x0 ∧ DeltaDot.Adj v x2 ∧ DeltaDot.Adj v x3 := by
  obtain ⟨-, n02⟩ := dist_two_facts x0 x2 d02
  obtain ⟨-, n03⟩ := dist_two_facts x0 x3 d03
  obtain ⟨v0, h0, rfl⟩ := pt_rep x0
  obtain ⟨v2, h2, rfl⟩ := pt_rep x2
  obtain ⟨v3, h3, rfl⟩ := pt_rep x3
  have b02 : bil v0 v2 ≠ 0 := fun h => n02 ((adj_ptOf v0 v2 h0 h2).mpr h)
  have b03 : bil v0 v3 ≠ 0 := fun h => n03 ((adj_ptOf v0 v3 h0 h3).mpr h)
  have b23 : bil v2 v3 = 0 := (adj_ptOf v2 v3 h2 h3).mp h23
  obtain ⟨c, hc, hc0, hc2, hc3⟩ := exists_perp_triple v0 v2 v3 h0 h2 h3 b02 b03 b23
  exact ⟨ptOf c hc, (adj_ptOf c v0 hc h0).mpr hc0, (adj_ptOf c v2 hc h2).mpr hc2,
    (adj_ptOf c v3 hc h3).mpr hc3⟩

private theorem h2_point (u w : PtX) (huw : DeltaDot.dist u w = 2) :
    (DeltaDot.induce {v | DeltaDot.Adj u v ∧ DeltaDot.Adj w v}).Connected := by
  obtain ⟨hne, hnadj⟩ := dist_two_facts u w huw
  obtain ⟨c0, hc0u, hc0w⟩ := common_nbr u w hne hnadj
  obtain ⟨vu, hu, rfl⟩ := pt_rep u
  obtain ⟨vw, hw, rfl⟩ := pt_rep w
  have hbuw : bil vu vw ≠ 0 := fun h => hnadj ((adj_ptOf vu vw hu hw).mpr h)
  have hnew : ∀ c : ZMod 3, vw ≠ c • vu := ne_smul_of_pt_ne vu vw hu hw hne
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨⟨c0, hc0u, hc0w.symm⟩⟩⟩
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  by_cases hab : a = b
  · subst hab
    exact SimpleGraph.Reachable.refl _
  by_cases hadj : DeltaDot.Adj a b
  · exact SimpleGraph.Adj.reachable hadj
  · obtain ⟨vA, hA, rfl⟩ := pt_rep a
    obtain ⟨vB, hB, rfl⟩ := pt_rep b
    have hau : bil vA vu = 0 := by
      rw [bil_comm']; exact (adj_ptOf vu vA hu hA).mp ha.1
    have haw : bil vA vw = 0 := by
      rw [bil_comm']; exact (adj_ptOf vw vA hw hA).mp ha.2
    have hbu : bil vB vu = 0 := by
      rw [bil_comm']; exact (adj_ptOf vu vB hu hB).mp hb.1
    have hbw : bil vB vw = 0 := by
      rw [bil_comm']; exact (adj_ptOf vw vB hw hB).mp hb.2
    have hab' : bil vA vB ≠ 0 := fun h => hadj ((adj_ptOf vA vB hA hB).mpr h)
    have hneab : ∀ c : ZMod 3, vB ≠ c • vA := ne_smul_of_pt_ne vA vB hA hB hab
    obtain ⟨c, hc, hcu, hcw, hca, hcb⟩ :=
      exists_perp_common vu vw vA vB hu hw hbuw hnew hA hB hau haw hbu hbw hab' hneab
    have hcN : ptOf c hc ∈ {v : PtX | DeltaDot.Adj (ptOf vu hu) v ∧ DeltaDot.Adj (ptOf vw hw) v} :=
      ⟨(adj_ptOf vu c hu hc).mpr (by rw [bil_comm']; exact hcu),
        (adj_ptOf vw c hw hc).mpr (by rw [bil_comm']; exact hcw)⟩
    have hAc : DeltaDot.Adj (ptOf vA hA) (ptOf c hc) :=
      (adj_ptOf vA c hA hc).mpr (by rw [bil_comm']; exact hca)
    have hcB : DeltaDot.Adj (ptOf c hc) (ptOf vB hB) := (adj_ptOf c vB hc hB).mpr hcb
    exact (SimpleGraph.Adj.reachable (show (DeltaDot.induce {v : PtX | DeltaDot.Adj (ptOf vu hu) v ∧
      DeltaDot.Adj (ptOf vw hw) v}).Adj ⟨ptOf vA hA, ha⟩ ⟨ptOf c hc, hcN⟩ from hAc)).trans
      (SimpleGraph.Adj.reachable (show (DeltaDot.induce {v : PtX | DeltaDot.Adj (ptOf vu hu) v ∧
      DeltaDot.Adj (ptOf vw hw) v}).Adj ⟨ptOf c hc, hcN⟩ ⟨ptOf vB hB, hb⟩ from hcB))

private theorem DeltaDot_triangulable : CFSG.Quasithin.Asc94.Triangulable DeltaDot :=
  CFSG.Quasithin.Asc94.triangulable_of_diam_two dist_le_two_pt
    (fun u w h => h2_point u w h)
    (fun x0 x1 x2 x3 h01 h12 h23 d02 d03 d13 => h3_point x0 x1 x2 x3 h01 h12 h23 d02 d03 d13)

private theorem smul_adj_iff (m : ↥MDot) (x y : PtX) :
    DeltaDot.Adj (m • x) (m • y) ↔ DeltaDot.Adj x y := by
  obtain ⟨vx, hx, rfl⟩ := pt_rep x
  obtain ⟨vy, hy, rfl⟩ := pt_rep y
  rw [smul_ptOf, smul_ptOf, adj_ptOf, adj_ptOf, bil_apply_pair (m : GL6) (MDot_le_OVq m.2) vx vy]

private theorem rotRev_mono_set {V : Type} {C C' : Set (List V)} (hC : C ⊆ C') :
    CFSG.Quasithin.Asc94.rotRev C ⊆ CFSG.Quasithin.Asc94.rotRev C' := by
  rintro d ⟨e, he, h⟩
  exact ⟨e, hC he, h⟩

private theorem elemMove_mono_set {V : Type} {Γ : SimpleGraph V} {C C' : Set (List V)}
    {p q : List V}
    (h : CFSG.Quasithin.Asc94.ElemMove Γ C p q) (hC : C ⊆ C') :
    CFSG.Quasithin.Asc94.ElemMove Γ C' p q := by
  induction h with
  | backDel l₁ l₂ w v hadj => exact CFSG.Quasithin.Asc94.ElemMove.backDel l₁ l₂ w v hadj
  | backIns l₁ l₂ w v hadj => exact CFSG.Quasithin.Asc94.ElemMove.backIns l₁ l₂ w v hadj
  | cycIns l₁ l₂ c w hc h₁ h₂ =>
    exact CFSG.Quasithin.Asc94.ElemMove.cycIns l₁ l₂ c w (rotRev_mono_set hC hc) h₁ h₂
  | cycDel l₁ l₂ c w hc h₁ h₂ =>
    exact CFSG.Quasithin.Asc94.ElemMove.cycDel l₁ l₂ c w (rotRev_mono_set hC hc) h₁ h₂

private theorem moves_mono_set {V : Type} {Γ : SimpleGraph V} {C C' : Set (List V)} {x y : List V}
    (hC : C ⊆ C') (h : Relation.ReflTransGen (CFSG.Quasithin.Asc94.ElemMove Γ C) x y) :
    Relation.ReflTransGen (CFSG.Quasithin.Asc94.ElemMove Γ C') x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih (elemMove_mono_set hab hC)

private theorem inClosure_mono_set {V : Type} {Γ : SimpleGraph V} {C C' : Set (List V)} {c : List V}
    (h : CFSG.Quasithin.Asc94.InClosure Γ C c) (hC : C ⊆ C') :
    CFSG.Quasithin.Asc94.InClosure Γ C' c := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, moves_mono_set hC hw⟩

private theorem dsub_adj {x y : PtX} (hx : x ∈ DeltaDotH) (hy : y ∈ DeltaDotH)
    (h : DeltaDot.Adj x y) : DeltaDotSub.spanningCoe.Adj x y :=
  ⟨hx, hy, h⟩

private theorem clique3 (a b c : PtX) (hab : DeltaDot.Adj a b) (hbc : DeltaDot.Adj b c)
    (hca : DeltaDot.Adj c a) : DeltaDot.IsClique ({a, b, c} : Set PtX) := by
  intro x hx y hy hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · exact absurd (hx.trans hy.symm) hxy
  · rw [hx, hy]; exact hab
  · rw [hx, hy]; exact hca.symm
  · rw [hx, hy]; exact hab.symm
  · exact absurd (hx.trans hy.symm) hxy
  · rw [hx, hy]; exact hbc
  · rw [hx, hy]; exact hca
  · rw [hx, hy]; exact hbc.symm
  · exact absurd (hx.trans hy.symm) hxy

private theorem ngon3_mem (p : List PtX) (hp : CFSG.Quasithin.Asc94.IsNGon DeltaDot 3 p) :
    p ∈ {d : List PtX | ∃ (c₀ : List PtX) (g : ↥MDot),
      CFSG.Quasithin.Asc94.IsSubCycle DeltaDotSub c₀ ∧ d = c₀.map (g • ·)} := by
  obtain ⟨⟨⟨hne, hch⟩, hhead⟩, hlen, hnd⟩ := hp
  rcases p with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp at hlen
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true] at hch
    obtain ⟨hab, hbc, hcd⟩ := hch
    simp only [List.head?_cons, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.some.injEq] at hhead
    subst hhead
    have hab_ne : a ≠ b := by
      rintro rfl
      simp [List.dropLast, List.nodup_cons] at hnd
    have hac_ne : a ≠ c := by
      rintro rfl
      simp [List.dropLast, List.nodup_cons] at hnd
    have hbc_ne : b ≠ c := by
      rintro rfl
      simp [List.dropLast, List.nodup_cons] at hnd
    have hclique := clique3 a b c hab hbc hcd
    have hcard : ({a, b, c} : Set PtX).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨a, b, c, hab_ne, hac_ne, hbc_ne, rfl⟩
    obtain ⟨m, hm⟩ := triangle_smul {a, b, c} hclique hcard
    have hmem : ∀ x ∈ ({a, b, c} : Set PtX), m • x ∈ DeltaDotH := by
      intro x hx
      rw [← hm]
      exact Set.smul_mem_smul_set hx
    refine ⟨[m • a, m • b, m • c, m • a], m⁻¹, ⟨⟨⟨by simp, ?_⟩, by simp⟩, ?_⟩, ?_⟩
    · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
      exact ⟨dsub_adj (hmem a (by simp)) (hmem b (by simp)) ((smul_adj_iff m a b).mpr hab),
        dsub_adj (hmem b (by simp)) (hmem c (by simp)) ((smul_adj_iff m b c).mpr hbc),
        dsub_adj (hmem c (by simp)) (hmem a (by simp)) ((smul_adj_iff m c a).mpr hcd)⟩
    · intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hmem a (by simp)
      · exact hmem b (by simp)
      · exact hmem c (by simp)
      · exact hmem a (by simp)
    · simp [List.map, inv_smul_smul]
  · simp at hlen

private theorem DeltaDot_isBase : CFSG.Quasithin.Asc94.IsBase ↥MDot DeltaDot DeltaDotSub := by
  unfold CFSG.Quasithin.Asc94.IsBase
  intro c hc
  exact inClosure_mono_set (DeltaDot_triangulable c hc) (fun p hp => ngon3_mem p hp)

private theorem F_5_8_proved : CFSG.ASVolI.F_5_8 :=
  ⟨⟨DeltaDotH_isClique, DeltaDotH_ncard⟩, fun θ hθ h3 => triangle_smul θ hθ h3,
    ⟨DeltaDot_connected, DeltaDot_triangulable⟩, DeltaDot_isBase⟩

end ChF5S

theorem as_F_5_8 : F_5_8 := ChF5S.F_5_8_proved

end CFSG.ASVolI
