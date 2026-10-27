module

public import CFSG.Quasithin.Background.SimsF5Defs

public section

namespace CFSG.Quasithin.SimsF5

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

section AbstractGraph

variable {M : Type} [Group M]

@[expose] def DeltaGraph (M0 R Tf : Subgroup M) : SimpleGraph (M ⧸ M0) :=
  SimpleGraph.fromRel fun u v => ∃ a b : M, (a : M ⧸ M0) = u ∧ (b : M ⧸ M0) = v ∧
    ∃ r ∈ R, r ∉ Tf ∧ ∃ m₁ ∈ M0, ∃ m₂ ∈ M0, a⁻¹ * b = m₁ * r * m₂

end AbstractGraph

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

open CFSG.Quasithin.Asc94

@[expose] def F53 : Prop :=
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

@[expose] def F54 : Prop :=
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

@[expose] def F55 : Prop :=
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

@[expose] def F56 : Prop :=
  ∀ (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E) (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y)
    (M : Type) [Group M] (ε : Y →* M) (z : M) (Tb : Subgroup E) (fb : ↥(M₁ ⊓ M₂)),
    HypF5 Gp M₁ M₂ β ε z Tb fb →
    M0Of β ε ⊔ Subgroup.normalizer (AOf (MiTwo β ε) (fOf β ε fb) : Set M) = ⊤

@[expose] def F57 : Prop :=
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

end

end CFSG.Quasithin.SimsF5
