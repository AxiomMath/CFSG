module

public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Tim79aSec23Cp
public import CFSG.RankThree.GF2n.Tim79aSec23Tilde
public import CFSG.RankThree.GF2n.Tim79aWCQ
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki
open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.Transvection
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev XbarZ (V H : Subgroup G) : Type := Xbar V H ⧸ Subgroup.center (Xbar V H)

@[expose] def projZ (V H : Subgroup G) : Xbar V H →* XbarZ V H :=
  QuotientGroup.mk' (Subgroup.center (Xbar V H))

@[expose] noncomputable def qBar (V H : Subgroup G) : ℕ := Nat.card (barOf V H V)

@[expose] def VZ (V H : Subgroup G) : Subgroup (XbarZ V H) := (Vy V H).map (projZ V H)

@[expose] def rootClassZ (V H : Subgroup G) : Set (Subgroup (XbarZ V H)) :=
  {A | ∃ x : XbarZ V H, A = conjSub (VZ V H) x}

@[expose] def MeetsSq (V H : Subgroup G) : Prop :=
  ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H

structure Sec23Setup (M V Q P H : Subgroup G) : Prop where
  mc : MinCexWCQ M V Q P H
  data : Sec23Data V H
  degenerate : ∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4

@[expose] def CentreClause (V H : Subgroup G) : Prop :=
  Subgroup.center (Xbar V H) ≤ commutator (Xbar V H)

@[expose] def TransvConclusionSp (H : Type) [Group H] (Δ : Set (Subgroup H)) (f : ℕ) : Prop :=
  ∃ n : ℕ, ∃ hn : 2 ≤ n, ∃ Φ : ↥(StatedSp n (GaloisField 2 f)) →* H,
      Function.Bijective Φ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
        ∃ g, X = (conjSub ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup
          (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ

@[expose] def TransvConclusionSU (H : Type) [Group H] (Δ : Set (Subgroup H)) (f : ℕ)
    (hf : 1 ≤ f) : Prop :=
  ∃ m : ℕ, ∃ hm : 4 ≤ m,
      ∃ Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m) →* H,
        Function.Surjective Φ ∧ Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
          ∃ g, X = (conjSub ((Unitary.rootDatum (card_galoisField_two_mul hf) m).rootGroup
            (unitaryLongRoot m (by omega))) g).map Φ

theorem transvectionConclusion_iff (H : Type) [Group H] (Δ : Set (Subgroup H)) (f : ℕ)
    (hf : 1 ≤ f) :
    TransvectionConclusion H Δ f hf ↔ TransvConclusionSp H Δ f ∨ TransvConclusionSU H Δ f hf :=
  Iff.rfl

@[expose] def Sec23Two (V H : Subgroup G) : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ 2 ^ f = qBar V H ∧ Nonempty (XbarZ V H ≃* PSL2Model f) ∧
      ∃ S : Sylow 2 (XbarZ V H), (S : Subgroup (XbarZ V H)) = VZ V H) ∨
    (∃ n : ℕ, 1 ≤ n ∧ 2 ^ (2 * n + 1) = qBar V H ∧ Nonempty (XbarZ V H ≃* SzModel n) ∧
      ∃ S : Sylow 2 (XbarZ V H), VZ V H =
        (Subgroup.center (S : Subgroup (XbarZ V H))).map (S : Subgroup (XbarZ V H)).subtype) ∨
    (∃ f : ℕ, 2 ≤ f ∧ 2 ^ f = qBar V H ∧ Nonempty (XbarZ V H ≃* PSU3Model f) ∧
      ∃ S : Sylow 2 (XbarZ V H), VZ V H =
        (Subgroup.center (S : Subgroup (XbarZ V H))).map (S : Subgroup (XbarZ V H)).subtype)

@[expose] def Sec23Three (V H : Subgroup G) : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ 2 ^ f = qBar V H ∧ TransvConclusionSp (XbarZ V H) (rootClassZ V H) f

@[expose] def Sec23Four (V H : Subgroup G) : Prop :=
  ∃ f : ℕ, ∃ hf : 1 ≤ f, 2 ^ f = qBar V H ∧
    TransvConclusionSU (XbarZ V H) (rootClassZ V H) f hf

@[expose] def Sec25Concl (V H P : Subgroup G) : Prop :=
  (∀ g ∈ xOf V H, (∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H) →
      (P ⊓ xOf V H) ⊔ conjSubgroup g V = xOf V H ∧
      (P ⊓ wOf V H) ⊔ (conjSubgroup g V ⊓ wOf V H) = wOf V H ∧
      (P ⊓ wOf V H) ⊓ (conjSubgroup g V ⊓ wOf V H) = ⊥) ∧
    xOf V H ⊔ cPbar V H P = H ∧ Assembly.IsElemAbelian 2 (wOf V H ⊔ cPbar V H P)

@[expose] def Sec25Bar (V H P : Subgroup G) : Prop :=
  (∀ g ∈ xOf V H, (∃ u ∈ V, ∃ w ∈ conjSubgroup g V, ⁅u, w⁆ ∉ wOf V H) →
      ∀ x ∈ xOf V H, ∃ y ∈ (P ⊓ xOf V H) ⊔ conjSubgroup g V, ∃ w ∈ wOf V H, x = y * w) ∧
    P ≤ (P ⊓ xOf V H) ⊔ cPbar V H P

@[expose] def Tim79aIdentBenderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    MeetsSq V H → Timmesfeld.Connectivity.Disconnected (Dtilde V H) → Sec23Two V H

@[expose] def Tim79aIdentConnectedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    MeetsSq V H → ¬ Timmesfeld.Connectivity.Disconnected (Dtilde V H) →
    (Sec23Three V H ∨ Sec23Four V H) ∧ 4 ≤ qBar V H

@[expose] def Tim79aIdentL2SzStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    MeetsSq V H → Timmesfeld.Connectivity.Disconnected (Dtilde V H) →
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (XbarZ V H ≃* PSL2Model n)) ∨
      (∃ n : ℕ, 1 ≤ n ∧ Nonempty (XbarZ V H ≃* SzModel n))) → Sec23Two V H

@[expose] def Tim79aIdentU3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), Sec23Setup M V Q P H →
    MeetsSq V H → Timmesfeld.Connectivity.Disconnected (Dtilde V H) →
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (XbarZ V H ≃* PSU3Model n)) → Sec23Two V H

end CFSG.RankThree.GF2n.Tim79a
