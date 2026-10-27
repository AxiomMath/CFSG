module

public import CFSG.LocalAnalysis.StandardType.GGKD2Spec1615
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585
public import CFSG.Sporadic.Th.Max3.Core
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

namespace S2MathAs3_1615

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

noncomputable section

@[expose] def SmallLab (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨
    lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der ∨ lab.tag = .twB2

@[expose] def ClassicalLab (lab : LargeEvenLabel) : Prop := lab.tag = .A ∨ lab.tag = .twA

@[expose] def E6Lab (lab : LargeEvenLabel) : Prop := lab.tag = .E6 ∨ lab.tag = .twE6

@[expose] def RemainingLab (lab : LargeEvenLabel) : Prop :=
  ¬ SmallLab lab ∧ ¬ ClassicalLab lab ∧ ¬ E6Lab lab

@[expose] def corner1584_connected : Prop :=
  ∀ (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (rho : GGK0MarkedKacIface1587.MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin rho.row.D.orbits.length),
    rho.row.D.orbits[j].qs = true →
      ∀ g : rho.setup.D.model,
        (g : ModGL rho.tau Omega) ∈ E6Centralizer1585.connectedCentralizer rho →
        (∀ d ∈ E6Centralizer1585.component rho j,
          rho.modelAction g d ∈ E6Centralizer1585.component rho j) →
        GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel)
          (↥(E6Centralizer1585.component rho j) ⧸
            Subgroup.center ↥(E6Centralizer1585.component rho j)) →
        ∃ y : ↥(E6Centralizer1585.component rho j) ⧸
            Subgroup.center ↥(E6Centralizer1585.component rho j),
          ∀ d d' : ↥(E6Centralizer1585.component rho j),
            rho.modelAction g (d : R) = (d' : R) →
            (d' : ↥(E6Centralizer1585.component rho j) ⧸
                Subgroup.center ↥(E6Centralizer1585.component rho j)) =
              y * (d : ↥(E6Centralizer1585.component rho j) ⧸
                    Subgroup.center ↥(E6Centralizer1585.component rho j)) * y⁻¹

@[expose] def corner1584_small_labels : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a → SmallLab lab → False)

@[expose] def SplitLift (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R))
    {L' : Type} [Group L'] (ψ : L' →* R) (e : MulAut L') : Prop :=
  (lab.tag = .A ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ lab.n ∧
      ∃ (M : GL (Fin (lab.rank + 1)) K)
        (hMN : M ∈ Subgroup.normalizer
          ((LargeEvenSLGroup (Fin (lab.rank + 1)) K : Subgroup (GL (Fin (lab.rank + 1)) K)) :
            Set (GL (Fin (lab.rank + 1)) K))),
        M ^ 3 = 1 ∧
        ∃ theta : R ≃* LargeEvenProj (LargeEvenSLGroup (Fin (lab.rank + 1)) K),
          (∀ l : L', TableB.projConj (LargeEvenSLGroup (Fin (lab.rank + 1)) K) ⟨M, hMN⟩
              (theta (ψ l)) = theta (ψ (e l))) ∧
          (∀ φ ∈ I,
            ∃ β ∈ LargeEvenMatConjImage
                (LargeEvenProjMk (LargeEvenSLGroup (Fin (lab.rank + 1)) K)) Set.univ,
              ∀ r : R, β (theta r) = theta (φ r)))
  ∨ (lab.tag = .twA ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 lab.n K),
      ∃ (M : GL (Fin (lab.rank + 1)) K)
        (hMN : M ∈ Subgroup.normalizer
          ((unitarySU 2 lab.n K (lab.rank + 1) : Subgroup (GL (Fin (lab.rank + 1)) K)) :
            Set (GL (Fin (lab.rank + 1)) K))),
        M ^ 3 = 1 ∧ M ∈ LargeEvenGUSet (Fin (lab.rank + 1)) K (2 ^ lab.n) ∧
        ∃ theta : R ≃* LargeEvenProj (unitarySU 2 lab.n K (lab.rank + 1)),
          (∀ l : L', TableB.projConj (unitarySU 2 lab.n K (lab.rank + 1)) ⟨M, hMN⟩
              (theta (ψ l)) = theta (ψ (e l))) ∧
          (∀ φ ∈ I,
            ∃ β ∈ InndiagSU.inndiagU (d := lab.rank + 1) h (Nat.succ_pos lab.rank),
              ∀ r : R, β (theta r) = theta (φ r)))

@[expose] def corner1584_split_lift : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a →
          ClassicalLab lab → SplitLift lab R I ψ e → False)

@[expose] def corner1584_nonsplit_shape : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
          GGRankOneSetup I ψ 3 e J 3 a →
          ClassicalLab lab → ¬ SplitLift lab R I ψ e →
            (lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∧
              (¬ ∃ r : R, ∀ l : L', ψ (e l) = r * ψ l * r⁻¹) ∧
              NonsplitUnitaryModel ψ e I))

theorem corner1615Assembly_holds
    (hSmall : corner1584_small_labels) (hConn : corner1584_connected)
    (hRem : corner1584_connected → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
        LargeEvenLabelAll lab (fun R _ I _ => ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
        Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ∀ (e : MulAut L')
        (J : Subgroup L') (a : MulAut L'), GGRankOneSetup I ψ 3 e J 3 a → RemainingLab lab →
        False)) (hE6 : corner1584_connected → ∀ lab : LargeEvenLabel,
        LargeEvenInLambda2 lab → LargeEvenLabelAll lab (fun R _ I _ => ∀ (L' : Type) [Group L']
        [Finite L'] (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator
        L' = ⊤ → ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'), GGRankOneSetup I ψ 3 e J 3 a →
        E6Lab lab → False))
    (hSplit : corner1584_split_lift) (hNon : corner1584_nonsplit_shape) :
    StrongKD2 := by
  intro lab hlab
  by_cases hsmall : SmallLab lab
  · refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hSmall lab hlab)
    intro L' _ _ ψ hsurj hker hcomm e J a hsetup
    exact (h L' ψ hsurj hker hcomm e J a hsetup hsmall).elim
  · by_cases hclass : ClassicalLab lab
    · have hc := largeEvenLabelAll_and (hSplit lab hlab) (hNon lab hlab)
      refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) hc
      intro L' _ _ ψ hsurj hker hcomm e J a hsetup
      by_cases hsl : SplitLift lab R I ψ e
      · exact (h.1 L' ψ hsurj hker hcomm e J a hsetup hclass hsl).elim
      · obtain ⟨hlab', hnon, hmodel⟩ :=
          h.2 L' ψ hsurj hker hcomm e J a hsetup hclass hsl
        exact ⟨⟨hlab', hnon⟩, hmodel⟩
    · by_cases he6 : E6Lab lab
      · refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hE6 hConn lab hlab)
        intro L' _ _ ψ hsurj hker hcomm e J a hsetup
        exact (h L' ψ hsurj hker hcomm e J a hsetup he6).elim
      · have hrem : RemainingLab lab := ⟨hsmall, hclass, he6⟩
        refine LargeEvenLabelAll.mono (fun R _ I _ h => ?_) (hRem hConn lab hlab)
        intro L' _ _ ψ hsurj hker hcomm e J a hsetup
        exact (h L' ψ hsurj hker hcomm e J a hsetup hrem).elim

end

end S2MathAs3_1615

end
