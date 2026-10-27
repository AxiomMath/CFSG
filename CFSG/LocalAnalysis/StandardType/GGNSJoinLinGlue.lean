module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourParts
public import CFSG.LocalAnalysis.StandardType.GGNSJoinLinTwo
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
import CFSG.LocalAnalysis.StandardType.GGNSJoinLinGlueAux
import CFSG.LocalAnalysis.StandardType.GGNSJoinLinGlueAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

@[expose] def NSLinTwoMatrixInput : Prop :=
  GGLabelRigidInput → ∀ {N : ℕ}, 6 ≤ N → ∀ {F : Type} [Field F] [Finite F] [CharP F 2],
    Nat.card F = 2 → ∀ {g : GL (Fin N) F}, g ^ 3 = 1 →
      ∀ {J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))},
        CFSG.Open.IsComponentOf J₀ (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) →
          ∀ {labJ : LargeEvenLabel}, LargeEvenInLambda2 labJ →
            GGHasLabel labJ (↥J₀ ⧸ Subgroup.center ↥J₀) → labJ.n ≤ 2

theorem nsNbrLinearInput_of_linTwo
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hKn : GGTCJEnnolaKnown) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hLin : NSLinTwoMatrixInput) : NSNbrLinearInput := by
  unfold NSLinTwoMatrixInput at hLin
  intro G _ _ B Bs x L D J 𝒦 hreg hns ι M e hpres hle3 hQ4 y K hnb ℓ hℓ hhasK
  have hcfg : GGConfig 3 B Bs x L D J := hreg.1.1
  have hInn : GGInnerDiagAll 3 B Bs x L D J := hreg.1.2.2.1
  have hLrow : GGInnerDiagOnLabel ggRowP_Ennola 3 Bs L :=
    ggX_ennola_of_nonSplit hreg hpres hle3 (Or.inl rfl) hns
  obtain ⟨labJ, hΛJ, hhasJ, h3⟩ := nsLG_common_label_J hRig hTCJ hKn hcfg hnb hLrow hQ4
  have h2 : labJ.n ≤ 2 :=
    nsLG_linear_bound hLin hRig hL hP hcfg hInn hnb hℓ hhasK hΛJ hhasJ
  omega

theorem nsNbrLinearInput_holds
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hKn : GGTCJEnnolaKnown) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) : NSNbrLinearInput :=
  nsNbrLinearInput_of_linTwo hRig hTCJ hKn hL hP (by
    intro hRig' N hN F _ _ _ hF g hg J₀ hJ₀ labJ hΛ hhas
    exact nsLinTwo_component_label hRig' hN hF hg hJ₀ hΛ hhas)

end NSJoin

end CFSG.StandardType

end
