module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePZPSU
public import CFSG.LocalAnalysis.StandardType.GGSecFivePZExc
public import CFSG.LocalAnalysis.StandardType.GGSecFivePZClassical
public import CFSG.LocalAnalysis.StandardType.GGSecFivePZD4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

theorem ggSecFivePZKnownGroupInput_holds : GGSecFivePZKnownGroupInput := by
  refine ggSecFivePZKnownGroupInput_of_psiInnerDiag
    fun G _ _ B Bs L D J x m hm h3 hcfg hNT hPZ t n f ψ hpres => ?_
  have h0 : (ggU t n f).D.rank = 0 → GGPsiInnerDiag (ggU t n f).D ψ x := fun hr => by
    have := hpres.1.2
    omega
  cases t
  · exact ggPsiInnerDiag_pz_classical hm h3 hcfg hNT hPZ ψ (.inl rfl) hpres
  · exact PZPSU.ggPsiInnerDiag_x_pz_PSU hm h3 hcfg hNT hPZ ψ hpres
  · exact ggPsiInnerDiag_pz_classical hm h3 hcfg hNT hPZ ψ (.inr (.inl rfl)) hpres
  · exact absurd rfl hpres.1.1.2.2.2
  · by_cases hn : n = 4
    · subst hn
      exact ggPsiInnerDiag_pz_D4 hm h3 hcfg hNT hPZ ψ hpres
    · exact ggPsiInnerDiag_pz_classical hm h3 hcfg hNT hPZ ψ (.inr (.inr (.inr ⟨rfl, hn⟩)))
        hpres
  · exact ggPsiInnerDiag_pz_classical hm h3 hcfg hNT hPZ ψ (.inr (.inr (.inl rfl))) hpres
  · exact h0 rfl
  · exact ggPsiInnerDiag_pz_exceptional hm hcfg hPZ (.inl rfl) hpres
  · exact ggPsiInnerDiag_pz_exceptional hm hcfg hPZ (.inr (.inl rfl)) hpres
  · exact ggPsiInnerDiag_pz_exceptional hm hcfg hPZ (.inr (.inr (.inl rfl))) hpres
  · exact ggPsiInnerDiag_pz_exceptional hm hcfg hPZ (.inr (.inr (.inr (.inl rfl)))) hpres
  · exact ggPsiInnerDiag_pz_exceptional hm hcfg hPZ (.inr (.inr (.inr (.inr rfl)))) hpres
  · exact h0 rfl
  · exact h0 rfl
  · exact h0 rfl
  · exact h0 rfl
  · exact h0 rfl

theorem ggSecFiveCompatRestWResNJoinInput_of_suppliers
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hRk1 : GGSecFiveRk1PhanInput)
    (hSmall : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ¬ GGSecFiveTier1Region p B Bs x L D J → ¬ GGSplitLie p L →
        ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
          GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e →
          (∃ (n : ℕ) (e' : Fin n ≃ ι), (n = 3 ∨ n = 4) ∧ M = (CoxeterMatrix.A n).reindex e') →
            False)
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) (hFSE : GGSecFiveE6QTwoFS81Input)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hField : GGSecFiveQTwoFieldTwoSelectedInput)
    (hB : GGSecFiveCompatJoinResNAt GGIsWeylMatrixB)
    (hD : GGSecFiveCompatJoinResNAt GGIsWeylMatrixD)
    (hE : GGSecFiveCompatJoinResNAt GGIsWeylMatrixE)
    (hF : GGSecFiveCompatJoinResNAt GGIsWeylMatrixF4) :
    GGSecFiveCompatRestWResNJoinInput :=
  ggSecFiveCompatRestWResNJoinInput_of_cells hTBF hSmall
    (ggSecFiveCompatQTwoCellResNInput_of_internal
      (ggSecFiveQTwoInternalInput_of_tbTor hTBF hWI hW hLift hFSE)
      (ggSecFiveQTwoKnownSelectedInput_of_fieldTwo hField))
    (ggSecFiveCompatOrderSixResNInput_of_qTwo hRk1
      (ggSecFiveCompatOrderSixQTwoResNInput_of_AD hTBF hWI hField
        (ggSecFiveCompatOrderSixQTwoADResNInput_of_innerDiag
          (ggSecFiveOrderSixADInnerDiagInput_of_modularA hTBF hWI
            (ggSecFiveOrderSixModularAInput_of_pz hTBF hWI hW hLift
              (ggSecFivePZTwA5Input_of_frame hTBF hWI hLB hPJ)
              ggSecFivePZKnownGroupInput_holds)) hField)))
    hB hD hE hF

end CFSG.StandardType
