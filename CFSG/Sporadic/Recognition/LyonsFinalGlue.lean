
module

public import CFSG.Sporadic.Recognition.LyonsAmalgamCertBase

public import CFSG.Sporadic.Recognition.LyonsAmalgamGlueMain
public import CFSG.Sporadic.Recognition.LyonsModelCert
public import Certificates.Certificate6113
public import CFSG.Sporadic.Recognition.LyonsModelBorel

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

section Stage

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem LyData.exists_stage_txW_of_certificates' (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∃ φ : ↥(NormX (x₁ : G)) ≃* Ly0.B0,
      ∃ (hφY : ((NN (x₁ : G) (x₂ : G)).subgroupOf (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Y0)
        (_hφT : ((normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)).subgroupOf
          (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Tx)
        (_hφK : ((NN (x₁ : G) (x₂ : G) ⊓ normalizer (zpowers (x₃ : G) : Set G)).subgroupOf
          (NormX (x₁ : G))).map φ.toMonoidHom = Ly0.Txy)
        (M : ModelGlue) (_hM : ∀ i : Fin 4, M.txW i = Glue.txWords.getD i.val [])
        (k : G), IsSwapY0 (x₁ : G) (x₂ : G) (x₃ : G) (borelPhiY φ hφY M.ιY) k := by
  have hM : Ly0.ModelChecks := Ly0.modelChecks_of_certificate
  obtain ⟨φ, h1, hφY, hφT, hφK⟩ := Ly0.exists_mulEquiv_borel hM D S
  have hcY : Nat.card Ly0.Y0 ≤ 349920 := (Ly0.card_Y0_of_borel hM D S).le
  have hcT : Nat.card Ly0.Tx ≤ 7776 := (D.card_Tx_of_borel S φ hφT).le
  have hcK : Nat.card Ly0.Txy ≤ 3888 := (D.card_Txy_of_borel S φ hφK).le
  obtain ⟨M, hMtx⟩ := Certificates.certificate6113 hcY hcT hcK
  obtain ⟨k, hk, -⟩ := D.exists_swap_and_mulEquiv_Tr0_of_borel S yOK_of_certificate trCheck_eq_true
    tauOK_eq_true φ hφY hφT hφK M
  exact ⟨φ, hφY, hφT, hφK, M, hMtx, k, hk⟩

end Stage

end CFSG.Sporadic.Recognition.LyonsSims
