module

public import CFSG.LocalAnalysis.StandardType.GGPsiInnerDiagOfMarking
import CFSG.LocalAnalysis.StandardType.GGLieOddCover
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GClsUni
import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUElem
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAut
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Solomon.LocalBalance.AutL3Arith
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
import CFSG.Quasithin.Vol2.KGFactC31RuRef
import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
import CFSG.RankThree.Native.PrimeLines
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec4.Item47
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.PartTwo.Toolkit.M12Local
import CFSG.RankThree.S4Free.SuzukiEight
import CFSG.Sporadic.HeldB.Common
import CFSG.Sporadic.Schreier.J4SNoCompCover
import CFSG.Sporadic.SuzOddCore.GraphData
import CFSG.Sporadic.SuzOddCore.SmallActionData
import Certificates.Certificate14953
import Certificates.Certificate16041
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2108
import Certificates.Certificate2109
import Certificates.Certificate2246
import Certificates.Certificate2274
import Certificates.Certificate2323
import Certificates.Certificate5133
import Certificates.Certificate7233Base
import Certificates.Certificate8166
import Certificates.Certificate8169

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag)
open scoped commutatorElement

private def UnitaryTwoActionProp (X : Type) [Group X] (K B : Subgroup X) : LargeEvenRawCont :=
  fun R _ I _ =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* R,
        ∀ b ∈ B, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ

private theorem largeEvenRecipeUnitary_of_legacy_label
    {lab : LargeEvenLabel} {Q : LargeEvenRawCont} {m : ℕ}
    (hraw : LargeEvenRawDatumLegacy lab Q)
    (htag : markTag lab = .PSU) (hchar : markChar lab = 2)
    (hrank : markRank lab = m) (hdeg : markDeg lab = 1) :
    LargeEvenRecipeUnitary m (2 ^ 1) Q := by
  obtain ⟨tag, r, n⟩ := lab
  have hlabel := CFSG.StandardType.ClNonsplit.unitaryLabel_of_markTag_PSU htag hchar
  have hn1 : n = 1 := by
    exact hlabel.2.symm.trans hdeg
  have hlabel' : tag = .twA ∨ (tag = .twD ∧ r = 3) := by
    simpa only [CFSG.StandardType.GGInndiagUnitaryLabel] using hlabel.1
  rcases hlabel' with hA | ⟨hD, hr3⟩
  · subst hA
    have hr1 : r + 1 = m := by simpa [markRank] using hrank
    rw [← hr1]
    simpa [LargeEvenRawDatumLegacy, hn1] using hraw
  · subst hD
    subst hr3
    have hm4 : m = 4 := by simpa [markRank] using hrank.symm
    rw [hm4]
    simpa [LargeEvenRawDatumLegacy, hn1] using hraw

section Certificates


theorem exists_unitary_two_innerDiag_presentation
    {X : Type} [Group X] [Finite X] {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hBpow : ∀ b ∈ B, b ^ 3 = 1)
    (hKperf : commutator ↥K = ⊤)
    (hoddK : Odd (Nat.card (Subgroup.center ↥K)))
    {m : ℕ} (hm : 4 ≤ m)
    (hLM : LieModel (↥K ⧸ Subgroup.center ↥K) .PSU m 2 1) :
    ∃ φ : (ggU .PSU m 1).K →* X,
      φ.range = K ∧ φ.ker ≤ Subgroup.center (ggU .PSU m 1).K ∧
        ∀ b ∈ B, GGPsiInnerDiag (ggU .PSU m 1).D φ b := by
  classical
  let : Finite ↥K := Subtype.finite
  obtain ⟨-, lab, hlab, hraw0⟩ :=
    CFSG.StandardType.Legacy.largeEvenMarking_of_lieModel_centerQuot hKperf hLM
  obtain ⟨tag, r, n⟩ := lab
  have hrawStd :=
    (CFSG.StandardType.largeEvenRawDatum_legacy ⟨tag, r, n⟩ _).2 hraw0
  obtain ⟨-, -, -, -, -, -, -, htag, hrank, hchar, hdeg⟩ :=
    CFSG.StandardType.largeEvenRawDatum_exists hrawStd
  have hrecipe := largeEvenRecipeUnitary_of_legacy_label hraw0 htag hchar hrank hdeg
  obtain ⟨F, instField, instFinite, hFcard, hQold⟩ := hrecipe
  let : Field F := instField
  let : Finite F := instFinite
  obtain ⟨hs, hna, θ, -, -, -, -⟩ := hQold
  let hData : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.unitaryData_two
      (K := F) (m := 1) (by norm_num) hFcard
  have hQnew : UnitaryTwoActionProp X K B
      (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F (2 ^ 1)))
        (LargeEvenGUSet (Fin m) F (2 ^ 1)))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F (2 ^ 1)))) := by
    dsimp only [UnitaryTwoActionProp]
    refine ⟨hs, hna, θ, ?_⟩
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (K : Set X) := hBN hb
    let α : MulAut ↥K := K.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩
    let β : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) :=
      MulAut.congr θ (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α)
    have hb3 : b ^ 3 = 1 := hBpow b hb
    have hx3 : (⟨b⁻¹, Subgroup.inv_mem _ hbN⟩ :
        Subgroup.normalizer (K : Set X)) ^ 3 = 1 := by
      apply Subtype.ext
      change (b⁻¹) ^ 3 = (1 : X)
      rw [inv_pow, hb3, inv_one]
    have hα3 : α ^ 3 = 1 := by
      change (K.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hbN⟩) ^ 3 = 1
      rw [← map_pow, hx3, map_one]
    have hβ3 : β ^ 3 = 1 := by
      change (MulAut.congr θ
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α)) ^ 3 = 1
      calc
        (MulAut.congr θ
            (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α)) ^ 3
            = MulAut.congr θ
                ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α) ^ 3) :=
              (map_pow (MulAut.congr θ) _ 3).symm
        _ = MulAut.congr θ
              (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K (α ^ 3)) := by
              rw [← map_pow]
        _ = 1 := by
              rw [hα3, map_one, map_one]
    obtain ⟨A, σ, hβeq⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GField.uni_aut_decomp
        (K := F) (m := 1) (d := m) (by norm_num) hFcard (by omega)
        (by
          rintro ⟨h3, -⟩
          omega) β
    have hprod3 : (CFSG.ComponentClassification.Burgoyne.U.uConjAut hData (by omega) A *
        CFSG.ComponentClassification.Burgoyne.U.uFieldAut hData (by omega) σ) ^ 3 = 1 := by
      exact (congrArg
        (fun γ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) F (2 ^ 1))) => γ ^ 3)
        hβeq.symm).trans hβ3
    have hσ3 : σ ^ 3 = 1 :=
      CFSG.ComponentClassification.Burgoyne.U.fieldAut_pow_eq_one hData
        (n := m) (by omega)
        (by
          rintro ⟨h3, -⟩
          omega) hprod3
    have hσ3_apply : ∀ x : F, σ (σ (σ x)) = x := by
      intro x
      have h := congrArg (fun e : F ≃+* F => e x) hσ3
      simpa [pow_succ, pow_two] using h
    have hF4 : Nat.card F = 4 := by simpa using hFcard
    have hσfix : ∀ x : F, σ x = x := fun x =>
      CFSG.LocalAnalysis.GLTheoremA.i4_ringEquiv_eq_id_of_card_four hF4 σ hσ3_apply x
    have hσ1 : σ = 1 := RingEquiv.ext fun x => by simpa using hσfix x
    have hφmem : CFSG.ComponentClassification.Burgoyne.U.uConjAut hData (by omega) A ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) F (2 ^ 1)))
          (LargeEvenGUSet (Fin m) F (2 ^ 1)) := by
      simpa using
        CFSG.LocalAnalysis.GLTheoremA.Y10GField.mem_conjGU
          (K := F) (m := 1) (d := m) (by norm_num) hFcard (by omega) A
    have hindβ : LargeEvenInduces θ
        (fun l l' => (l' : X) = b⁻¹ * l * b) β := by
      intro l l' hll'
      have hαl : α l = l' := by
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
        exact hll'.symm
      change (MulAut.congr θ
        (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α))
        (θ (QuotientGroup.mk l)) = θ (QuotientGroup.mk l')
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      have hstep : CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K α
          ((l : ↥K ⧸ Subgroup.center ↥K)) =
          ((α l : ↥K) : ↥K ⧸ Subgroup.center ↥K) :=
        CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk α l
      rw [hstep, hαl]
    refine ⟨CFSG.ComponentClassification.Burgoyne.U.uConjAut hData (by omega) A,
      hφmem, ?_⟩
    have hβpure : β = CFSG.ComponentClassification.Burgoyne.U.uConjAut hData (by omega) A :=
      hβeq.trans (by rw [hσ1, map_one]; exact mul_one _)
    exact hβpure ▸ hindβ
  have hrecNew : LargeEvenRecipeUnitary m (2 ^ 1) (UnitaryTwoActionProp X K B) := by
    refine ⟨F, instField, instFinite, hFcard, ?_⟩
    exact hQnew
  have hlabel := CFSG.StandardType.ClNonsplit.unitaryLabel_of_markTag_PSU htag hchar
  have hn1 : n = 1 := by
    exact hlabel.2.symm.trans hdeg
  have hlabel' : tag = .twA ∨ (tag = .twD ∧ r = 3) := by
    simpa only [CFSG.StandardType.GGInndiagUnitaryLabel] using hlabel.1
  have hrawT : LargeEvenRawDatumLegacy ⟨tag, r, n⟩ (UnitaryTwoActionProp X K B) := by
    rcases hlabel' with hA | ⟨hD, hr3⟩
    · subst hA
      have hr1 : r + 1 = m := by simpa [markRank] using hrank
      have hrec' : LargeEvenRecipeUnitary (r + 1) (2 ^ n)
          (UnitaryTwoActionProp X K B) := by
        rw [hr1, hn1]
        exact hrecNew
      simpa [LargeEvenRawDatumLegacy] using hrec'
    · subst hD
      subst hr3
      have hm4 : m = 4 := by simpa [markRank] using hrank.symm
      have hrec' : LargeEvenRecipeUnitary 4 (2 ^ n)
          (UnitaryTwoActionProp X K B) := by
        rw [← hm4, hn1]
        exact hrecNew
      simpa [LargeEvenRawDatumLegacy] using hrec'
  have hmark : CFSG.StandardType.LargeEvenMarking ↥K
      (fun _ _ _ I _ θ => ∀ b ∈ B, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ) := by
    refine ⟨hKperf, ⟨tag, r, n⟩, hlab, ?_⟩
    exact hrawT
  have hspos : GGPosTag .PSU := by simp [GGPosTag]
  have hcover := CFSG.StandardType.LieOddCover.ggLieOddCover_holds
  obtain ⟨ψK0, hψ0surj, hψ0ker⟩ :=
    hcover.1 .PSU m 1 hspos hLM.admissible ↥K hKperf hoddK hLM
  let ψK : (ggU .PSU m 1).K →* X := K.subtype.comp ψK0
  have hψrange : ψK.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ0surj, Subgroup.map_top,
      Subgroup.range_subtype]
  have hψker : ψK.ker ≤ Subgroup.center (ggU .PSU m 1).K := by
    rw [MonoidHom.ker_comp_of_injective ψK0 K.subtype K.subtype_injective]
    exact hψ0ker
  have hrankD : 2 ≤ (ggU .PSU m 1).D.rank := by
    rw [CFSG.StandardType.ggU_PSU_rank m 1 (by norm_num)]
    omega
  have hpres : GGPresentsG0 K (ggU .PSU m 1).D .PSU m 1 ψK :=
    ⟨⟨hLM.admissible, hrankD⟩, ⟨hψrange, hψker⟩, hKperf, hLM⟩
  refine ⟨ψK, hψrange, hψker, ?_⟩
  exact CFSG.StandardType.ggPsiInnerDiag_of_marking hpres hmark hBN

end Certificates

end CFSG.StandardType.RCKC1
