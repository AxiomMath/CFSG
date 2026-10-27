module

public import CFSG.Quasithin.Background.SimsE214Easy
public import CFSG.Quasithin.Background.SimsE214Two
public import CFSG.Quasithin.Background.SimsE214NatThree
public import CFSG.Quasithin.Background.SimsE214NatFive
public import CFSG.Quasithin.Background.SimsE214Four
public import CFSG.Quasithin.Background.SimsE214VStar
public import CFSG.Quasithin.Background.SimsE214Seven
public import CFSG.Quasithin.Background.SimsE214Ten
public import CFSG.Quasithin.Background.SimsE214Eleven
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftSaturate
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTwist
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImages
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallerRecognitionDischarge
public import CFSG.Quasithin.Background.B3Facts
public import CFSG.Quasithin.Background.B3FourConj
public import CFSG.Quasithin.Background.HFL3Four
public import CFSG.Quasithin.Background.HSecQuot
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.SmithB42Sp4Real
public import CFSG.Quasithin.EmptyFaithful.S152N11
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.Quasithin.H13.QRCBenderPairModel
public import CFSG.Quasithin.SteinbergCCPrimeWitness
public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseS
public import CFSG.Quasithin.Vol2.Ch11SecBTCIso
public import CFSG.Quasithin.Vol2.Ch11SecOE7B
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem3
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch3E213MP6BC
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD
public import CFSG.Quasithin.Vol2.Ch3E215MSp4A
public import CFSG.Quasithin.Vol2.Ch7NotFFS7
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210
public import CFSG.Quasithin.Vol2.Ch8Sec2L825A
public import CFSG.Quasithin.Vol2.Ch8Sec2L825J
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.Quasithin.SimsE2

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem e214
    (hNine : E214NineSz) :
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ) (h : E2.Hyp28 H T M V), CharTwo H →
    IsTISetIn V M →
    ∀ (I : Subgroup Γ) (g : Γ), IsInIHTV H T M V I → g ∈ I → I = V ⊔ conjSubgroup V g →
      V ⊓ conjSubgroup V g ≠ ⊥ →
      ∀ (MI TI JI B A P Z : Subgroup Γ) (k : ℕ),
        MI = M ⊓ I → TI = T ⊓ I → JI = kerIn MI I → B = V ⊓ pCoreOf 2 I →
        A = conjSubgroup V g ⊓ pCoreOf 2 I → P = A ⊔ B → Z = V ⊓ conjSubgroup V g →
        E1.nParam (⊤ : Subgroup (E2.StarQuot MI I)) = (k : ℕ∞) →
        MI = I ⊓ Subgroup.normalizer (V : Set Γ) ∧
        ((P = JI ∧ E2.star MI I V = centerOf (E2.star MI I TI)) ∨
          (∃ (_ : (P.subgroupOf I).Normal), CFSG.IsQuasisimple (↥I ⧸ P.subgroupOf I) ∧
            IsSz 3 (E2.StarQuot MI I) ∧
            (∀ x : Γ, x ∈ JI ↔ x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ P) ∧
            V ⊔ P = ⁅Subgroup.closure {t : Γ | t ∈ TI ∧ t ^ 2 ∈ P}, MI⁆ ⊔ P ∧
            E2.IsBorelIn ⊤ (E2.star MI I MI) ∧ E2.star MI I V = centerOf (E2.star MI I TI)) ∨
          (∃ (_ : (P.subgroupOf I).Normal),
            Nonempty (↥I ⧸ P.subgroupOf I ≃* Equiv.Perm (Fin 6) × Multiplicative (ZMod 2)) ∧
            ∀ x : Γ, x ∈ JI ↔ x ∈ I ∧ ∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ P)) ∧
        ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
            Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) →
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
            ∃ r : ℕ, IsSumOfNaturalSections r I P Z JI (CFSG.Open.StatedSL 2 F)) ∧
        ((IsSz k (E2.StarQuot MI I) ∨ (1 ≤ k ∧ IsSp4Full k (E2.StarQuot MI I))) →
          ∀ Y₁ Y₂ : Subgroup Γ, Z ≤ Y₂ → Y₂ < Y₁ → Y₁ ≤ P → I ≤ Subgroup.normalizer (Y₁ : Set Γ) →
            I ≤ Subgroup.normalizer (Y₂ : Set Γ) →
            (∀ Y : Subgroup Γ, Y₂ ≤ Y → Y ≤ Y₁ → I ≤ Subgroup.normalizer (Y : Set Γ) →
              Y = Y₂ ∨ Y = Y₁) →
            4 * k ≤ E3.mQuot Y₁ Y₂) ∧
        ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
            (IsNaturalSection I P Z JI (CFSG.Open.StatedSL 2 F) ∨
              IsNaturalSection I P Z JI (CFSG.Open.StatedSp 2 F))) →
          (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧ qOf (autI h.elem I) ≤ ((1 : ℚ) : WithTop ℚ)) ∧
        (autI h.elem A ≤ autI h.elem I ∧
          autI h.elem I ≤ Subgroup.normalizer (autI h.elem A : Set (MulAut (IntMod V h.elem)))) ∧
        (rk ↥(autI h.elem A) ≤ 2 * k → ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
          ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
              Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) ∨
            IsSz k (E2.StarQuot MI I) ∨ Nonempty (E2.StarQuot MI I ≃* DihedralGroup 5)) ∧
          rk ↥(autI h.elem A) = 2 * k ∧ E3.mQuot V Z = 3 * k ∧
          ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
              Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F)) ∧
              IsSumOfNaturalSections 2 I P Z JI (CFSG.Open.StatedSL 2 F)) ∨
            (∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ k = 2 * a + 1 ∧
              Nat.card F = 2 ^ k ∧ IsSz k (E2.StarQuot MI I) ∧
              IsNaturalSection I P Z JI (CFSG.Blueprint.suzukiGroup a F)) ∨
            (∃ (F : Type) (_ : Field F) (_ : Finite F) (S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)),
              Nat.card F = 4 ∧ S ≤ CFSG.Open.StatedSL 2 F ∧ Nonempty (↥S ≃* DihedralGroup 5) ∧
              Nonempty (E2.StarQuot MI I ≃* DihedralGroup 5) ∧ IsNaturalSection I P Z JI S))) ∧
        (k = 2 → rk ↥(autI h.elem A) ≤ 6 → ((1 : ℚ) : WithTop ℚ) < qOf (autI h.elem I) →
          IsPSL 2 2 2 (E2.StarQuot MI I) ∧
          ∃ s : ℕ, (s = 2 ∨ s = 3) ∧ rk ↥(autI h.elem A) = 2 * s ∧ E3.mQuot V Z = 2 * (s + 1)) ∧
        (((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
              Nonempty (E2.StarQuot MI I ≃* ↥(CFSG.Open.StatedSL 2 F))) ∨ IsSz k (E2.StarQuot MI I)) →
          1 < k → ∀ X : Subgroup Γ, X ≤ MI → Nat.card X = 2 ^ k - 1 →
            Z = V ⊓ Subgroup.centralizer (X : Set Γ)) ∧
        (∀ p : ℕ, p.Prime → p ≠ 2 → Nonempty (E2.StarQuot MI I ≃* DihedralGroup p) →
          ∃ (r : ℕ) (W : Fin r → Subgroup Γ),
            (∀ i, Z ≤ W i ∧ W i ≤ P ∧ IsFaithfulIrredSection I (W i) Z JI ∧
              E3.mQuot (W i) Z = 2 * E2.dParamPrime p) ∧
            (⨆ i, W i) = P ∧ ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z) ∧
        ⁅V, P⁆ ⊔ Z = B ⊔ Z := by
  intro Γ _ _ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk
  have h4 := e214_four Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk
    (e214_vstar_sp4 Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk)
  exact ⟨e214_one Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    e214_two Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    e214_three H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    h4,
    e214_five H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    e214_six Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    e214_seven Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk h4,
    e214_eight Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk h4,
    e214_nine hNine Γ H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    e214_ten H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk,
    e214_eleven H T M V h hc hTI I g hI hg hIV hZ MI TI JI B A P Z k hMI hTI' hJI hB hA hP hZ' hk⟩

end CFSG.Quasithin.SimsE2
