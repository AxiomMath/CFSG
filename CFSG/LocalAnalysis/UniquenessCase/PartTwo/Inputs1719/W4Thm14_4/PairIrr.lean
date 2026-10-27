module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MatColumn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.MatRow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.PairRestrict
public import CFSG.Quasithin.Background.F918Z5B1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Nat
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

theorem kA5PairIrr_holds : KA5PairIrr := by
  intro W _ _ hW L₁ L₂ X I hX hcomm ha₁ ha₂ hI h₁ h₂
  classical
  obtain ⟨hXI, hfaith, hD, hE, hsup, hcommAut, hHas⟩ :=
    exists_matModel_of_pair_irr hW hX hcomm ha₁ ha₂ hI h₁ h₂
  obtain ⟨F, hF, hFin, hChar, d, r, β, ρ, σ, -, hr, hM⟩ := hHas
  letI : Field F := hF
  letI : Finite F := hFin
  letI : CharP F 2 := hChar
  have hVI : ∀ v : ↥I, v ^ 2 = 1 := fun v => Subtype.ext (by
    have h := hW (v : W)
    simpa using h)
  have hcol := matModel_column_cases (V := ↥I) hVI hM hD ⟨0, hr⟩
  have hrow := matModel_row_cases (V := ↥I) hVI hM hE
  have hcard := card_eq_card_pow_of_matEquiv (V := ↥I) (F := F) (d := d) (r := r) β
  rcases hcol with ⟨hF2, hd4, -⟩ | ⟨hF4, hd2⟩
  · have hr4 := hrow.1 hF2
    right
    have hcardI : Nat.card ↥I = 2 ^ 16 := by
      rw [hcard, hF2, hd4, hr4]
    show padicValNat 2 (Nat.card ↥I) = 16
    rw [hcardI, padicValNat.prime_pow]
  · rcases hrow.2 hF4 with hr2 | hr4
    · have hcardI : Nat.card ↥I = 2 ^ 8 := by
        rw [hcard, hF4, hd2, hr2]
        norm_num
      have hrk8 : rk ↥I = 8 := by
        show padicValNat 2 (Nat.card ↥I) = 8
        rw [hcardI, padicValNat.prime_pow]
      refine Or.inl ⟨hrk8, ?_⟩
      subst d
      subst r
      have hperfD : Group.IsPerfect ↥(autSub L₁ I) := isPerfect_of_isAlt_five hD
      have hperfE : Group.IsPerfect ↥(autSub L₂ I) := isPerfect_of_isAlt_five hE
      obtain ⟨e₁⟩ := hD
      obtain ⟨e₂⟩ := hE
      have hPSL : IsPSL 2 2 2 ↥(autSub L₁ I) :=
        CFSG.Quasithin.H13.OddSyl.isPSL_two_two_two_of_alt_five e₁
      have hXD : Nonempty (↥(autSub L₁ I) ≃* ↥(autSub L₂ I)) := ⟨e₁.trans e₂.symm⟩
      obtain ⟨hcardF, hρ, hσ⟩ :=
        CFSG.Quasithin.SqModel.matModel_two_equiv hM hperfD hperfE hPSL hXD
      have hOmega : Omega4PlusModule (autSub L₁ I ⊔ autSub L₂ I) 2 :=
        omega4PlusModule_of_matModel hcardF hcommAut hM hρ hσ
      have hOmega' : Omega4PlusModule (autSub X I) 2 := by
        rw [hsup]
        exact hOmega
      obtain ⟨K, hK, hKfin, hKcard, hreal⟩ := hOmega'
      letI : Field K := hK
      letI : Finite K := hKfin
      have hTensor : NatTensor X I ⊥ 2 2 :=
        ⟨K, inferInstance, inferInstance, hKcard,
          Thm14_5.realizes_of_autSub hXI hfaith hreal⟩
      exact natOmegaPlus_of_natTensor (by norm_num) hTensor
    · right
      have hcardI : Nat.card ↥I = 2 ^ 16 := by
        rw [hcard, hF4, hd2, hr4]
        norm_num
      show padicValNat 2 (Nat.card ↥I) = 16
      rw [hcardI, padicValNat.prime_pow]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
