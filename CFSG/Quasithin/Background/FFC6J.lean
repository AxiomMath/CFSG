module

public import CFSG.Quasithin.Background.FFC6B
public import CFSG.Quasithin.Background.FFC6G
public import CFSG.Quasithin.Background.FFC6H
public import CFSG.Quasithin.Background.FFC6I
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.FFC2Ident

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.B5
open scoped commutatorElement

namespace B59

section CaseA

variable {M : Type} [CommGroup M] [Finite M]

theorem caseA_M
    (hI : B58Inputs) (hB42 : AsB42) (hM : ∀ v : M, v ^ 2 = 1) {X K Ab : Subgroup (MulAut M)}
    (h : B51Hyp X K) (hmin : IsFFStarMin X Ab) (hXK : X = K) (hno : ¬ ThreeRank2 ↥K)
    (hirr : commV K ∈ IrrPlus K ⊤)
    (hnat : ∃ n, BinaryNaturalSL K (commV K) (fixV K ⊓ commV K) 2 n) :
    1 ≤ rAV Ab ∧ IsSylowTwoOf Ab K := by
  have hAbX : Ab ≤ X := hmin.1.1
  have hAbK : Ab ≤ K := hXK ▸ hAbX
  have hA2 : IsPGroup 2 Ab := hmin.1.2.2.1.isPGroup
  obtain ⟨T, hT, hAbT⟩ := exists_isSylowTwoOf_ge hAbX hA2
  obtain ⟨C, hC⟩ : ∃ C : Subgroup M, C = fixV K ⊓ commV K := ⟨_, rfl⟩
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hM h hirr hT hC
  obtain ⟨B, hBA, hB, hconcl⟩ := b42_offender hB42 hM h hirr hT hmin.1 hAbT hC
  have hb4 := b4Hyp_section' hM h hirr hT.1 hT.2.1 hC
  have hKT : K ⊔ T = K := sup_eq_left.2 (hXK ▸ hT.1)
  have hKL : K ≤ X := le_G h
  have hLU : K ≤ stabSub (commV K) := hKL.trans hGU
  have hLC : K ≤ stabSub C := hKL.trans hGC
  have hnoL' : ¬ ThreeRank2 ↥(autSec K (commV K) C) := fun h' =>
    hno (h'.of_mulEquiv (secEquiv K hLU hLC hfL).symm)
  have h23 : (∃ n, BinaryNaturalSL (autSec K (commV K) C) (⊤ : Subgroup (Sec (commV K) C)) ⊥ 3 n) →
      False := by
    rintro ⟨n, hn3⟩
    have h3 := binaryNaturalSL_of_autSec hUC hLU hLC hfL hn3
    rw [hC] at h3
    obtain ⟨n₂, hn₂⟩ := hnat
    exact false_of_sl2_sl3 hn₂ h3
  rw [hKT] at hB hconcl hb4
  have hcase1 := b42_case1_of_sl2 hI (asB42Ident_of_b42 hB42) (sq_eq_one_sec hM _ _) hb4 hB rfl
    hnoL' h23 hconcl
  have hq1 : qOf (autSec K (commV K) C) = ((1 : ℚ) : WithTop ℚ) := hcase1.2.2.2
  have hS : IsSylowTwoOf B (autSec K (commV K) C) := hcase1.2.2.1
  have hMW : K ⊔ Ab ≤ stabSub (commV K) := sup_le hLU (hAbX.trans hGU)
  have hMC : K ⊔ Ab ≤ stabSub C := sup_le hLC (hAbX.trans hGC)
  have hnc : ¬ commSub (commV K) K ≤ C := by
    obtain ⟨-, hcomm, -, -⟩ := irr_data hirr
    rw [hcomm]
    intro hle
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  have c : SecCtx X K Ab (commV K) C := ⟨hAbX, hmin.1.2.2.1, hmin.1.2.1, hUC, hMW, hMC, hnc⟩
  have hquad : IsQuadratic Ab := B1_4_3 hM hmin
  have h1 := qOf_secX_le h c hquad
  rw [sup_eq_left.2 hAbK, hq1] at h1
  have hr1 : (1 : ℚ) ≤ rAV (autSec Ab (commV K) C) := by exact_mod_cast h1
  have hfA : Ab ⊓ centSec (commV K) C = ⊥ := sec_A_inf_centSec h c
  have hr : 1 ≤ rAV Ab :=
    hr1.trans (rAV_autSec_le hM hUC (hAbX.trans hGU) (hAbX.trans hGC) hfA hmin.1.2.1 hmin.1.2.2.1)
  exact ⟨hr, sylow_of_autSec hAbK hLU hLC hfL hfA hA2 hBA hS⟩

end CaseA

end B59

end FFC

end CFSG.Quasithin
