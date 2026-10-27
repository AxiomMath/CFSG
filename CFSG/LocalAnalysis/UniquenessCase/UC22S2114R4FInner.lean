module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4FReduction
public import CFSG.LieType.BorelExponent.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
import CFSG.LieType.BorelExponent.Linear
import CFSG.LieType.BorelExponent.Unitary
import CFSG.LieType.BorelExponent.Symplectic
import CFSG.LieType.BorelExponent.OrthogonalPlus
import CFSG.LieType.BorelExponent.OrthogonalMinus
import CFSG.LieType.BorelExponent.Chevalley
import CFSG.LieType.BorelExponent.TwistedE6
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveStrong
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114SolvOver
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dTitsModels
import CFSG.Assembly.E6FourLabelArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LieType.BorelExponent
open CFSG.QuasithinUnique (IsSylowTwoOf)


theorem uc22s2114r4f_dvd_of_inner_borel {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} {m f : ℕ} (hadm : StatedLieAdmissible t m 2 f)
    (hmodel : LieModel X t m 2 f) (hl : 4 ≤ PartTwo.S17.CS17LieRank t m)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) {α : MulAut X} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hα1 : α ≠ 1) (hαr : α ^ r = 1)
    (hαU : U.map α.toMonoidHom = U)
    (hin : α ∈ (MulAut.conj : X →* MulAut X).range) :
    r ∣ 2 ^ (2 * f) - 1 := by
  have : Fact r.Prime := ⟨hr⟩
  have hB : HasBorelExponent X (lieBorelExponent t f) := by
    cases t with
    | PSL => exact borelExponentAt_PSL X m f hadm hmodel
    | PSU => exact borelExponentAt_PSU X m f hadm hmodel
    | PSp => exact borelExponentAt_PSp X m f hadm hmodel
    | POmegaOdd => exact absurd rfl hadm.2.2.2
    | POmegaPlus => exact borelExponentAt_POmegaPlus X m f hadm hmodel
    | POmegaMinus => exact borelExponentAt_POmegaMinus X m f hadm hmodel
    | F4 => exact borelExponentAt_F4 X m f hadm hmodel
    | E6 => exact borelExponentAt_E6 X m f hadm hmodel
    | E7 => exact borelExponentAt_E7 X m f hadm hmodel
    | E8 => exact borelExponentAt_E8 X m f hadm hmodel
    | twistedE6 => exact borelExponentAt_twistedE6 X m f hadm hmodel
    | G2 => simp [PartTwo.S17.CS17LieRank] at hl
    | trialityD4 => simp [PartTwo.S17.CS17LieRank] at hl
    | twistedB2 => simp [PartTwo.S17.CS17LieRank] at hl
    | twistedG2 => simp [PartTwo.S17.CS17LieRank] at hl
    | twistedF4 => simp [PartTwo.S17.CS17LieRank] at hl
    | Tits => simp [PartTwo.S17.CS17LieRank] at hl
  obtain ⟨x, rfl⟩ := hin
  have hxU : x ∈ normalizer (U : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hαU
  have hd := hB.dvd_of_orderOf_conj hU hr hr2 (orderOf_eq_prime hαr hα1) hxU
  have hf : 2 ^ f - 1 ∣ 2 ^ (2 * f) - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 ⟨2, by omega⟩
  cases t <;> simp only [lieBorelExponent] at hd
  all_goals first | exact hd | exact hd.trans hf |
    simp [PartTwo.S17.CS17LieRank] at hl

theorem s21_14R4FInner_of_rank_tables {G : Type} [Group G] [Finite G]
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    (hKC : PartTwo.Inputs1719.K_CartanRank) {D : Data G} {Ch : Choice2011 G} :
    S21_14R4FInner D Ch := by
  intro hSg _ _ hH c L hL _ _ l f hl hlr _ hBL hfaith hcase _ b hbB hbL r hr hr5 hbr hrn _ hin
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hb1 : inducedBarInfAutHom L ⟨b, hbL⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith hbB h1
    rw [h, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 :=
    rhoInf_pow_eq_one L hbL (by rw [← hbr]; exact pow_orderOf_eq_one b)
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hfinish : ∀ (t : StatedLieTag) (m : ℕ), StatedLieAdmissible t m 2 f →
      LieModel (BarInf L) t m 2 f → 4 ≤ PartTwo.S17.CS17LieRank t m →
      7 ≤ r → r ∣ 2 ^ f - 1 → False := by
    intro t m hadm hmodel hrank hr7 hrd
    exact uc22s2114_not_mem_sig hSg hns hH c hr hrn
      (hSg.four_mem r hr hr2
        ((uc22s2114_four_le_pRank_of_lieRank_four hT hKC hL hadm hmodel hrank hr hr7 hrd).trans
          (CFSG.SectionRank.pRank_mono hr.one_lt hL.1.le)))
  rcases hcase with hodd | ⟨hpsl, hfo, _⟩
  · obtain ⟨t, m, hadm, hmodel, rfl⟩ := hlr
    obtain ⟨U, hU, hθU⟩ := uc22s2114_exists_map_eq
      (uc22p2214_isSylowOf_inf D.sylowM hL.1) hbL (c.B0_le_normalizer hodd hbB)
    have hd := uc22s2114r4f_dvd_of_inner_borel hadm hmodel hl hU hr hr2 hb1 hθr hθU hin
    have hrd : r ∣ 2 ^ f - 1 :=
      (uc22s2114_dvd_two_pow_gcd_sub_one (d := f) (f := 2) hodd ⟨1, rfl⟩ hrn
        (by rwa [mul_comm])).trans
          (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right c.n f))
    have hr7 : 7 ≤ r := P2251h.seven_le_of_dvd_two_pow_sub_one (by omega)
      (uc22p20v_not_three_dvd_sub_one hodd) hr hrn
    exact hfinish t m hadm hmodel hl hr7 hrd
  · obtain ⟨U, hU, hθU⟩ := uc22s2114_exists_map_eq_of_solvOver c hL
      (fun U hU => S15.K21dTitsProof.solvOver_of_lieModel (by omega) (Or.inl rfl) hpsl hU)
      hbB hbL
    obtain ⟨x, hx⟩ := hin
    have hxU : x ∈ normalizer (U : Set (BarInf L)) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.2
      rwa [hx]
    have hrd : r ∣ 2 ^ f - 1 :=
      (borelExponentAt_PSL (BarInf L) 5 f (LieModel.admissible hpsl) hpsl).dvd_of_orderOf_conj
        hU hr hr2 (by rw [hx]; exact orderOf_eq_prime hθr hb1) hxU
    have hr5ne : r ≠ 5 := by
      rintro rfl
      obtain ⟨k, hk⟩ := CFSG.Assembly.e6Four_five_dvd_two_pow_sub_one.1 hrd
      obtain ⟨j, hj⟩ := hfo
      omega
    have hr6ne : r ≠ 6 := by rintro rfl; norm_num at hr
    exact hfinish .PSL 5 (LieModel.admissible hpsl) hpsl (by decide) (by omega) hrd

end CFSG.LocalAnalysis.UniquenessCase.UC22
