module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112L2Meet
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112L2Act
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rg
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xe
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveStrong
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightCaseTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112e3_le_normalizer_inf_of_odd {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hodd : Odd c.n) {L : Subgroup G} (hBL : c.B ≤ normalizer (L : Set G)) :
    c.B ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
  (le_inf (c.hle.trans (c.B0_le_normalizer hodd)) hBL).trans inf_normalizer_le_normalizer_inf

theorem uc22s2112e3_inf_eq_bot {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h847 : R847E3Thin D) (hH : H1930 D) (c : Ctx21 D Ch) (hev : Even c.n) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hLN : (L.subgroupOf D.M).Normal) (hthin : F08.Thin8 L) :
    c.B ⊓ L = ⊥ := by
  by_contra hne
  have hodd : Odd (Nat.card ↥(c.B ⊓ L)) :=
    Odd.of_dvd_nat (uc22s13xe_odd_card_B c) (Subgroup.card_dvd_of_le inf_le_left)
  have h1 : Nat.card ↥(c.B ⊓ L) ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq _ h)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd h1
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hrd
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  have hxBL := Subgroup.mem_inf.1 x.2
  have hXB : Subgroup.zpowers (x : G) ≤ c.B := Subgroup.zpowers_le.2 hxBL.1
  have hXL : Subgroup.zpowers (x : G) ≤ L := Subgroup.zpowers_le.2 hxBL.2
  have hXcard : Nat.card ↥(Subgroup.zpowers (x : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  obtain ⟨q, hq⟩ := hSg.nonempty
  rcases h847 L hL hLN hthin _ hXL r hr hr2 hXcard q hq with hN | ⟨rfl, -⟩
  · exact s21_2 D Ch hH c _ hXB hN
  · exact Nat.not_odd_iff_even.2 hev
      (u4p_odd_n D Ch hH c (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hq))

theorem uc22s2112e3_commutator_le {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLp : IsL2Odd (Bar2 L) p) (hBN : c.B ≤ normalizer (L : Set G))
    (hBS : c.B ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G)) :
    ⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp (uc22p22r_fo_sylow_inf D.sylowM hL.1)
  have hOK : CFSG.Quasithin.opResidual 3 c.B ≤
      (UC6S846.rhoL L).ker.map (normalizer (L : Set G)).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hx, hx3⟩
    exact ⟨⟨x, hBN hx⟩, MonoidHom.mem_ker.2 (uc22s2112_rhoL_eq_one hSyl hp hp2 hLp hBN hBS
      c.hB.2.1 (uc22s13xe_odd_card_B c) hx hx3), rfl⟩
  rw [Subgroup.commutator_le]
  intro x hx l hl
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 (hOK hx)
  have h := (UC6S846.rhoL_fix_iff L n ⟨l, hl⟩).1 (by rw [MonoidHom.mem_ker.1 hn]; rfl)
  simpa [commutatorElement_def] using h

theorem s21_12L2_of_r847E3Thin {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3Thin D) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLp : IsL2Odd (Bar2 L) p) (hcase : (L.subgroupOf D.M).Normal ∨ Odd c.n) :
    ⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L := by
  have hBN : c.B ≤ normalizer (L : Set G) := h5 hH c L hL
  refine uc22s2112e3_commutator_le c hL hp hp2 hLp hBN ?_
  rcases Nat.even_or_odd c.n with hev | hodd
  · exact uc22s2112_le_normalizer_inf c hBN (uc22s2112e3_inf_eq_bot hSg h847 hH c hev hL
      (hcase.resolve_right (Nat.not_odd_iff_even.2 hev)) (thin8_of_isL2Odd_bar2 hp hp2 hLp))
  · exact uc22s2112e3_le_normalizer_inf_of_odd c hodd hBN

@[expose] def S21_12R3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsChev (BarInf L) p →
      ((∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L) ∧
      (¬ (L.subgroupOf D.M).Normal → Even c.n → IsL2Odd (Bar2 L) p →
        ⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L)

section Certified

set_option linter.unusedSectionVars false

theorem s21_12_of_s21_12R3 {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch)
    (hSg : UC6S846.SigmaStd D) (h847 : R847E3Thin D) (h3 : S21_3 D Ch)
    (hO : LieOrderFormulasInput) (hThin : PartTwo.ThinList13) (hK : PartTwo.S17.K_LieModelNotL2)
    (h : S21_12R3 D Ch) : S21_12 D Ch := by
  have ha : S21_12a D Ch := s21_12a_of_s21_12aF h3 hO hThin hK
    fun hH c L hL p hp hp2 hch => (h hH c L hL p hp hp2 hch).1
  intro hH c L hL p hp hp2 hch
  have hLp := ha hH c L hL p hp hp2 hch
  refine ⟨hLp, ?_⟩
  by_cases hN : (L.subgroupOf D.M).Normal
  · exact s21_12L2_of_r847E3Thin h5 hSg h847 hH c hL hp hp2 hLp (Or.inl hN)
  rcases Nat.even_or_odd c.n with hev | hodd
  · exact (h hH c L hL p hp hp2 hch).2 hN hev hLp
  · exact s21_12L2_of_r847E3Thin h5 hSg h847 hH c hL hp hp2 hLp (Or.inr hodd)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UC22
