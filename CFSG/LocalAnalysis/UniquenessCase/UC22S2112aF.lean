module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.L2Over17
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel OddLieType)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aF (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    IsChev (BarInf L) p → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

theorem isL2Odd_of_thin_of_isChev (hO : LieOrderFormulasInput) (hThin : PartTwo.ThinList13)
    (hK : PartTwo.S17.K_LieModelNotL2) (D : Data G)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hthin : F08.Thin8 L) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hch : IsChev (BarInf L) p) :
    IsL2Odd (Bar2 L) p := by
  obtain ⟨hsimple, hlist⟩ := PartTwo.s13_list_bar hThin D hL hthin
  haveI : IsSimpleGroup (Bar2 L) := hsimple
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (uc22p21k_center_eq_bot hL.2.2)
  obtain ⟨t, n, f, hadm, hm⟩ := hch
  have hm' : LieModel (Bar2 L) t n p f := hm.of_mulEquiv e
  have hodd : OddLieType (Bar2 L) := ⟨t, n, p, f, hp, hp2, hadm, hm'⟩
  obtain ⟨r, hr, hr2, hmr⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ IsL2Odd (Bar2 L) r := by
    rcases hlist with ⟨a, ha⟩ | hL2 | ⟨a, hsz⟩ | hJ1
    · have ha2 : a = 2 := by
        rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO ha hodd with
          ⟨-, -, h⟩ | ⟨-, h2, -⟩ | ⟨h1, -⟩
        · exact h
        · exact absurd h2 (by norm_num)
        · exact absurd h1 (by decide)
      subst ha2
      obtain ⟨e5⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model (Bar2 L) ha
      exact ⟨5, Nat.prime_five, by norm_num, PartTwo.S17.isL2Odd_of_isL2Over17_prime
        Nat.prime_five (PartTwo.S17.isL2Over17_five_of_alt5 e5)⟩
    · exact hL2
    · exact (CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO hsz
        (by rintro ⟨h, -⟩; exact absurd h (by decide))
        (by rintro ⟨h, -⟩; exact absurd h (by decide))
        (by rintro ⟨h, -⟩; exact absurd h (by decide)) hodd).elim
    · exact (PartTwo.S17.not_oddLieType_of_isJ1 hO hJ1 hodd).elim
  have hr17 : PartTwo.S17.IsL2Over17 (Bar2 L) r :=
    ⟨r, 1, hr, hr2, (pow_one r).symm, le_rfl, hmr⟩
  obtain ⟨rfl, rfl⟩ : t = .PSL ∧ n = 2 := by
    by_contra hc
    exact hK (Bar2 L) t n p f r hp2 (by tauto) hadm hm' hr17
  have hpeq : p ^ f = r := by
    have h := CFSG.GH74.GLS.EvenSelP.pow_eq_of_lieModel hp hp2 hr hr2 hm' hmr
    rwa [pow_one] at h
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hpeq
    exact hr.one_lt.ne' hpeq.symm
  have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).1 (hpeq ▸ dvd_pow_self p hf0)
  exact hpr ▸ hmr

theorem s21_12aF_of_s21_12a {D : Data G} {Ch : Choice2011 G} (h : S21_12a D Ch) :
    S21_12aF D Ch :=
  fun hH c L hL p hp hp2 hch _ => PartTwo.S17.thin8_of_isL2Odd (h hH c L hL p hp hp2 hch)

theorem s21_12a_of_s21_12aF {D : Data G} {Ch : Choice2011 G} (h3 : S21_3 D Ch)
    (hO : LieOrderFormulasInput) (hThin : PartTwo.ThinList13)
    (hK : PartTwo.S17.K_LieModelNotL2) (h : S21_12aF D Ch) :
    S21_12a D Ch := by
  intro hH c L hL p hp hp2 hch
  refine isL2Odd_of_thin_of_isChev hO hThin hK D hL ?_ hp hp2 hch
  by_cases hb : ∃ b ∈ c.B0, b ≠ 1 ∧ CentralizesBar b L
  · exact h3 hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } L hL hb
  · exact h hH c L hL p hp hp2 hch fun b hb0 hcb =>
      Classical.byContradiction fun hne => hb ⟨b, hb0, hne, hcb⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
