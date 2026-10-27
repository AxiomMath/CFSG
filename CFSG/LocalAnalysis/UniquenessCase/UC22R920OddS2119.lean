module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R920OddN
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenJ
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenShapes
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx21

theorem false_of_isL2Odd_r920odd (D : Data G) (Ch : Choice2011 G) (h212 : S21_12 D Ch)
    (h920 : R920odd D) (h847 : F08.R847 D) (hsig : D.sig.Nonempty) (hH : H1930 D)
    (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hLK : L ≠ K) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hLp : IsL2Odd (Bar2 L) p) {D₃ : Subgroup G} (hD₃L : D₃ ≤ L)
    (hD₃ : Nat.card D₃ = 3) (hD₃U : D₃ ∈ uniqueSet D.M) : False := by
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hp2 : p ≠ 2 := by omega
  haveI : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) hLp
  have hZc : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZc
  have hChev : IsChev (BarInf L) p :=
    ⟨.PSL, 2, 1, hLp.admissible, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hLp⟩
  have h12 := h212 hH c₀ L hL p hp hp2 hChev
  obtain ⟨b, hbB0, r, hr, hr2, hr3, hbo⟩ := exists_mem_B0_orderOf_ne_three c hn3
  have hb3 : b ∈ CFSG.Quasithin.opResidual 3 c.B0 :=
    CFSG.Quasithin.mem_opResidual_of_coprime hbB0 (by
      rw [hbo]
      exact (Nat.coprime_primes hr Nat.prime_three).2 hr3)
  have hb1 : b ≠ 1 := by
    intro hb
    rw [hb, orderOf_one] at hbo
    exact hr.ne_one hbo.symm
  set Z : Subgroup G := Subgroup.zpowers b with hZ
  have hZr : IsPGroup r Z := by
    rw [hZ]
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbo, pow_one])
  have hZ1 : Z ≠ ⊥ := by
    rw [hZ, Ne, Subgroup.zpowers_eq_bot]
    exact hb1
  have hZle : Z ≤ c₀.B := by
    rw [hZ]
    exact Subgroup.zpowers_le.mpr hbB0
  have hZres : Z ≤ CFSG.Quasithin.opResidual 3 c₀.B := by
    rw [hZ]
    exact Subgroup.zpowers_le.mpr hb3
  have hZL : ⁅Z, L⁆ ≤ CFSG.Open.pCoreOf 2 L :=
    (Subgroup.commutator_mono hZres le_rfl).trans h12.2
  exact (s21_2 D Ch hH c₀ Z hZle)
    (normalizer_le_of_commutator_le_pCoreOf_r920odd D h920 h847 hsig hL hK hLK hp5 hLp hD₃L hD₃
      hD₃U hr hr2 hZr hZ1 hZL)

end Ctx21

theorem s21_19_of_r920odd (hE : UC22P20gExcFacts) (D : Data G) (Ch : Choice2011 G)
    (h207 : S20_7 D) (h211 : S21_1 D Ch) (h212 : S21_12 D Ch) (h8107 : F08.R8107 D)
    (h847 : F08.R847 D) (h920 : R920odd D) (hsig : D.sig.Nonempty) : S21_19 D Ch := by
  intro hH c L hL K hK hLK hLn hLs hKs
  rcases hLs with hJ1 | ⟨p, hp, hp5, hLp⟩
  · exact Ctx21.false_of_isJ1_of_shape D Ch h211 h8107 hH c hL hK hLK hLn hJ1 hKs
  · have hn3 : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 hH c
    have hL3 := pRank_three_eq_one_and_thin8_or_isU3
      (Or.inr (Or.inr (Or.inr ⟨p, hp, hLp⟩)))
    have hK3 := pRank_three_eq_one_and_thin8_or_isU3 hKs
    have h3L : 3 ∣ Nat.card L :=
      CFSG.GroupTheory.dvd_card_of_one_le_pRank Nat.prime_three (by rw [hL3.1])
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
    let D₃ : Subgroup G := Subgroup.zpowers ((x : ↥L) : G)
    have hxG : orderOf ((x : ↥L) : G) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hx
    have hD₃L : D₃ ≤ L := Subgroup.zpowers_le.mpr x.2
    have hD₃3 : Nat.card D₃ = 3 := by
      rw [show D₃ = Subgroup.zpowers ((x : ↥L) : G) from rfl, Nat.card_zpowers, hxG]
    have hD₃U : D₃ ∈ uniqueSet D.M :=
      mem_uniqueSet_of_card_eq_three D h8107 hL hK hLK hL3 hK3 hD₃L hD₃3
    exact Ctx21.false_of_isL2Odd_r920odd D Ch h212 h920 h847 hsig hH c hn3 hL hK hLK hp hp5 hLp
      hD₃L hD₃3 hD₃U

end CFSG.LocalAnalysis.UniquenessCase.UC22
