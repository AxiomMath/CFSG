module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KU3Census
import CFSG.Adapters.StatedPSLTwo
import CFSG.CGT.PushingUpLit.CGT6.SixFourLTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcRed
import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
import CFSG.RankThree.GF2n.Stroth80.Sec7TailRadicalSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem ne_bot_of_isL2_bar2 {X : Type} [Group X] [Finite X] {K : Subgroup X} {n : ℕ}
    (hL2 : IsL2 (Bar2 K) (2 * n)) (hn : 2 ≤ n) : K ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card (Bar2 K) = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) := by
    rw [CFSG.SeitzReduction.RankOne.card_of_lieModel_PSL_two_two hL2,
      CFSG.RankThree.PartOne.S12K.ordA_one_eq (by omega)]
  have hgt : 1 < Nat.card (Bar2 K) := by
    rw [hcard]
    have hq : 4 ≤ 2 ^ (2 * n) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
    have hq2 : 1 ≤ (2 ^ (2 * n)) ^ 2 - 1 := by
      have h4 : 4 ≤ (2 ^ (2 * n)) ^ 2 := by
        have ha : 2 ≤ 2 ^ (2 * n) := by omega
        calc 4 = 2 * 2 := by norm_num
          _ ≤ 2 ^ (2 * n) * 2 ^ (2 * n) := Nat.mul_le_mul ha ha
          _ = (2 ^ (2 * n)) ^ 2 := (pow_two _).symm
      omega
    have h := Nat.mul_le_mul hq hq2
    omega
  have hle : Nat.card (Bar2 K) ≤ Nat.card ↥K :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  rw [hbot] at hle hgt
  rw [Subgroup.card_bot] at hle
  omega

private theorem normalizer_ne_top_of_ne_bot_ne_top {X : Type} [Group X]
    (hsimple : IsSimpleGroup X) {K : Subgroup X} (hbot : K ≠ ⊥) (htop : K ≠ ⊤) :
    Subgroup.normalizer (K : Set X) ≠ ⊤ := by
  intro hN
  haveI := hsimple
  have hnormal : K.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  haveI := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K with h | h
  · exact hbot h
  · exact htop h

private theorem not_isSolvable_normalizer {X : Type} [Group X] {K : Subgroup X}
    (hperf : ⁅K, K⁆ = K) (hbot : K ≠ ⊥) :
    ¬ Group.IsSolvable ↥(Subgroup.normalizer (K : Set X)) := fun hsol =>
  CFSG.LocalAnalysis.GLTheoremA.Y10GField.solvable_no_perfect hsol
    (Subgroup.le_normalizer) hperf hbot

private theorem exists_psl2_of_not_isSolvable
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (eX : X ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f))
    {K : Subgroup X} (hns : ¬ Group.IsSolvable ↥(Subgroup.normalizer (K : Set X))) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(Subgroup.normalizer (K : Set X)) ≃*
      CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 m)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let ι : ↥(Subgroup.normalizer (K : Set X)) →* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup
      (GaloisField 2 f) :=
    eX.toMonoidHom.comp (Subgroup.normalizer (K : Set X)).subtype
  have hι : Function.Injective ι := eX.injective.comp (Subgroup.subtype_injective _)
  exact CFSG.RankThree.GF2n.Stroth80.exists_mulEquiv_psl2_of_not_isSolvable hF ι hι hns

private theorem card_psl2MatrixGroup_galoisField_two {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 m)) =
      2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
    2 (GaloisField 2 m)).toEquiv]
  exact CFSG.CGT.PushingUpLit.CGT6.card_psl2_two_pow hm hK

private theorem psl2_two_pow_card_lt {m f : ℕ} (hm : 2 ≤ m) (hmf : m < f) :
    2 ^ m * ((2 ^ m) ^ 2 - 1) < 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have ha : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
  have hab : 2 ^ m < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) hmf
  have h1 : (2 ^ m) ^ 2 - 1 < (2 ^ f) ^ 2 - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow 2 (2 ^ m) (by positivity))
      (Nat.pow_lt_pow_left hab (by norm_num))
  have hbf : 3 ≤ 2 ^ f := by omega
  have h2 : 0 < (2 ^ f) ^ 2 - 1 := by
    have h9 : 9 ≤ (2 ^ f) ^ 2 := by
      calc 9 = 3 * 3 := by norm_num
        _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hbf hbf
        _ = (2 ^ f) ^ 2 := (pow_two _).symm
    omega
  calc 2 ^ m * ((2 ^ m) ^ 2 - 1)
      < 2 ^ m * ((2 ^ f) ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
    _ < 2 ^ f * ((2 ^ f) ^ 2 - 1) := Nat.mul_lt_mul_of_pos_right hab h2

private theorem two_pow_add_one_lt_sub_one {m f : ℕ} (hm : 2 ≤ m) (hmf : m < f) :
    2 ^ m + 1 < 2 ^ f - 1 := by
  have ha : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
  have h : 2 ^ m + 2 < 2 ^ f := by
    have h4 : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (n := 2) (by norm_num) hm
    have h1 : 2 ^ (m + 1) ≤ 2 ^ f :=
      Nat.pow_le_pow_right (n := 2) (by norm_num) (by omega)
    rw [pow_succ] at h1
    have h2 : 2 ^ m + 2 < 2 ^ m * 2 := by omega
    omega
  exact Nat.lt_sub_iff_add_lt.mpr (by omega)

private theorem exists_centralizer_orderOf_ge_model {f : ℕ} (hf : 2 ≤ f)
    (x : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f)) (hxne : x ≠ 1)
    (hxodd : Odd (orderOf x)) :
    ∃ y : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f),
      y ∈ Subgroup.centralizer ({x} : Set _) ∧ 2 ^ f - 1 ≤ orderOf y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨hcyc, hcard, -⟩ :=
    CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_odd_element_full_centralizer
      f hf hF x hxne hxodd
  obtain ⟨y, hy⟩ := hcyc.exists_generator (α := ↥(Subgroup.centralizer ({x} : Set _)))
  have hyord : orderOf (y : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set _)) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy]
  refine ⟨(y : _), y.2, ?_⟩
  rw [hyord]
  rw [hF] at hcard
  rcases hcard with h | h <;> omega

private theorem symm_mem_centralizer_of_map_mem {X : Type} [Group X] {f : ℕ}
    (e : X ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f))
    {D₀ : Subgroup X} {d : ↥D₀} (htop : Subgroup.zpowers d = ⊤)
    {y : CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f)}
    (hy : y ∈ Subgroup.centralizer ({e (d : X)} : Set _)) :
    e.symm y ∈ Subgroup.centralizer (D₀ : Set X) := by
  have hcomm : e.symm y * (d : X) = (d : X) * e.symm y := by
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact ((Subgroup.mem_centralizer_iff.mp hy) (e (d : X)) (Set.mem_singleton _)).symm
  have hdmem : (d : X) ∈ Subgroup.centralizer ({e.symm y} : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hcomm
  have hzple : Subgroup.zpowers (d : X) ≤ Subgroup.centralizer ({e.symm y} : Set X) :=
    Subgroup.zpowers_le.mpr hdmem
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hmem : h ∈ Subgroup.zpowers (d : X) := by
    have hm : (⟨h, hh⟩ : ↥D₀) ∈ Subgroup.zpowers d := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact ((Subgroup.mem_centralizer_iff.mp (hzple hmem)) (e.symm y)
    (Set.mem_singleton _)).symm

private theorem exists_centralizer_orderOf_ge {X : Type} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (e : X ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField 2 f))
    {D₀ : Subgroup X} {p : ℕ} (hD0card : Nat.card D₀ = p) (hp : p.Prime) (hodd : Odd p) :
    ∃ c : X, c ∈ Subgroup.centralizer (D₀ : Set X) ∧ 2 ^ f - 1 ≤ orderOf c := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic ↥D₀ := isCyclic_of_prime_card (p := p) (by simpa using hD0card)
  obtain ⟨d, hd⟩ := IsCyclic.exists_generator (α := ↥D₀)
  have hdord : orderOf d = p := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hd, hD0card]
  have hdne : d ≠ 1 := by
    intro h1
    exact hp.ne_one (hdord.symm.trans (orderOf_eq_one_iff.mpr h1))
  have htop : Subgroup.zpowers d = ⊤ :=
    zpowers_eq_top_of_prime_card (by simpa using hD0card) hdne
  have hxne : e (d : X) ≠ 1 := by
    intro h1
    exact hdne (Subtype.ext (e.injective (by simpa using h1)))
  have hxodd : Odd (orderOf (e (d : X))) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hdord]
    exact hodd
  obtain ⟨y, hymem, hyord⟩ := exists_centralizer_orderOf_ge_model hf (e (d : X)) hxne hxodd
  exact ⟨e.symm y, symm_mem_centralizer_of_map_mem e htop hymem, by
    rwa [MulEquiv.orderOf_eq]⟩

theorem kU3CensusL2_holds : KU3CensusL2 := by
  intro X _ _ f hX K D₀ n p h
  obtain ⟨hperf, hL2, hn, -, hp, hpdvd, -, hD0card, hcen, hKtop⟩ := h
  obtain ⟨eX⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel hX
  have hf : 2 ≤ f := CFSG.SeitzReduction.RankOne.two_le_of_lieModel_PSL_two_two hX
  haveI : IsSimpleGroup X := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hX
  have hKne : K ≠ ⊥ := ne_bot_of_isL2_bar2 hL2 hn
  have hNne : Subgroup.normalizer (K : Set X) ≠ ⊤ :=
    normalizer_ne_top_of_ne_bot_ne_top inferInstance hKne hKtop
  have hNns : ¬ Group.IsSolvable ↥(Subgroup.normalizer (K : Set X)) :=
    not_isSolvable_normalizer hperf hKne
  obtain ⟨m, hm, ⟨eN⟩⟩ := exists_psl2_of_not_isSolvable (by omega) eX hNns
  have hmf : m < f := by
    by_contra hge
    have hNlt : Nat.card ↥(Subgroup.normalizer (K : Set X)) < Nat.card X := by
      have hlt : Subgroup.normalizer (K : Set X) < ⊤ := lt_of_le_of_ne le_top hNne
      have h := Subgroup.card_lt_of_lt hlt
      rwa [Nat.card_congr Subgroup.topEquiv.toEquiv] at h
    have hcardN : Nat.card ↥(Subgroup.normalizer (K : Set X)) =
        2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr eN.toEquiv, card_psl2MatrixGroup_galoisField_two (by omega)]
    have hcardX : Nat.card X = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
      rw [Nat.card_congr eX.toEquiv, card_psl2MatrixGroup_galoisField_two (by omega)]
    rw [hcardN, hcardX] at hNlt
    rcases lt_or_eq_of_le (le_of_not_gt hge) with hfm | hfm
    · exact absurd hNlt (not_lt.mpr (le_of_lt (psl2_two_pow_card_lt (by omega) hfm)))
    · rw [hfm] at hNlt
      exact lt_irrefl _ hNlt
  have hodd : Odd p :=
    Odd.of_dvd_nat (Even.add_one ((Nat.even_pow' (by omega)).mpr even_two)) hpdvd
  obtain ⟨c, hcmem, hcord⟩ := exists_centralizer_orderOf_ge hf eX hD0card hp hodd
  have hcN : c ∈ Subgroup.normalizer (K : Set X) := hcen hcmem
  have hcordN : orderOf (eN ⟨c, hcN⟩) = orderOf c := by
    rw [MulEquiv.orderOf_eq]
    exact (Subgroup.orderOf_coe ⟨c, hcN⟩).symm
  have hle : orderOf (eN ⟨c, hcN⟩) ≤ 2 ^ m + 1 := by
    have h := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le
      (GaloisField 2 m) (eN ⟨c, hcN⟩)
    have hcard : Nat.card (GaloisField 2 m) = 2 ^ m := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact GaloisField.card 2 m (by omega)
    rwa [hcard] at h
  exact absurd ((hcord.trans (le_of_eq hcordN.symm)).trans hle)
    (not_le.mpr (two_pow_add_one_lt_sub_one hm hmf))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
