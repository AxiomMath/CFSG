module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Prime
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213OutL2
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qe
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.OutNoOdd
import CFSG.Adapters.LieModelOrders
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Quasithin.EmptyFaithful.R3c3Rank
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinCycB
import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3Closed2 (L : Subgroup G) : Prop :=
  (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ 4 ≤ CFSG.Open.pRank r L) ∨
    (¬ 5 ∣ Nat.card (center (Bar2 L)) ∧ (IsSpor (BarInf L) .J2 ∨ IsSpor (BarInf L) .He)) ∨
    (∃ p e : ℕ, p.Prime ∧ 5 ≤ p ∧ 2 ≤ e ∧ ¬ p ∣ Nat.card (center (Bar2 L)) ∧
      LieModel (BarInf L) .PSL 2 p e) ∨
    (¬ 3 ∣ Nat.card (center (Bar2 L)) ∧ LieModel (BarInf L) .PSL 5 2 1)

@[expose] def S21_3Rest3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ¬ S21_3Closed L → ¬ S21_3Closed2 L →
    ¬ F08.Thin8 L → CFSG.Open.pRank 3 L ≤ 2 →
    (IsStronglyPEmbedded 3 D.M → CFSG.Open.pRank 3 L ≤ 1) →
    ∀ a ∈ c.B, (orderOf a).Prime →
      (∀ p ∈ D.sig,
        CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ D.M) ≤ 1) →
      ¬ CentralizesBar a L

theorem uc22s213_not_centralizesBar_of_four_le_pRank (hU : uniqueFourUnique G) {M L : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) (hLM : L ≤ M) {a : G} (hodd : Odd (orderOf a))
    (hpr : (orderOf a).Prime) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h4 : 4 ≤ CFSG.Open.pRank r L)
    (hN : ∀ p ∈ uniqueFourSigma M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  have hrσ := UC6.four_le_pRank_imp_mem_sigma hU hM hr hr2
    (h4.trans (CFSG.SectionRank.pRank_mono hr.one_lt hLM))
  have := uc22s213_pRank_le_one_of_centralizesBar hLM hodd hpr haL hr hr2 (hN r hrσ)
  omega

theorem uc22s213_not_centralizesBar_of_isSpor_J2_He (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hJHe : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName), (s = .J2 ∨ s = .He) →
      IsSpor X s → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) ∧ ¬ 125 ∣ Nat.card X ∧
        3600 < Nat.card X)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hZ : ¬ 5 ∣ Nat.card (center (Bar2 L)))
    {s : TauCeti.SporadicName} (hs : s = .J2 ∨ s = .He) (hX : IsSpor (BarInf L) s) {a : G}
    (ha : a ∈ c.B) (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  obtain ⟨hsimp, hnc⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  obtain ⟨h2, h125, h3600⟩ := hJHe (BarInf L) s hs hX
  have h2O := hout (BarInf L) hsimp hnc s hX
  haveI : Finite (MulAut (BarInf L)) :=
    Finite.of_injective (fun (g : MulAut (BarInf L)) (w : BarInf L) => g w)
      (fun g h hgh => MulEquiv.ext (congrFun hgh))
  have hpos : 0 < Nat.card (Outer (BarInf L)) := Nat.card_pos
  have h53 : ¬ 5 ^ 3 ∣ Nat.card (BarInf L) := by
    rw [show (5 : ℕ) ^ 3 = 125 by norm_num]
    exact h125
  refine uc22s213_not_centralizesBar_of_prime hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL
    Nat.prime_five le_rfl hZ h2 (fun P => ⟨⟨fun x y => Subtype.ext
      (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinCyc.comm_of_not_dvd Nat.prime_five P.isPGroup'
        h53 x x.2 y y.2)⟩⟩)
    (fun h5 => ?_) h3600 ha hpr hN
  have := Nat.le_of_dvd hpos h5
  omega

theorem uc22s213_lt_ordA_one {q : ℕ} (hq : 25 ≤ q) : 3600 < CFSG.Open.ordA 1 q := by
  have h : CFSG.Open.ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) := by
    simp [CFSG.Open.ordA]
  have hg : Nat.gcd 2 (q - 1) ≤ 2 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 2 _)
  have hg0 : 0 < Nat.gcd 2 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hq2 : 624 ≤ q ^ 2 - 1 := by
    have h625 : 25 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    norm_num at h625
    omega
  have hle : 3601 * Nat.gcd 2 (q - 1) ≤ q * (q ^ 2 - 1) :=
    calc 3601 * Nat.gcd 2 (q - 1) ≤ 3601 * 2 := Nat.mul_le_mul_left _ hg
      _ ≤ 25 * 624 := by norm_num
      _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq hq2
  rw [h]
  exact lt_of_lt_of_le (by norm_num) ((Nat.le_div_iff_mul_le hg0).mpr hle)

theorem uc22s213_not_centralizesBar_of_psl2 (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) {p e : ℕ} (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) (hX : LieModel (BarInf L) .PSL 2 p e) {a : G}
    (ha : a ∈ c.B) (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  have hp : p.Prime := hX.admissible.1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hsyl : ∀ P : Sylow p (BarInf L), IsElemAbelian p (P : Subgroup (BarInf L)) ∧
      Nat.card (P : Subgroup (BarInf L)) = p ^ e := fun P =>
    uc22p22q_psl2_sylow_elem hp hp2 hX
      ⟨P.subtype le_top, by rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top]⟩
  obtain ⟨P⟩ : Nonempty (Sylow p (BarInf L)) := inferInstance
  have hrank : e ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top (hsyl P).1 (hsyl P).2
  rw [uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ] at hrank
  by_cases he4 : 4 ≤ e
  · exact uc22s213_not_centralizesBar_of_four_le_pRank hU S.maxLocal
      (CFSG.Quasithin.A3.subnormal_le hL.1) (uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha) hpr hp hp2
      (he4.trans hrank) hN
  have hpe : ¬ p ∣ e := fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega
  have h25 : 25 ≤ p ^ e :=
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp5 2
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  have h3600 : 3600 < Nat.card (BarInf L) := by
    rw [hX.card_eq_lieOrd (by norm_num)]
    exact uc22s213_lt_ordA_one h25
  refine uc22s213_not_centralizesBar_of_prime hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL hp
    hp5 hZ ?_ (fun P => (hsyl P).1.1) (uc22s213_not_dvd_card_outer_psl2 hX hp2 hpe) h3600 ha hpr
    hN
  rw [uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
  omega

theorem uc22s213_not_centralizesBar_of_psl_five_two (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hX : LieModel (BarInf L) .PSL 5 2 1)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  have hc := hX.statedClassicalModel (by decide)
  have hout : Nat.card (Outer (BarInf L)) ∣ 2 ^ 1 := by
    simpa using (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound _ 5 2 1
      hc).2.2.2.2 (by norm_num)
  exact uc22s213_not_centralizesBar_of_inner hS hU S hσ hPart hSE hOut hL hZ
    (fun σ hσ' =>
      CFSG.EvenSporadicStandard.HSStd.InvCent.mem_range_conj_of_odd_orderOf_of_card_outer_dvd
        hout hσ')
    (by rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two hc]; decide)
    (CFSG.Quasithin.R3c3.two_le_pRank_three_isPSL_two_one (n := 5) (Or.inr rfl) hc) hk1 hodd hpr
    hN

theorem s21_3Rest2_of_rest3 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hSS : StronglyEmbeddedSolvable) (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (hout : ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup X → (∃ a b : X, a * b ≠ b * a) →
      ∀ s : TauCeti.SporadicName, IsSpor X s → Nat.card (Outer X) ≤ 2)
    (hJHe : ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName), (s = .J2 ∨ s = .He) →
      IsSpor X s → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) ∧ ¬ 125 ∣ Nat.card X ∧
        3600 < Nat.card X)
    (Ch : Choice2011 G) (h : S21_3Rest3 (UC6.dataOfSetup4 hS hU S) Ch) :
    S21_3Rest2 (UC6.dataOfSetup4 hS hU S) Ch := by
  intro hH c L hL hC hthin h3 hk1 a ha hpr hN
  by_cases hC2 : S21_3Closed2 L
  · have hodd := uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha
    rcases hC2 with ⟨r, hr, hr2, h4⟩ | ⟨hZ, hX | hX⟩ | ⟨p, e, -, hp5, he, hZ, hX⟩ | ⟨hZ, hX⟩
    · exact uc22s213_not_centralizesBar_of_four_le_pRank hU S.maxLocal
        (CFSG.Quasithin.A3.subnormal_le hL.1) hodd hpr hr hr2 h4 hN
    · exact uc22s213_not_centralizesBar_of_isSpor_J2_He hS hU S hσ hPart hSE hSS hK3 hB hOut Ch
        hH c hout hJHe hL hZ (Or.inl rfl) hX ha hpr hN
    · exact uc22s213_not_centralizesBar_of_isSpor_J2_He hS hU S hσ hPart hSE hSS hK3 hB hOut Ch
        hH c hout hJHe hL hZ (Or.inr rfl) hX ha hpr hN
    · exact uc22s213_not_centralizesBar_of_psl2 hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL
        hp5 he hZ hX ha hpr hN
    · exact uc22s213_not_centralizesBar_of_psl_five_two hS hU S hσ hPart hSE hOut hL hZ hX hk1
        hodd hpr (hN S.p S.hp)
  · exact h hH c L hL hC hC2 hthin h3 hk1 a ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
