module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fix
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GLift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.GH74.GLS.IVK.Proofs2.OddTools
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
import CFSG.GH74.GLS.Stage2.Local.P34Main
import CFSG.GH74.GLS.Stage2.Local.P34S5A
import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6Untw
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaGrpSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P218c
import CFSG.Models.Transport
import CFSG.Quasithin.Background.B216Quotient
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.G2Relaxed
import CFSG.Quasithin.EmptyFaithful.S14117
import CFSG.Quasithin.EmptyFaithful.S14117Coprime
import CFSG.Quasithin.EmptyFaithful.S14117Rank
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatTen
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.KD4T.Certs
import CFSG.RankThree.PartOne.S11d.OddOutPSL2
import CFSG.RankThree.PartOne.S11d.OutEsix
import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsL3EpsOdd17 IsReeOver17)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_sig_of_le_pRank {D : Data G} (hσ : UC6S846.SigmaStd D) {L : Subgroup G}
    (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h4 : 4 ≤ Open.pRank p L) :
    p ∈ D.sig ∧ IsStronglyPEmbedded p D.M := by
  obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp h4
  have hpσ : p ∈ D.sig :=
    hσ.four_mem p hp hp2 (UC6S846.le_pRank' hp (hEL.trans hL.1.le) hEel hEc)
  exact ⟨hpσ, UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ⟩

theorem uc22s2112r34_not_isL2Over17 {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (hno : ∀ f : ℕ, ¬ LieModel Y .PSL 2 p f) : ¬ IsL2Over17 Y (p ^ f) := by
  rintro ⟨r, e, hr, -, hq, he, hm⟩
  have hrq : r ∣ p ^ f := by
    rw [hq]
    exact dvd_pow_self r (by omega)
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrq)
  exact hno e hm

theorem uc22s2112r34_not_isL3EpsOdd17 {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (h4 : 4 ≤ Open.pRank p (⊤ : Subgroup Y)) : ¬ IsL3EpsOdd17 Y p := by
  have : Fact p.Prime := ⟨hp⟩
  have hle := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
    (A := Y) hp
  rw [Nat.factorization_def _ hp] at hle
  rintro (h | h)
  · have hc : Nat.card Y = ordA 2 (p ^ 1) := (h.card_eq_lieOrd (by norm_num)).trans rfl
    rw [hc, CFSG.ClassicalInvolution.RouteD.TWR.v_ordA2 one_pos] at hle
    omega
  · have hc : Nat.card Y = ordTwistedA 2 (p ^ 1) := (h.card_eq_lieOrd (by norm_num)).trans rfl
    rw [hc, CFSG.ClassicalInvolution.RouteD.TWR.v_ordTA2 one_pos] at hle
    omega

theorem uc22s2112r34_not_isReeOver17 {Y : Type} [Group Y] {q : ℕ}
    (hree : ∀ f : ℕ, ¬ LieModel Y .twistedG2 0 3 f) : ¬ IsReeOver17 Y q := by
  rintro ⟨m, -, hm⟩
  exact hree _ hm

theorem uc22s2112r34_inner_of_kFieldAutOdd (hKF1 : KFieldAutOdd) {D : Data G}
    {Ch : Choice2011 G} (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel (BarInf L) t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2) (hpσ : p ∈ D.sig)
    (hMs : IsStronglyPEmbedded p D.M) (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    {b : G} (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hbr : orderOf b = r) (hrg : ¬ r ∣ (genericOrders t n p f).1)
    (hrN : ¬ r ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hθ1 : inducedBarInfAutHom L ⟨b, hb⟩ ≠ 1) :
    inducedBarInfAutHom L ⟨b, hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  classical
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  by_contra hθ
  have hord : orderOf (inducedBarInfAutHom L ⟨b, hb⟩) = r := by
    have hd := orderOf_map_dvd (inducedBarInfAutHom L) ⟨b, hb⟩
    rw [Subgroup.orderOf_mk, hbr] at hd
    rcases (Nat.dvd_prime hr).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hθ1
    · exact h1
  obtain ⟨-, Y, hY, hYs, hYp⟩ :=
    hKF1 (BarInf L) t n p f r hp hp2 hadm hX hA1 hRee hr hr5 hrg _ hord hθ
  have hYp' : 2 ≤ Open.pRank p Y := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hYp
  obtain ⟨E, hEY, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hYp'
  have hp2Y : p ^ 2 ∣ Nat.card ↥Y := hEc ▸ Subgroup.card_dvd_of_le hEY
  have hpY : p ∣ Nat.card ↥Y := (dvd_pow_self p two_ne_zero).trans hp2Y
  have hrank : 2 ≤ Open.pRank p (signalizerFixedSubgroup (inducedBarInfAutHom L ⟨b, hb⟩)) :=
    UC6S846.le_pRank' hp (hEY.trans hY) hEel hEc
  have := hYs
  refine uc22s2112r34_false_of_fixed hKF7 hH c hL.1.le hpσ hMs hbB hb (hbr ▸ hr) (hbr ▸ hrN)
    hpN hrank hY ?_ (MonoidHom.id ↥Y) Function.surjective_id hpY ?_
  ·
    intro hsolv
    have : IsMulCommutative ↥Y := ⟨⟨IsSimpleGroup.comm_iff_isSolvable.2 hsolv⟩⟩
    have hprime := Group.is_simple_iff_prime_card.1 hYs
    rw [← (Nat.prime_dvd_prime_iff_eq hp hprime).1 hpY] at hp2Y
    have h2 := hp.two_le
    have hle := Nat.le_of_dvd hp.pos hp2Y
    nlinarith
  ·
    rintro rfl ⟨e⟩
    have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [Nat.card_congr e.toEquiv, h60] at hp2Y
    norm_num at hp2Y

theorem uc22s2112r34_inner_of_mem (hKF1 : KFieldAutOdd) {D : Data G} {Ch : Choice2011 G}
    (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : LieModel (BarInf L) t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hRee : t ≠ .twistedG2) (hpσ : p ∈ D.sig)
    (hMs : IsStronglyPEmbedded p D.M) (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L))
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hrg : ¬ r ∣ (genericOrders t n p f).1)
    (hrN : ¬ r ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {R : Subgroup G} (hRB : R ≤ c.B0)
    (hRr : ∀ x ∈ R, x ≠ 1 → orderOf x = r) {x : G} (hx : x ∈ R) :
    inducedBarInfAutHom L ⟨x, hBN (hRB hx)⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  by_cases hx1 : x = 1
  · subst hx1
    exact ⟨1, by rw [map_one, ← map_one (inducedBarInfAutHom L)]; rfl⟩
  · refine uc22s2112r34_inner_of_kFieldAutOdd hKF1 hKF7 hH c hL hp hp2 hadm hX hA1 hRee hpσ hMs
      hpN (hRB hx) _ hr hr5 (hRr x hx hx1) hrg hrN fun h1 => hx1 ?_
    exact hfaith x (hRB hx)
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 (hBN (hRB hx)) h1)

section Rank


theorem uc22s2112r34_pRank_of_lieModel {L : Subgroup G} {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel (BarInf L) t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1))
    (hRee : t ≠ .twistedG2) (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) :
    3 ≤ Open.pRank p L ∧ ((((t = .PSp ∧ n = 2) ∨ t = .G2) ∧ f = 1) ∨ 4 ≤ Open.pRank p L) := by
  rw [pRank_eq_pRank_barInf hp hpN]
  exact PartTwo.Inputs1719.OddLie.three_le_pRank_of_lieModel_odd hp hp2 hX hA1 hA2 hRee

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
