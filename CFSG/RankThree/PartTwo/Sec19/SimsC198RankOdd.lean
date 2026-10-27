module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartOne.LIT.RankProjective
import CFSG.RankThree.PartTwo.Sec19.SimsC198Crit
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
import CFSG.Models.PGLSimple
import CFSG.Models.PGLOrders
import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
import CFSG.LieType.Steinberg.CentralExt.GriessSmallRee
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbMainExc
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaPRank
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG
open CFSG.Open (StatedLieAdmissible StatedClassicalModel)
open CFSG.PGLModel (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec4 (g2ThreeIndex)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)

variable {X : Type} [Group X] [Finite X]

private theorem false_of_pRank_prime (h : RankHyp X) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ Subgroup.center X))) : False := by
  have h3 := CFSG.SectionRank.pRank_quotient_le_three (by omega : p ≠ 2)
    (h.rank_prime p Fact.out hp) (Subgroup.center X) le_rfl
  omega

private theorem false_of_pRank_three (h : RankHyp X) (h3 : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X))) : False := by
  rw [CFSG.SectionRank.pRank_quotient_eq _ h3] at h4
  have := h.rank_three
  omega

private theorem four_le_pRank_psl {G : Type} [Group G] [Finite G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (h : StatedClassicalModel G .PSL n p f) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hr with ⟨-, ⟨hn2, -⟩ | ⟨hn3, -⟩ | h4⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
  · omega
  · omega
  · exact h4
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h4

private theorem four_le_pRank_psu {G : Type} [Group G] [Finite G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (h : StatedClassicalModel G .PSU n p f) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hr with ⟨ht, -⟩ | ⟨-, ⟨hn3, -⟩ | h4⟩ | ⟨ht, -⟩ | h4
  · exact absurd ht (by decide)
  · omega
  · exact h4
  · exact absurd ht (by decide)
  · exact h4

private theorem four_le_pRank_psl_three {G : Type} [Group G] [Finite G] {p f : ℕ} (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (h : StatedClassicalModel G .PSL 3 p f) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hr with ⟨-, ⟨hn2, -⟩ | ⟨-, h2f⟩ | h4⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | h4
  · omega
  · omega
  · exact h4
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact h4

private theorem four_le_pRank_psu_three {G : Type} [Group G] [Finite G] {p f : ℕ} (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (h : StatedClassicalModel G .PSU 3 p f) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hr with ⟨ht, -⟩ | ⟨-, ⟨-, h2f⟩ | h4⟩ | ⟨ht, -⟩ | h4
  · exact absurd ht (by decide)
  · omega
  · exact h4
  · exact absurd ht (by decide)
  · exact h4

private theorem three_le_pRank_psp_two {G : Type} [Group G] [Finite G] {p : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel G .PSp 2 p 1) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hr with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨-, ⟨-, h3f⟩ | h4⟩ | h4
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · omega
  · omega
  · omega

theorem false_of_rankHyp_PSL4 (h : RankHyp X) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (e : X ⧸ Subgroup.center X ≃* projSL 4 (GaloisField p 1)) : False := by
  have hadm : StatedLieAdmissible .PSL 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, by simp, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e
  exact false_of_pRank_prime h hp (four_le_pRank_psl (by omega) le_rfl hm)

theorem false_of_rankHyp_PSU4 (h : RankHyp X) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (e : X ⧸ Subgroup.center X ≃* projSU 4 p 1) : False := by
  have hadm : StatedLieAdmissible .PSU 4 p 1 := ⟨Fact.out, le_rfl, by norm_num, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  exact false_of_pRank_prime h hp (four_le_pRank_psu (by omega) le_rfl hm)

theorem false_of_rankHyp_PSU4_three (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* projSU 4 3 1) : False := by
  have hadm : StatedLieAdmissible .PSU 4 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center X)
  · have hB : CFSG.Blueprint.LieModel (projSU 4 3 1) .PSU 4 3 1 :=
      Or.inl ⟨by decide,
        CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _)⟩
    have := CFSG.HardMathSupport.Timmesfeld.FieldBonus.five_le_pRank_of_lieModel_U43 e hB h3
    have := h.rank_three
    omega
  · exact false_of_pRank_three h h3 (four_le_pRank_psu (by norm_num) le_rfl hm)

theorem noLocalDatum_projSL_three_three : NoLocalDatum (projSL 3 (GaloisField 3 1)) := by
  have hadm : StatedLieAdmissible .PSL 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hcard : Nat.card (projSL 3 (GaloisField 3 1)) = 5616 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _))
  refine noLocalDatum_of_card (CFSG.PGLModel.isSimpleGroup_projSL_of_two_le (n := 3)
    (GaloisField 3 1) (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))) ?_
  intro N hN _ h5
  have := IsType198Card.le N hN
  rw [hcard] at h5
  omega

theorem noLocalDatum_projSU_three_three : NoLocalDatum (projSU 3 3 1) := by
  have hadm : StatedLieAdmissible .PSU 3 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  refine noLocalDatum_of_card (CFSG.PGLModel.isSimpleGroup_projSU_of_admissible hadm) ?_
  intro N hN _ h5
  have := IsType198Card.le N hN
  rw [CFSG.PGLModel.card_projSU_three_three] at h5
  omega

private theorem card_center_dvd_row (hq : IsQuasisimple X) {t : CFSG.Open.StatedLieTag}
    {n p f : ℕ}
    (hrow : Nonempty (CFSG.Open.griessHopfMultiplier (X ⧸ Subgroup.center X) ≃*
      CFSG.Blueprint.Multiplier.generic t n p f × CFSG.Blueprint.Multiplier.exceptional t n p f)) :
    Nat.card (Subgroup.center X) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨eg⟩ := hrow
  have h1 := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_hopf hq
    (MulEquiv.refl (X ⧸ Subgroup.center X))
  rw [Nat.card_congr eg.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod] at h1
  simpa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using h1

section Psp

theorem false_of_rankHyp_PSp4 (h : RankHyp X) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (e : X ⧸ Subgroup.center X ≃* projSp 2 (GaloisField p 1)) : False := by
  have hp4 : p ≠ 4 := fun h4 => by
    have : Nat.Prime 4 := h4 ▸ Fact.out
    exact absurd this (by norm_num)
  have hadm : StatedLieAdmissible .PSp 2 p 1 := ⟨Fact.out, le_rfl, le_rfl, by simp; omega⟩
  have hcm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm e
  obtain ⟨-, hrow⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row hcm
    (Or.inl (by rw [pow_one]; omega))
  have hd := card_center_dvd_row h.quasisimple hrow
  have hgen : genericOrders .PSp 2 p 1 = (Nat.gcd 2 (p ^ 1 - 1), 1) := rfl
  have hexc : exceptionalOrders .PSp 2 p 1 = (1, 1) := rfl
  rw [hgen, hexc] at hd
  have h2 : Nat.card (Subgroup.center X) ∣ 2 := by
    have : Nat.card (Subgroup.center X) ∣ Nat.gcd 2 (p ^ 1 - 1) := by simpa using hd
    exact this.trans (Nat.gcd_dvd_left _ _)
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center X) := fun hpd =>
    absurd (Nat.le_of_dvd two_pos (hpd.trans h2)) (by omega)
  have h3 := three_le_pRank_psp_two (by omega) hcm
  rw [CFSG.SectionRank.pRank_quotient_eq _ hpZ] at h3
  have := h.rank_prime p Fact.out hp
  omega

theorem false_of_rankHyp_PSU3_three (h : RankHyp X) {e : ℕ} (he : 2 ≤ e)
    (e' : X ⧸ Subgroup.center X ≃* projSU 3 3 e) : False := by
  have hadm : StatedLieAdmissible .PSU 3 3 e :=
    ⟨Nat.prime_three, by omega, le_rfl, by
      intro h2
      have h32 : 3 ^ e = 2 := (Prod.mk.inj h2).2
      have h30 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
      omega⟩
  have hcm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e'
  obtain ⟨-, hrow⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row hcm
    (by decide)
  have hd := card_center_dvd_row h.quasisimple hrow
  have hgen : genericOrders .PSU 3 3 e = (Nat.gcd 3 (3 ^ e + 1), 1) := rfl
  have hexc : exceptionalOrders .PSU 3 3 e = (1, 1) := rfl
  rw [hgen, hexc] at hd
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
    intro h3
    have h3' : 3 ∣ Nat.gcd 3 (3 ^ e + 1) := by simpa using h3.trans hd
    have h31 : 3 ∣ 3 ^ e + 1 := (Nat.dvd_gcd_iff.mp h3').2
    have h30 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
    omega
  exact false_of_pRank_three h h3 (four_le_pRank_psu_three (by norm_num) he hcm)

end Psp

section Psl

theorem false_of_rankHyp_PSL3_three (h : RankHyp X) {e : ℕ} (he : 2 ≤ e)
    (e' : X ⧸ Subgroup.center X ≃* projSL 3 (GaloisField 3 e)) : False := by
  have hadm : StatedLieAdmissible .PSL 3 3 e :=
    ⟨Nat.prime_three, by omega, by norm_num, by simp, by simp⟩
  have hcm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e'
  obtain ⟨-, hrow⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hcm
  have hd := card_center_dvd_row h.quasisimple hrow
  have hgen : genericOrders .PSL 3 3 e = (Nat.gcd 3 (3 ^ e - 1), 1) := rfl
  have hexc : exceptionalOrders .PSL 3 3 e = (1, 1) := rfl
  rw [hgen, hexc] at hd
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
    intro h3
    have h3' : 3 ∣ Nat.gcd 3 (3 ^ e - 1) := by simpa using h3.trans hd
    have h31 : 3 ∣ 3 ^ e - 1 := (Nat.dvd_gcd_iff.mp h3').2
    have h30 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
    have hpos : 0 < 3 ^ e := by positivity
    omega
  exact false_of_pRank_three h h3 (four_le_pRank_psl_three (by norm_num) he hcm)

theorem false_of_rankHyp_PSL4_three (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* projSL 4 (GaloisField 3 1)) : False := by
  have hadm : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hcm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e
  obtain ⟨-, hrow⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row hcm
  have hd := card_center_dvd_row h.quasisimple hrow
  have hgen : genericOrders .PSL 4 3 1 = (2, 1) := by decide
  have hexc : exceptionalOrders .PSL 4 3 1 = (1, 1) := rfl
  rw [hgen, hexc] at hd
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := fun h3 =>
    absurd (Nat.le_of_dvd (by norm_num) (h3.trans hd)) (by norm_num)
  exact false_of_pRank_three h h3 (four_le_pRank_psl (by norm_num) le_rfl hcm)

end Psl

section G2

theorem false_of_rankHyp_G2_large (h : RankHyp X) {q : TauCeti.PrimePower} (hp : 3 < q.p)
    (hq : q.exponent = 1) (hX : Sec4.IsoGTwo (X ⧸ Subgroup.center X) q) : False := by
  obtain ⟨hv, ⟨θ⟩⟩ := hX
  have hmod := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv θ
    (Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv (by omega))
  have h3 := (CFSG.SectionRank.g2_odd_central_cover_rank_three (Subgroup.center X) le_rfl
    q.prime_p (by omega) hmod).1
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h3
  have := h.rank_prime q.p q.prime_p hp
  omega

theorem false_of_rankHyp_G2_three (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) : False := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  have hmod : CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 :=
    CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
      (Sec4.Census.chevalleyExceptionalModel_G2_three q g2ThreeIndex.2 rfl rfl)
  have hB : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .G2 0 3 1 :=
    Or.inr (Or.inl ⟨rfl, by decide, hmod⟩)
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center X)
  · have := CFSG.HardMathSupport.Timmesfeld.FieldBonus.four_le_pRank_of_lieModel_G2
      (MulEquiv.refl _) hB h3
    have := h.rank_three
    omega
  · obtain ⟨eA⟩ :=
      CFSG.HardMathSupport.Timmesfeld.LieRank.nonempty_mulEquiv_adjointGroup_G2_of_lieModel hB
    obtain ⟨eR, -⟩ : ∃ eR : X ⧸ Subgroup.center X ≃*
        CFSG.HardMathSupport.Timmesfeld.LieRank.RG, True :=
      ⟨eA.trans (Subgroup.equivMapOfInjective _
        (CFSG.Quasithin.G2U.glHom (RingEquiv.refl (ZMod 3)))
        (CFSG.Quasithin.G2U.glHom_injective _)), trivial⟩
    haveI : Finite CFSG.HardMathSupport.Timmesfeld.LieRank.RG := Finite.of_equiv _ eR.toEquiv
    have hRG : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup CFSG.HardMathSupport.Timmesfeld.LieRank.RG) :=
      CFSG.HardMathSupport.Timmesfeld.LieRank.specA.n_le_pRank Nat.prime_three
    have heq : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup CFSG.HardMathSupport.Timmesfeld.LieRank.RG) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eR
    exact false_of_pRank_three h h3 (heq ▸ hRG)

theorem false_of_rankHyp_ree27 (h : RankHyp X) (hr : (TauCeti.LieTypeIndex.reeG2 1).Valid)
    (e : X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group) : False := by
  have hree : CFSG.Blueprint.ReeTitsModel (X ⧸ Subgroup.center X) .twistedG2 3 (2 * 1 + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 1 ⟨hr, ⟨e⟩⟩
  obtain ⟨-, -, h6⟩ := CFSG.SectionRank.smallReeModel_rank hree
  have hadm : StatedLieAdmissible .twistedG2 0 3 3 :=
    ⟨Nat.prime_three, by norm_num, rfl, rfl, ⟨1, rfl⟩, le_rfl⟩
  obtain ⟨-, hrow⟩ := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedG2_row
    (⟨hadm, Or.inr ⟨rfl, ⟨.reeG2 1, hr⟩, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩ :
      CFSG.Models.LieModel (X ⧸ Subgroup.center X) .twistedG2 0 3 3)
  have hd := card_center_dvd_row h.quasisimple hrow
  have hgen : genericOrders .twistedG2 0 3 3 = (1, 1) := rfl
  have hexc : exceptionalOrders .twistedG2 0 3 3 = (1, 1) := rfl
  rw [hgen, hexc] at hd
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := fun h3 =>
    absurd (Nat.le_of_dvd (by norm_num) (h3.trans hd)) (by norm_num)
  exact false_of_pRank_three h h3 (by omega)

end G2

end CFSG.RankThree.PartTwo.Sec19.SimsC198
