module

public import CFSG.Quasithin.EmptyFaithful.S151CLDef
public import CFSG.Quasithin.EmptyFaithful.S151CLY
public import CFSG.Quasithin.EmptyFaithful.S152VL2
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G]

theorem false_of_isPSL_two_fm (hlist : Lemma115_3_List) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hcomp : IsComponentOf L (g1_1516 Z₁)) {p : ℕ} (hFM : IsFermatOrMersennePrime p)
    (hp7 : 7 ≤ p) (hmodel : IsPSL 2 p 1 ↥L) : False := by
  have hq := hc.ctx.qtfe
  have hp : p.Prime := hFM.1
  have hp2 : p ≠ 2 := by omega
  have h3 : 3 < p := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hq.omegaOneCenter_ne_bot
    exact ⟨a, a.2, fun h => ha (Subtype.ext h)⟩
  have hyp := hc.h18.six z hzZ hz1
  have hLin : IsComponentIn L (g1_1516 Z₁) := DoubleA3.isComponentIn_iff_open.mpr hcomp
  have := hq.simple
  have hcore := qtkeCore_of_cat hq.nonabelian hq.qtke
  obtain ⟨-, hcomm, -, hcases⟩ :=
    Lemma115_3_List.component_cases hlist hq.simple hq.nonabelian hcore hyp hLin
  have hin : InducesInner z L := S152V.inducesInner_of_cases_l2p hcases hp hmodel hp2
  have hZ : Subgroup.center ↥L = ⊥ := F420.center_eq_bot_of_statedPSL hmodel
  have hcard : 2 * Nat.card ↥L = p * (p ^ 2 - 1) :=
    F420.two_mul_card_of_statedPSL_two_odd hp hp2 hmodel
  have hheven : 2 ∣ p * (p ^ 2 - 1) := Dvd.intro _ hcard
  have hL1 : L ≠ ⊥ := by
    intro hL
    rw [hL, Subgroup.card_bot] at hcard
    have h9 : 9 ≤ p ^ 2 := by nlinarith
    have h24 : 3 * 8 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul h3.le (by omega)
    omega
  obtain ⟨l, hl, hl1, hll, hlz⟩ :=
    S152V.inner_involution_data hZ (sq_eq_one_of_mem_omegaOneCenter T hzZ) hcomm hL1 hin
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := S152V.exists_psl2_equiv hmodel
  have hAut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L := by
    have h1 := CFSG.QuasithinUnique.DoubleA3.card_mulAut_psl2_le_two_mul F hp hodd hF h3 hheven
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    exact h1
  have hY1G : oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      g1_1516 Z₁ := hc.h18.one.2.trans (mZ1516_le_g1 Mc Z₁)
  have hYC : oTwoUpper (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (L : Set G) := by
    refine (Subgroup.closure_le _).mpr fun k hk => ?_
    have hkY := mem_oTwoUpper_of_odd hk.1 hk.2
    have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
      oTwoUpper_le_normalizer_component h37 h38 hc hcomp hY1G
        (mem_oTwoUpper_of_odd hkY (by simpa using hk.2))
    have hkz : k * z = z * k := (Subgroup.mem_centralizer_iff.mp hk.1 z hzZ).symm
    have hcommk :=
      S152V.odd_centralizes_of_inner_involution hFM hF e hZ hAut hl hl1 hll hlz hkN hkz hk.2
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcommk x hx).symm
  have hLMc : L ≤ Mc := le_mc_of_le_centralizer_oTwoUpper hq
    (Subgroup.le_centralizer_iff.mp hYC)
  exact hc.hL.not_le fun x hx => ⟨hc.hL.mem.1 hx, hLMc hx⟩

theorem compListNoL32_holds (hlist : Lemma115_3_List) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    CompListNoL32 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hL32
  have hmodel : IsPSL 2 7 1 ↥L := by
    rcases hL32 with h | h
    · exact StandardRecognition.statedClassicalModel_of_blueprintLieModel (by decide)
        (CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _
          (StandardRecognition.blueprintLieModel_of_statedClassicalModel (by decide) h))
    · exact h
  exact false_of_isPSL_two_fm hlist h37 h38 hc hcomp
    ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩ le_rfl hmodel

theorem compListNoL2p_holds (hlist : Lemma115_3_List) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    CompListNoL2p := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp p hFM hp hmodel
  exact false_of_isPSL_two_fm hlist h37 h38 hc hcomp hFM hp.le hmodel

end CFSG.Quasithin
