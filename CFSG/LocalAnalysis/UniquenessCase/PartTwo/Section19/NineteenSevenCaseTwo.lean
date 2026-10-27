module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenSevenSixteenThirtySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Idx
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R39B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen24R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenFourteen
public import CFSG.LocalAnalysis.WeakClosure81.FourteenEightTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem nineteen_seven_mQuot_UOf_eq_two
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h3 : R19_3At D V₀ V p L K hS.ctx) (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) {g : G} (hO : InCalOStar 2 D.M V₀ V g) :
    E3.mQuot V (UOf D.M V g) = 2 := by
  have h125 : Hyp125 D V₀ V := hS.ctx.hyp.hyp125
  have h64 : Hyp64 2 D.M V₀ V g := hyp64_of_hyp125 h125 hO
  have h64' : Hyp64 2 D.M V₀ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hA1 : barSub V₀ V hV (BOf D.M V g) ≠ ⊥ := barSub_BOf_ne_bot_uncond h64'
  have hM : D.M ≤ Subgroup.normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ Subgroup.normalizer (V₀ : Set G) := h64'.le_normalizer₀
  set B : Subgroup G := BOf D.M V g with hBdef
  have hi : E3.mQuot (conjSubgroup V g) B = E3.mQuot (conjSubgroup V g) D.M := by
    unfold E3.mQuot
    rw [hBdef, BOf, inf_comm, Subgroup.inf_relIndex_right]
  have hile : E3.mQuot (conjSubgroup V g) B ≤ 2 := by
    rw [hi]
    exact hO.1.2.2.1
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) D.M :=
    ⟨inf_le_right, g, inf_le_left, rfl⟩
  have hB : barSub V₀ V hV B ∈ E3.aSet 2 (Mbar D.M V₀ V hV) :=
    nineteen_seven_barSub_mem_calABar D hV hS h3 h5 h61 hSg h1219 S hSω hSK
      (i := E3.mQuot (conjSubgroup V g) B) (k := 2) (by omega) hBγ hA1
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ BOf D.M V g, b ∉ F11.CTilde D.M V₀ V := by
    by_contra hcon
    push Not at hcon
    exact hA1 ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hcon)
  have hbs : b ∈ stabTil V₀ V := (inf_le_right.trans (le_stabTil hM hM₀)) hbB
  have hβ : actTil V₀ V hV ⟨b, hbs⟩ ∈ barSub V₀ V hV (BOf D.M V g) :=
    actTil_mem_barSub V₀ V hV hbB hbs
  have hX : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil V₀ V hV))) :=
    nineteen_seven_mbar_le_normalizer D hV hS S hSω
  have hU : ∀ w : Vtil V₀ V hV, w ∈ imgTil V₀ V hV (UOf D.M V g) ↔
      w * (actTil V₀ V hV ⟨b, hbs⟩ w)⁻¹ ∈ fixV (barSub V₀ V hV (BOf D.M V g)) :=
    fun w => mem_imgTil_UOf_iff h64' hgen hbB hbC hbs w
  obtain ⟨k, hk⟩ := OmegaModel.card_eq_mul_pow_of_aSet S hX hB hβ hU
  have hcardU : Nat.card (imgTil V₀ V hV (UOf D.M V g)) *
      (imgTil V₀ V hV (UOf D.M V g)).index = Nat.card (Vtil V₀ V hV) :=
    Subgroup.card_mul_index _
  have hidx_eq : (imgTil V₀ V hV (UOf D.M V g)).index = Nat.card S.K ^ k := by
    have hUpos : 0 < Nat.card (imgTil V₀ V hV (UOf D.M V g)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hUpos (by rw [hcardU, hk])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmQuot : E3.mQuot V (UOf D.M V g) = 2 * k := by
    rw [mQuot_UOf_eq_rkIdx h64' hgen, rkIdx, hidx_eq, hSK,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, padicValNat.prime_pow]
  have hmk_le : 2 * k ≤ 2 := by
    have h1 := mQuot_UOf_le hO
    rwa [hmQuot] at h1
  have hk_ne0 : k ≠ 0 := by
    intro hk0
    apply imgTil_UOf_ne_top h64' hgen
    rw [← Subgroup.index_eq_one, hidx_eq, hk0, pow_zero]
  have hk1 : k = 1 := by omega
  rw [hmQuot, hk1, mul_one]

theorem nineteen_seven_not_inCalOStar
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h2 : R19_2At D V₀ V p L K hS.ctx) (h3 : R19_3At D V₀ V p L K hS.ctx)
    (h5 : R19_5At D V₀ V p L K hS.ctx) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) (g : G) : ¬ InCalOStar 2 D.M V₀ V g := by
  intro hO
  have h125 : Hyp125 D V₀ V := hS.ctx.hyp.hyp125
  have h64 : Hyp64 2 D.M V₀ V g := hyp64_of_hyp125 h125 hO
  obtain ⟨Y, hYreg, hYfix⟩ := exists_isFixedPointFreeTorus h64
  have hYcard : Nat.card Y = 3 := by
    rw [hYreg.2.1,
      nineteen_seven_mQuot_UOf_eq_two D hV hS h3 h5 h61 hSg h1219 S hSω hSK hO]
    norm_num
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot] at hYcard
    simp at hYcard
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYne
  have hyY : (y : G) ∈ Y := y.2
  have hyne : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hyM : (y : G) ∈ D.M := by
    have h1 : (y : G) ∈ LOf V g ⊓ D.M := (Subgroup.mem_inf.1 (hYreg.1 hyY)).1
    exact (Subgroup.mem_inf.1 h1).2
  have hyord : orderOf (y : G) = 3 := by
    have hdvd : orderOf (y : G) ∣ Nat.card ↥Y := Subgroup.orderOf_dvd_natCard Y hyY
    rw [hYcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hyne
    · exact h
  have hy3 : (y : G) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hyord]
  have hyOpp : (y : G) ∈ Opp 3 D.M := by
    unfold Opp CFSG.RankThree.PartOne.pElementSubgroup
    exact Subgroup.subset_closure ⟨hyM, 1, by simpa using hyord⟩
  have h2' : Opp 3 D.M = L ⊔ K := h2
  have hyLK : (y : G) ∈ L ⊔ K := h2' ▸ hyOpp
  have h3' : ⁅L ⊔ K, V₀⁆ = ⊥ := h3
  have hcent : L ⊔ K ≤ Subgroup.centralizer (V₀ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3'
  have hcomm : ∀ z ∈ V₀, (y : G) * z * (y : G)⁻¹ = z := by
    intro z hz
    have hzy : z * (y : G) = (y : G) * z :=
      (Subgroup.mem_centralizer_iff.1 (hcent hyLK)) z hz
    calc (y : G) * z * (y : G)⁻¹ = z * (y : G) * (y : G)⁻¹ := by rw [hzy.symm]
      _ = z := by group
  have hV₀V : V₀ ≤ V := h125.pairFacts.le
  have hzN : ∀ z ∈ V₀, z ∈ NOf D.M V g := fun z hz =>
    hYfix (y : G) hyY hyne z (hV₀V hz) (hcomm z hz)
  have hV₀ne : V₀ ≠ ⊥ := by
    intro hbot
    have hbig : 1 < mSub V₀ := hS.ctx.hyp.big
    rw [hbot, show mSub (⊥ : Subgroup G) = 0 from rk_bot] at hbig
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV₀ne
  have hzV₀ : (z : G) ∈ V₀ := z.2
  have hzno : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzB : (z : G) ∈ BOf D.M V g := (Subgroup.mem_inf.1 (hzN (z : G) hzV₀)).2
  have hzVg : (z : G) ∈ conjSubgroup V g := (Subgroup.mem_inf.1 hzB).1
  haveI : IsMulCommutative ↥V := hV.1
  haveI : IsMulCommutative ↥(conjSubgroup V g) :=
    Subgroup.map_isMulCommutative (H := V) (f := (MulAut.conj g⁻¹).toMonoidHom)
  have hVg_comm : ∀ a ∈ conjSubgroup V g, ∀ b ∈ conjSubgroup V g, a * b = b * a :=
    isMulCommutative_iff_of_setLike.1
      (inferInstance : IsMulCommutative ↥(conjSubgroup V g))
  have hVg_le_M : conjSubgroup V g ≤ D.M := by
    intro x hx
    exact centralizer_singleton_le_M_of_mem_V₀' D h125 hzV₀ hzno
      (Subgroup.mem_centralizer_iff.2 fun w hw => by
        rw [Set.mem_singleton_iff.1 hw]
        exact hVg_comm z hzVg x hx)
  exact hO.1.1.1 hVg_le_M

section Certified


theorem nineteen_seven_calO2_eq_empty (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h2 : R19_2At D V₀ V p L K hS.ctx) (h3 : R19_3At D V₀ V p L K hS.ctx)
    (h5 : R19_5At D V₀ V p L K hS.ctx) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (S : OmegaModel (Vtil V₀ V hV)) (hSω : S.omega = barSub V₀ V hV L ⊔ barSub V₀ V hV K)
    (hSK : Nat.card S.K = 4) :
    calO2 2 D.M V₀ V = ∅ := by
  have h125 : Hyp125 D V₀ V := hS.ctx.hyp.hyp125
  have hV₀ : V₀ ≠ ⊥ := by
    intro hbot
    have hbig : 1 < mSub V₀ := hS.ctx.hyp.big
    rw [hbot, show mSub (⊥ : Subgroup G) = 0 from rk_bot] at hbig
    omega
  refine Set.eq_empty_iff_forall_notMem.2 fun X hX => ?_
  obtain ⟨g, -, hO1⟩ :=
    nineteen_seven_calO2_subset_calO1 D hV hS h3 h5 h61 hSg h1219 S hSω hSK hX
  have hH :=
    (weakClosureSetting_of_hyp125 D hx h61 h127 (r1114_holds D hx h61) h125 hV₀).hyp6H
  obtain ⟨-, hr⟩ := nineteen_seven_sixteen_thirtyFive D hV hS h5 h61 S hSω hSK
  have hlt : ((mSub V₀ + 2 : ℕ) : ℕ∞) < rMV D.M V :=
    lt_of_lt_of_le (by exact_mod_cast (by omega : mSub V₀ + 2 < 4 + mSub V₀)) hr
  have hstar : InCalOStar 2 D.M V₀ V g := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hlt
  exact nineteen_seven_not_inCalOStar D hV hS h2 h3 h5 h61 hSg h1219 S hSω hSK g hstar

theorem nineteen_seven_case_two (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (hV : IsElemAbelian 2 V) (hS : Setting19_7 D V₀ V p L K hV)
    (h2 : R19_2At D V₀ V p L K hS.ctx) (h3 : R19_3At D V₀ V p L K hS.ctx)
    (h5 : R19_5At D V₀ V p L K hS.ctx) (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D)
    (h127 : R127 D) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hii : NatOmegaPlus (barSub V₀ V hV L ⊔ barSub V₀ V hV K) ⊤ ⊥ 4 2) :
    False := by
  obtain ⟨S, hSω, hSK2⟩ :=
    exists_omegaModel_of_natOmegaPlus (a := 2) (by norm_num) hii
  have hSK : Nat.card S.K = 4 := by simpa using hSK2
  have h125 : Hyp125 D V₀ V := hS.ctx.hyp.hyp125
  have hV₀ : V₀ ≠ ⊥ := by
    intro hbot
    have hbig : 1 < mSub V₀ := hS.ctx.hyp.big
    rw [hbot, show mSub (⊥ : Subgroup G) = 0 from rk_bot] at hbig
    omega
  have hWc : E3.wClos V 0 D.T ≤ centralizer (V : Set G) :=
    nineteen_seven_wClos_le_centralizer D hV hS h3 h5 h61 hSg h1219 S hSω hSK
  have hrk : ∀ p ∈ D.sig, 3 ≤ CFSG.pRank p ↥D.M := fun p hp => by
    rw [UC6.groupPRank_eq_pRank]
    exact hx.three_le p hp
  have hN : Subgroup.normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    fifteen_thirteen_a D (r129_1_of_r127 D h127) h61 hx.sig_nonempty hrk h125 hWc
  have hδ : (4 : ℕ∞) ≤ deltaInf D.M V :=
    (nineteen_seven_sixteen_thirtyFive D hV hS h5 h61 S hSω hSK).1
  have hβ : (D.k : ℕ∞) < betaN 0 D.M V := by
    calc (D.k : ℕ∞) < (4 : ℕ∞) := by
          exact_mod_cast (by have hk := TwelveSeven.k_le_two D; omega : D.k < 4)
      _ ≤ deltaInf D.M V := hδ
      _ = deltaN (mSub V) D.M V := rfl
      _ ≤ deltaN 0 D.M V := deltaN_anti (Nat.zero_le _)
      _ ≤ betaN 0 D.M V := deltaN_le_betaN 0
  have h24 := trichotomy_of_lt D h126 h125
    (Sixteen24.k_lt_rParam_of_hyp125 D hSg h1219 hx h61 h125) hβ
  have hO2 : calO2 2 D.M V₀ V = ∅ :=
    nineteen_seven_calO2_eq_empty D hV hS h2 h3 h5 hx h61 h127 hSg h1219 S hSω hSK
  have h2rk : 2 ≤ rk ↥V := by
    have h1 : rk ↥V₀ ≤ rk ↥V := rk_mono h125.pairFacts.le
    have hbig : 1 < rk ↥V₀ := hS.ctx.hyp.big
    omega
  have hOk : calO2 D.k D.M V₀ V = ∅ := by
    have hsub := calO2_mono_index (M := D.M) (V₀ := V₀) hV
      (TwelveSeven.k_le_two D) h2rk
    rw [hO2] at hsub
    exact Set.subset_empty_iff.1 hsub
  have hC : ¬ centralizer (E3.cClos V D.k D.T : Set G) ≤ D.M := by
    rcases h24 with h1 | h1 | h1
    · exact absurd hN h1
    · exact h1
    · rw [hOk] at h1
      exact absurd h1 Set.not_nonempty_empty
  exact hC (centralizer_cClos_le_of_ne_bot D h125 hV₀ D.k)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
