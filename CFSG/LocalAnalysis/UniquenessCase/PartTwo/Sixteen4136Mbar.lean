module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem isKGroup_mbar (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : D.M ≤ stabTil V₀ V) : CFSG.Open.IsKGroup ↥(Mbar D.M V₀ V hV) := by
  have hK : CFSG.Open.IsKGroup ↥D.M :=
    D.standing.kProper.isKGroup D.M (uc22br4_M_ne_top D)
  have hsub : CFSG.Open.IsKGroup ↥(D.M.subgroupOf (stabTil V₀ V)) :=
    hK.of_injective (Subgroup.subgroupOfEquivOfLe hMs).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hMs).injective
  exact hsub.of_surjective ((actTil V₀ V hV).subgroupMap (D.M.subgroupOf (stabTil V₀ V)))
    (MonoidHom.subgroupMap_surjective _ _)

private theorem prod_two_pow_sub_dvd_168 {n : ℕ} (hn : n ≤ 3) :
    (∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ))) ∣ 168 := by
  interval_cases n <;> decide

theorem pRank_le_one_of_odd_of_rk_le_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hrk : rk W ≤ 3) {X : Subgroup (MulAut W)}
    (hX : Odd (Nat.card X)) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥X) ≤ 1 := by
  have hcardW : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have h2 : ∀ e : W, e * e = 1 := fun e => by rw [← pow_two]; exact hW e
  have hAut : Nat.card (MulAut W) =
      ∏ i : Fin (rk W), (2 ^ rk W - 2 ^ (i : ℕ)) :=
    CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two h2 (rk W) hcardW
  have hdvdAut : Nat.card (MulAut W) ∣ 168 := hAut ▸ prod_two_pow_sub_dvd_168 hrk
  have hdvdX : Nat.card X ∣ 168 := (Subgroup.card_subgroup_dvd_card X).trans hdvdAut
  have hcop8 : Nat.Coprime (Nat.card X) 8 := by
    rw [show (8:ℕ) = 2 ^ 3 by norm_num]
    exact (Nat.coprime_two_right.mpr hX).pow_right 3
  have hdvd21 : Nat.card X ∣ 21 := by
    have hdvd' : Nat.card X ∣ 8 * 21 := by
      rwa [show (8:ℕ) * 21 = 168 by norm_num]
    exact hcop8.dvd_of_dvd_mul_left hdvd'
  have hnot : ¬ p ^ 2 ∣ 21 := by
    rintro h
    have hpp : p ∣ p ^ 2 := by rw [pow_two]; exact dvd_mul_right p p
    have hp_dvd : p ∣ 21 := hpp.trans h
    have hp_le : p ≤ 21 := Nat.le_of_dvd (by norm_num) hp_dvd
    have hp2 : 2 ≤ p := hp.two_le
    interval_cases p <;> norm_num at h
  by_contra hgt
  push Not at hgt
  have hp2dvd : p ^ 2 ∣ Nat.card X := by
    have hpp := CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp
      (⊤ : Subgroup ↥X)
    rw [Subgroup.card_top] at hpp
    exact (pow_dvd_pow p (by omega : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥X))).trans hpp
  exact hnot (hp2dvd.trans hdvd21)

theorem even_card_mbar_of_hyp16 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    Even (Nat.card ↥(Mbar D.M V₀ V h.hyp125.isElemAbelian)) := by
  set hV := h.hyp125.isElemAbelian with hVdef
  set hpf := h.hyp125.pairFacts with hpfdef
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  haveI := s15_Three_cTilde_normal (D := D) hV hMs
  by_contra hodd
  have hoddOdd : Odd (Nat.card ↥(Mbar D.M V₀ V hV)) := Nat.not_even_iff_odd.mp hodd
  have hmBar_le : mBar D.M V₀ V hV ≤ 3 := by
    have h1 : ¬ (3 < mBar D.M V₀ V hV) := fun hlt =>
      h.not_gt ((Hyp125.mBarGT_iff_lt_mBar h.hyp125 3).2 hlt)
    omega
  have hmp : E3.mParam (Mbar D.M V₀ V hV) = rk (Vtil V₀ V hV) := by
    unfold E3.mParam
    rw [if_neg hodd]
  have hrk3 : rk (Vtil V₀ V hV) ≤ 3 := by
    rw [← hmp]
    exact hmBar_le
  have hprank : ∀ p : ℕ, p.Prime →
      CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) ≤ 1 := fun p hp =>
    pRank_le_one_of_odd_of_rk_le_three (s15_Infra_vtil_sq_eq_one V₀ V hV) hrk3 hoddOdd hp
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have hpP : p.Prime := (D.sig_prime p hp).1
  have hcardV₀ : Nat.card V₀ ≤ 4 := by
    have h2 : Nat.card V₀ = 2 ^ mSub V₀ := card_eq_two_pow_mSub hpf.elemAbelian₀.isPGroup
    rw [h2, show (4:ℕ) = 2 ^ 2 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) h.small
  obtain ⟨-, hle, hge⟩ :=
    uc22p22q_r115_of D hx h61 V₀ V (Hyp125.hyp11 h127 h.hyp125) hcardV₀ p hp
  have hle' : CFSG.Open.pRank p D.M - 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
    rw [← s15_Three_pRank_MBar11 (D := D) hV hMs p]
    exact hle
  have := hprank p hpP
  omega

theorem exists_involution_of_hyp16 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} (h : Hyp16 D V₀ V) :
    ∃ t ∈ Mbar D.M V₀ V h.hyp125.isElemAbelian, orderOf t = 2 ∧
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 := by
  set hV := h.hyp125.isElemAbelian with hVdef
  set hpf := h.hyp125.pairFacts with hpfdef
  have hev : Even (Nat.card ↥(Mbar D.M V₀ V hV)) :=
    even_card_mbar_of_hyp16 D hx h61 h127 h
  have hmBar_le : mBar D.M V₀ V hV ≤ 3 := by
    have h1 : ¬ (3 < mBar D.M V₀ V hV) := fun hlt =>
      h.not_gt ((Hyp125.mBarGT_iff_lt_mBar h.hyp125 3).2 hlt)
    omega
  have hmp : E3.mParam (Mbar D.M V₀ V hV) =
      sInf {n : ℕ | ∃ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))} := by
    unfold E3.mParam
    rw [if_pos hev]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : {n : ℕ | ∃ t ∈ Mbar D.M V₀ V hV, orderOf t = 2 ∧
      n = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Mbar D.M V₀ V hV)) 2
      (even_iff_two_dvd.1 hev)
    refine ⟨rkIdx (fixV (Subgroup.zpowers (x : MulAut (Vtil V₀ V hV)))),
      x, x.2, ?_, rfl⟩
    rw [Subgroup.orderOf_coe]
    exact hx2
  obtain ⟨t, htX, hto, hval⟩ := Nat.sInf_mem hne
  refine ⟨t, htX, hto, ?_⟩
  have h3 : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3 := by
    rw [← hval, ← hmp]
    exact hmBar_le
  calc rk ↥(commSub ⊤ (Subgroup.zpowers t))
      = rk ↥(commV (Subgroup.zpowers t)) := by rw [commV_eq_commSub]
    _ = rkIdx (fixV (Subgroup.zpowers t)) := by rw [rkIdx_fixV_zpowers]
    _ ≤ 3 := h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
