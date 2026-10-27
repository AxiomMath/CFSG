module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyFiveShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2CentralizerFpf
public import CFSG.LocalAnalysis.WeakClosure81.NineStep6
public import CFSG.RankThree.GF2n.Tim77Prop24TwoSz
public import CFSG.RankThree.PartTwo.Sec21.FF84S3BCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.RankThreeUC
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem config17_26a_II_gammaSet_facts {D : Data G} {V₀ V : Subgroup G}
    (h125 : Hyp125 D V₀ V) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V₀ 0 D.T) (hm : 4 < mSub V₀) :
    IsElemAbelian 2 A ∧ CFSG.CGT.Timmesfeld75.IsTI A ∧ rk ↥A = mSub V₀ ∧ A ≤ D.T := by
  classical
  have hV0ne : V₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, mSub, CFSG.Quasithin.rk_bot] at hm
    omega
  have hTI0 : CFSG.CGT.Timmesfeld75.IsTI V₀ := by
    rcases h125.1 with ⟨-, hbot⟩ | ⟨h0, -, -⟩
    · exact absurd hbot hV0ne
    · exact h0.2.2.2.1
  have hV0el : IsElemAbelian 2 V₀ := h125.pairFacts.elemAbelian₀
  obtain ⟨hAT, g, hAg, hmq⟩ := hA
  have hconjel : IsElemAbelian 2 (conjSubgroup V₀ g) := isElemAbelian_conjSubgroup' hV0el g
  have hAeq : A = conjSubgroup V₀ g :=
    (E3.mQuot_eq_zero_iff (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hconjel)
      hAg).mp hmq
  have hAel : IsElemAbelian 2 A := hAeq.symm ▸ hconjel
  have hATI : CFSG.CGT.Timmesfeld75.IsTI A := hAeq.symm ▸ isTI_conj hTI0 g
  have hcard : Nat.card ↥A = Nat.card ↥V₀ := by
    rw [hAeq]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  exact ⟨hAel, hATI, by unfold mSub rk; rw [hcard], hAT⟩

theorem config17_26a_II_map_pCoreOf_H1_le {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) :
    ((pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian)).subgroupOf (L ⊔ D.T)).map
        (gap17_25_action c.hyp125 c) ≤
      pCoreOf 2 (Subgroup.centralizer (((Subgroup.center
          ((barSub V₀ V c.hyp125.isElemAbelian D.T).subgroupOf
            (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T)))).map
          ((barSub V₀ V c.hyp125.isElemAbelian D.T).subgroupOf
            (barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T))).subtype) :
          Set ↥(barSub V₀ V c.hyp125.isElemAbelian (L ⊔ D.T)))) := by
  classical
  have hV := c.hyp125.isElemAbelian
  set H : Subgroup G := L ⊔ D.T with hHdef
  set H₁ : Subgroup G := H17_25_one D V₀ V L hV with hH1def
  set Ybar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV H with hYdef
  set Sbar : Subgroup ↥Ybar := (barSub V₀ V hV D.T).subgroupOf Ybar with hSdef
  set Cbar : Subgroup ↥Ybar :=
    Subgroup.centralizer (((Subgroup.center Sbar).map Sbar.subtype) : Set ↥Ybar) with hCdef
  set f : ↥H →* ↥Ybar := gap17_25_action c.hyp125 c with hfdef
  have hf : Function.Surjective f := gap17_25_action_surjective c
  have hH1 : (H₁.subgroupOf H) = Cbar.comap f :=
    gap17_25_H1_eq_comap c
  have hmapH1 : (H₁.subgroupOf H).map f = Cbar := by
    rw [hH1]
    exact Subgroup.map_comap_eq_self_of_surjective hf Cbar
  have hN1le : ((pCoreOf 2 H₁).subgroupOf H) ≤ (H₁.subgroupOf H) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H₁) (Subgroup.mem_subgroupOf.mp hx))
  have hKleC : ((pCoreOf 2 H₁).subgroupOf H).map f ≤ Cbar := by
    rw [← hmapH1]
    exact Subgroup.map_mono hN1le
  have hH1leH : H₁ ≤ H := by
    change preBarSub H V₀ V hV _ ≤ H
    exact inf_le_left
  have hKp : IsPGroup 2 (((pCoreOf 2 H₁).subgroupOf H).map f) := by
    have hN1p : IsPGroup 2 ((pCoreOf 2 H₁).subgroupOf H) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁).of_equiv
        (Subgroup.subgroupOfEquivOfLe
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 H₁).trans hH1leH)).symm
    exact hN1p.map f
  have hnorm : Cbar ≤ Subgroup.normalizer
      ((((pCoreOf 2 H₁).subgroupOf H).map f : Subgroup ↥Ybar) : Set ↥Ybar) := by
    rw [← hmapH1]
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map f)
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro q
    simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁) (Subgroup.mem_subgroupOf.mp hk)) q
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKleC hnorm hKp

theorem config17_26a_II_inf_le_ker
    {D : Data G} {V₀ V L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (h20 : R17_20At D V₀ V) (hC117 : C117 D V₀ V)
    (hKF1 : Inputs1719.K_J2_centralizer_fpf) (hJ2 : IsSpor (Bar2 L) .J2) (hm : 4 < mSub V₀)
    {A : Subgroup G} (hA : A ∈ E3.gammaSet V₀ 0 D.T) {h : G}
    (hh : h ∈ H17_25_one D V₀ V L c.hyp125.isElemAbelian)
    (hO1 : InCalO 1 (normalizer (A : Set G)) ⊥ A h)
    (hB : A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h) ≤
      pCoreOf 2 (H17_25_one D V₀ V L c.hyp125.isElemAbelian)) :
    (A ⊓ pCoreOf 2 (A ⊔ conjSubgroup A h)).subgroupOf (L ⊔ D.T) ≤
      (gap17_25_action c.hyp125 c).ker := by
  classical
  have hV := c.hyp125.isElemAbelian
  set H : Subgroup G := L ⊔ D.T with hHdef
  set H₁ : Subgroup G := H17_25_one D V₀ V L hV with hH1def
  set X : Subgroup G := A ⊔ conjSubgroup A h with hXdef
  set B : Subgroup G := A ⊓ pCoreOf 2 X with hBdef
  set P : Subgroup G := pCoreOf 2 X ⊓ pCoreOf 2 H₁ with hPdef
  set Ybar : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV H with hYdef
  set Sbar : Subgroup ↥Ybar := (barSub V₀ V hV D.T).subgroupOf Ybar with hSdef
  set Cbar : Subgroup ↥Ybar :=
    Subgroup.centralizer (((Subgroup.center Sbar).map Sbar.subtype) : Set ↥Ybar) with hCdef
  set f : ↥H →* ↥Ybar := gap17_25_action c.hyp125 c with hfdef
  obtain ⟨hAel, hATI, hrk, hAT⟩ := config17_26a_II_gammaSet_facts c.hyp125 hA hm
  have h2rk : 2 < rk ↥A := by rw [hrk]; omega
  have hTH1 : D.T ≤ H₁ := by
    simpa [H₁, hV] using T_le_H17_25_one c.hyp125
  have hAH1 : A ≤ H₁ := hAT.trans hTH1
  have hH1H : H₁ ≤ H := by
    change preBarSub H V₀ V hV _ ≤ H
    exact inf_le_left
  have hAH : A ≤ H := hAH1.trans hH1H
  have hAhH1 : conjSubgroup A h ≤ H₁ := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    have hxeq : x = h⁻¹ * (h * x * h⁻¹) * h := by group
    rw [hxeq]
    exact H₁.mul_mem (H₁.mul_mem (H₁.inv_mem hh) (hAH1 hx)) hh
  have hXH1 : X ≤ H₁ := by
    rw [hXdef]
    exact sup_le hAH1 hAhH1
  have hO2eq : pCoreOf 2 X = nVSub A h ⊔ bSub A h := by
    rw [hXdef]
    exact pCoreOf_sup_conj_eq_nVSub_sup_bSub hAel hATI h2rk hO1
  have hBeq : B = nVSub A h := by
    rw [hBdef, hXdef]
    exact inf_pCoreOf_sup_conj_eq hAel hATI h2rk hO1
  have hUne : nVSub A h ≠ ⊥ := nVSub_ne_bot hAel h2rk hO1
  have hmqU : E3.mQuot A (nVSub A h) = 1 := mQuot_nVSub_eq_one hAel hO1
  have hne : nVSub A h ≠ A := by
    intro hEq
    rw [hEq, E3.mQuot_self] at hmqU
    omega
  have hlt : nVSub A h < A := lt_of_le_of_ne inf_le_left hne
  obtain ⟨a, haA, haU⟩ := SetLike.exists_of_lt hlt
  have hAhN : ¬ conjSubgroup A h ≤ normalizer (A : Set G) := hO1.1.1
  have hex : ∃ a' ∈ conjSubgroup A h, a' ∉ normalizer (A : Set G) := by
    by_contra hc
    exact hAhN fun x hx => by_contra fun hxn => hc ⟨x, hx, hxn⟩
  obtain ⟨a', ha'Ah, ha'N⟩ := hex
  have ha'B : a' ∉ bSub A h := fun hb => ha'N (Subgroup.mem_inf.mp hb).2
  have hrX : a * a' ∈ X := by
    rw [hXdef]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right ha'Ah)
  have hrH1 : a * a' ∈ H₁ := hXH1 hrX
  have hrH : a * a' ∈ H := hH1H hrH1
  set r : ↥H := ⟨a * a', hrH⟩ with hrdef
  have hrodd : Odd (orderOf (a * a')) :=
    odd_orderOf_mul hAel hATI hUne haA haU ha'Ah ha'B
  have hBP : B ≤ P := by
    intro x hx
    rw [hBdef] at hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hB hx⟩
  have hPX : P ≤ pCoreOf 2 X := inf_le_left
  have hPH1 : P ≤ pCoreOf 2 H₁ := inf_le_right
  have hrNorX : a * a' ∈ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) hrX
  have hrNorH1 : a * a' ∈ Subgroup.normalizer (pCoreOf 2 H₁ : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁) hrH1
  have hrNorP : a * a' ∈ Subgroup.normalizer (P : Set G) :=
    (Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2 X) (K := pCoreOf 2 H₁))
      (Subgroup.mem_inf.mpr ⟨hrNorX, hrNorH1⟩)
  have hf : Function.Surjective f := gap17_25_action_surjective c
  have hH1eq : (H₁.subgroupOf H) = Cbar.comap f :=
    gap17_25_H1_eq_comap c
  have hmapH1 : (H₁.subgroupOf H).map f = Cbar := by
    rw [hH1eq]
    exact Subgroup.map_comap_eq_self_of_surjective hf Cbar
  have hrHsub : (r : ↥H) ∈ H₁.subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr hrH1
  have hxC : f r ∈ Cbar := by
    rw [← hmapH1]
    exact Subgroup.mem_map_of_mem f hrHsub
  have hxodd : Odd (orderOf (f r)) := by
    have hdvd : orderOf (f r) ∣ orderOf (a * a') := by
      have h := orderOf_map_dvd (f : ↥H →* ↥Ybar) (r : ↥H)
      simpa [hrdef, Subgroup.orderOf_mk] using h
    exact hrodd.of_dvd_nat hdvd
  have hxnorm : f r ∈ Subgroup.normalizer ((P.subgroupOf H).map f : Set ↥Ybar) := by
    have hrN : r ∈ Subgroup.normalizer ((P.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro q
      simpa [hrdef, Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp hrNorP q
    exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f hrN)
  have hfpf : ∀ p ∈ (P.subgroupOf H).map f,
      f r * p = p * f r → p = 1 := by
    intro p hp hcomm
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    set q₀ : G := (q : G)
    have hq₀P : q₀ ∈ P := Subgroup.mem_subgroupOf.mp hq
    set ker' : Subgroup G := (f.ker).map H.subtype with hker'def
    have hPH : P ≤ H := (hPH1.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H₁)).trans hH1H
    have hkerH : (ker'.subgroupOf H).Normal := by
      have heq : ker'.subgroupOf H = f.ker := by
        apply Subgroup.map_injective H.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le (H := ker') (K := H)
          (Subgroup.map_subtype_le f.ker)]
      rw [heq]
      exact MonoidHom.normal_ker f
    have hHker : H ≤ Subgroup.normalizer (ker' : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le f.ker)).1 hkerH
    have hNn : ((P ⊓ ker').subgroupOf P).Normal := by
      have h := Subgroup.inf_subgroupOf_inf_normal_of_right (A := P) (B' := ker') (B := H)
        (hN := hkerH)
      rwa [inf_eq_left.mpr hPH] at h
    have hwker : (r * q * r⁻¹ * q⁻¹ : ↥H) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : f (r * q * r⁻¹ * q⁻¹) =
          f r * f q * (f r)⁻¹ * (f q)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [h1]
      have h2 : f r * f q * (f r)⁻¹ * (f q)⁻¹ =
          (f r * f q) * (f q * f r)⁻¹ := by group
      rw [h2, hcomm, mul_inv_cancel]
    set n₀ : G := (a * a') * q₀ * (a * a')⁻¹ * q₀⁻¹ with hn₀def
    have hn₀ker : n₀ ∈ ker' := by
      refine Subgroup.mem_map.mpr
        ⟨r * q * r⁻¹ * q⁻¹, hwker, ?_⟩
      show (a * a') * q₀ * (a * a')⁻¹ * q₀⁻¹ = n₀
      rw [hn₀def]
    have hn₀P : n₀ ∈ P := by
      have hrq : (a * a') * q₀ * (a * a')⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hrNorP q₀).mp hq₀P
      exact P.mul_mem hrq (P.inv_mem hq₀P)
    have hn₀N : n₀ ∈ P ⊓ ker' := Subgroup.mem_inf.mpr ⟨hn₀P, hn₀ker⟩
    have hnN : q₀⁻¹ * n₀ * q₀ ∈ P ⊓ ker' := by
      have hmem : (⟨n₀, hn₀P⟩ : ↥P) ∈ (P ⊓ ker').subgroupOf P := hn₀N
      have hconj := hNn.conj_mem ⟨n₀, hn₀P⟩ hmem ⟨q₀⁻¹, P.inv_mem hq₀P⟩
      simpa using Subgroup.mem_subgroupOf.mp hconj
    have hrker : a * a' ∈ Subgroup.normalizer (ker' : Set G) := hHker (hH1H hrH1)
    have hrNorN : a * a' ∈ Subgroup.normalizer ((P ⊓ ker') : Set G) :=
      (Subgroup.inf_normalizer_le_normalizer_inf (H := P) (K := ker'))
        (Subgroup.mem_inf.mpr ⟨hrNorP, hrker⟩)
    have hQP : IsPGroup 2 P :=
      IsPGroup.to_inf_left (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    obtain ⟨q', hq', n', hn', hqeq⟩ :=
      @CFSG.RankThree.PartTwo.Sec21.FF84.S3.B_coprime_quot G _ _ 2 ⟨Nat.prime_two⟩
        P (P ⊓ ker') (a * a') hQP inf_le_left hNn hrNorP hrNorN hrodd.not_two_dvd_nat
        q₀ hq₀P ⟨q₀⁻¹ * n₀ * q₀, hnN, by rw [hn₀def]; group⟩
    have hq'P : q' ∈ P := (Subgroup.mem_inf.mp hq').1
    have hq'C : q' ∈ Subgroup.centralizer ({a * a'} : Set G) := (Subgroup.mem_inf.mp hq').2
    have hq'comm : (a * a') * q' = q' * (a * a') :=
      (Subgroup.mem_centralizer_singleton_iff.mp hq'C).symm
    have hq'1 : q' = 1 := by
      refine (prop24Setup hAel hATI hUne hne).eq_one_of_commute_mul
        haA haU ha'Ah ha'B ?_ hq'comm
      rw [← hO2eq]
      exact hPX hq'P
    have hq₀N : q₀ ∈ P ⊓ ker' := by
      rw [hqeq, hq'1, one_mul]
      exact hn'
    have hq₀ker : q₀ ∈ ker' := (Subgroup.mem_inf.mp hq₀N).2
    obtain ⟨k, hkker, hkval⟩ := Subgroup.mem_map.mp hq₀ker
    rw [MonoidHom.mem_ker] at hkker
    have hkq : k = q := Subtype.ext (by simpa [q₀] using hkval)
    rw [← hkq]
    exact hkker
  have hMnorm : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 (h20 L c).2.1
  have hL1 : barSub V₀ V hV L ≠ ⊥ := gap17_25_barSub_L_ne_bot c h20 hC117
  have hPle : (P.subgroupOf H).map f ≤ ((pCoreOf 2 H₁).subgroupOf H).map f := by
    apply Subgroup.map_mono
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hPH1 (Subgroup.mem_subgroupOf.mp hx))
  have hPleC : (P.subgroupOf H).map f ≤
      pCoreOf 2 (Subgroup.centralizer (((Subgroup.center Sbar).map Sbar.subtype) :
        Set ↥Ybar)) := by
    refine hPle.trans ?_
    exact config17_26a_II_map_pCoreOf_H1_le c
  have hKnormal : ((barSub V₀ V hV L).subgroupOf Ybar).Normal :=
    gap17_25_barSub_normal c hMnorm
  have hKspor : IsSpor ↥((barSub V₀ V hV L).subgroupOf Ybar) .J2 :=
    gap17_25_barSub_isSpor (c := c) hJ2 hL1
  have hKindex : ∃ n : ℕ, ((barSub V₀ V hV L).subgroupOf Ybar).index = 2 ^ n :=
    exists_index_barSub_pow_two c.hyp125 c hMnorm
  have hSsylow : CFSG.Quasithin.IsSylowIn 2 Sbar ⊤ :=
    gap17_25_barSub_T_sylow c
  have hPbar_bot : (P.subgroupOf H).map f = ⊥ :=
    hKF1 (↥Ybar) ((barSub V₀ V hV L).subgroupOf Ybar) hKnormal hKspor hKindex
      Sbar hSsylow ((P.subgroupOf H).map f) (f r) hPleC hxC hxodd hxnorm hfpf
  intro b hb
  have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
  have hbP : (b : G) ∈ P := hBP hbB
  have hfb : f b ∈ (P.subgroupOf H).map f :=
    Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hbP)
  rw [hPbar_bot] at hfb
  exact Subgroup.mem_bot.mp hfb

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
