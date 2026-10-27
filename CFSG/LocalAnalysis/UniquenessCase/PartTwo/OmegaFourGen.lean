module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenTwentyThreeHyp125
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Close
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38B
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure OmegaFourSetting (D : Data G) (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (S : OmegaModel (Vtil ⊥ V hV)) : Prop where
  hyp125 : Hyp125 D ⊥ V
  five_mem : 5 ∈ D.sig
  card_K : Nat.card S.K = 4
  omega_le : S.omega ≤ Mbar D.M ⊥ V hV
  le_normalizer : Mbar D.M ⊥ V hV ≤ Subgroup.normalizer (S.omega : Set (MulAut (Vtil ⊥ V hV)))
  wOne : ⁅E3.wClos V 1 D.T, V⁆ = ⊥
  aBar_le : aBar D.M ⊥ V hV ≤ 2
  mBar_eq : mBar D.M ⊥ V hV = 4

namespace OmegaFourSetting

theorem five_dvd_cent (D : Data G) (hext : DataExt D) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) : 5 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) := by
  by_contra hnd
  have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
  have h1 := pRank_le_pRank_mbar_of_not_dvd (V₀ := ⊥) hV hP (by norm_num : Nat.Prime 5) hnd
  have h2 := pRank_five_le_two_of_omegaModel S h.card_K (Mbar D.M ⊥ V hV)
  have h3 := hext.three_le 5 h.five_mem
  omega

theorem r16_34 (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {x : IntMod V hV}
    (hx : S.Q (mkTil ⊥ V hV x) ≠ 0) :
    1 < CFSG.Open.pRank 5 (D.M ⊓ centralizer ({x.val} : Set G)) ∧
      centralizer ({x.val} : Set G) ≤ D.M := by
  have hH125 : Hyp125 D ⊥ V := h.hyp125
  have hP : PairFacts D.M ⊥ V := hH125.pairFacts
  have h4 : Nat.card (⊥ : Subgroup G) ≤ 4 := by simp
  have hpp : Nat.Prime 5 := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hx1 : mkTil ⊥ V hV x ≠ 1 := fun h0 => hx (h0 ▸ S.Q_one)
  have hx0 : x.val ∉ (⊥ : Subgroup G) := fun h0 =>
    hx1 ((QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x).2 h0)
  have hperf := S.isPerfect_ptCent_omega0 hx
  have hcard := S.card_ptCent_omega0 hx
  have hpP₀ : 5 ∣ Nat.card ↥(ptCent S.omega0 (mkTil ⊥ V hV x)) := by
    rw [hcard, h.card_K]
    norm_num
  have hP₀ : ptCent S.omega0 (mkTil ⊥ V hV x) ≤
      ptCent (Mbar D.M ⊥ V hV) (mkTil ⊥ V hV x) :=
    inf_le_inf_right _ (S.omega0_le_omega.trans h.omega_le)
  have hker := five_dvd_cent D hext h
  obtain ⟨X, hXle, hXp, hXc⟩ := exists_noncyclic_cent_of_perfect_bar D hpp hp2 hV hP
    (Or.inl rfl) h4 x hx0 hP₀ hperf hpP₀ hker
  refine ⟨?_, ?_⟩
  · have h2 := uc22p22u_two_le_pRank hpp hp2 hXp hXc
    have h3 := CFSG.SectionRank.pRank_mono hpp.one_lt hXle
    omega
  · have hx1' : x.val ≠ 1 := fun h0 => hx0 (h0 ▸ (⊥ : Subgroup G).one_mem)
    have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 x.val x.val_mem⟩
    exact centralizer_le_of_noncyclic D h61 h.five_mem (hXle.trans inf_le_left) hXp hXc hx1'
      hx2 (hXle.trans inf_le_right)

theorem Q_eq_zero_of_mem_imgTil_bot (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {U : Subgroup G}
    (hUC : ¬ centralizer (U : Set G) ≤ D.M) {u : Vtil ⊥ V hV}
    (hu : u ∈ imgTil ⊥ V hV U) : S.Q u = 0 := by
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil ⊥ V hV U u).1 hu
  by_contra hne
  exact hUC ((Subgroup.centralizer_le (Set.singleton_subset_iff.2 hxU)).trans
    (r16_34 D h61 hext h hne).2)

theorem rk_imgTil_le_four (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {U : Subgroup G}
    (hUC : ¬ centralizer (U : Set G) ≤ D.M) : rk ↥(imgTil ⊥ V hV U) ≤ 4 := by
  have hsing : ∀ u ∈ imgTil ⊥ V hV U, S.Q u = 0 := fun u hu =>
    Q_eq_zero_of_mem_imgTil_bot D h61 hext h hUC hu
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [h.card_K]; norm_num
  have hcard := S.card_le_of_totallySingular hsing
  rw [card_eq_two_pow hW2 (imgTil ⊥ V hV U), hSK2, ← pow_mul] at hcard
  have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard
  omega

theorem two_mul_le_mQuot_of_mem_calDn_bot (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {U : Subgroup G} (hU : U ∈ calDn (mSub V) D.M V) :
    4 ≤ E3.mQuot V U := by
  obtain ⟨hUV, t, ht, ⟨k, hk⟩, W', hW'V, -, -, hW't, hD⟩ := hU
  have hH125 : Hyp125 D ⊥ V := h.hyp125
  have hP : PairFacts D.M ⊥ V := hH125.pairFacts
  obtain ⟨htM, htCU⟩ := Subgroup.mem_inf.1 ht
  have hts : t⁻¹ ∈ stabTil ⊥ V :=
    le_stabTil hP.le_normalizer hP.le_normalizer₀ (D.M.inv_mem htM)
  obtain ⟨w, hwW, hwt⟩ : ∃ w ∈ W', w ∉ centralizer ({t} : Set G) := by
    by_contra hcon
    exact hW't fun w hw => Classical.byContradiction fun hw' => hcon ⟨w, hw, hw'⟩
  have hwV : w ∈ V := hW'V hwW
  have htN : t⁻¹ * w * t ∈ V :=
    (Subgroup.mem_normalizer_iff''.1 (hP.le_normalizer htM) w).1 hwV
  have hz₀V : w⁻¹ * t⁻¹ * w * t ∈ V := by
    have h1 : w⁻¹ * (t⁻¹ * w * t) ∈ V := V.mul_mem (V.inv_mem hwV) htN
    simpa [mul_assoc] using h1
  have hz₀mem : w⁻¹ * t⁻¹ * w * t ∈ commElt W' t := Subgroup.subset_closure ⟨w, hwW, rfl⟩
  have hDz := hD _ hz₀mem
  have hz₁ : w⁻¹ * t⁻¹ * w * t ≠ 1 := by
    intro h0
    apply hwt
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh'
    rw [Set.mem_singleton_iff] at hh'
    rw [hh']
    have h2 : t⁻¹ * w * t = w := by
      calc t⁻¹ * w * t = w * (w⁻¹ * t⁻¹ * w * t) := by group
        _ = w := by rw [h0, mul_one]
    calc t * w = t * (t⁻¹ * w * t) := by rw [h2]
      _ = w * t := by group
  let xw : IntMod V hV := IntMod.mk hV ⟨w, hwV⟩
  let x₀ : IntMod V hV := xw⁻¹ * actStab ⊥ V hV ⟨t⁻¹, hts⟩ xw
  have hval : x₀.val = w⁻¹ * t⁻¹ * w * t := by
    show (xw⁻¹ * actStab ⊥ V hV ⟨t⁻¹, hts⟩ xw).val = _
    have hxw : xw.val = w := rfl
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, hxw]
    simp [mul_assoc]
  have hsing : S.Q (mkTil ⊥ V hV x₀) = 0 := by
    by_contra hne
    have h' := (r16_34 D h61 hext h (x := x₀) hne).2
    rw [hval] at h'
    exact hDz h'
  have hne1 : mkTil ⊥ V hV x₀ ≠ 1 := fun hh =>
    hz₁ (hval ▸ (mem_modNull ⊥ V hV x₀).1
      ((QuotientGroup.eq_one_iff (N := modNull ⊥ V hV) x₀).1 hh))
  let g : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨t⁻¹, hts⟩
  have hgM : g ∈ Mbar D.M ⊥ V hV := actTil_mem_barSub ⊥ V hV (D.M.inv_mem htM) hts
  have hgnorm : g ∈ Subgroup.normalizer (S.omega : Set (MulAut (Vtil ⊥ V hV))) :=
    h.le_normalizer hgM
  have hgord : ∃ j : ℕ, g ^ 2 ^ j = 1 := by
    refine ⟨k, ?_⟩
    have h1 : (⟨t⁻¹, hts⟩ : stabTil ⊥ V) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [inv_pow, ← hk, pow_orderOf_eq_one, inv_one]
    show actTil ⊥ V hV ⟨t⁻¹, hts⟩ ^ 2 ^ k = 1
    rw [← map_pow, h1, map_one]
  have hcomm : g (mkTil ⊥ V hV xw) * (mkTil ⊥ V hV xw)⁻¹ = mkTil ⊥ V hV x₀ := by
    have hg1 : g (mkTil ⊥ V hV xw) = mkTil ⊥ V hV (actStab ⊥ V hV ⟨t⁻¹, hts⟩ xw) :=
      actTil_mk ⊥ V hV _ _
    calc g (mkTil ⊥ V hV xw) * (mkTil ⊥ V hV xw)⁻¹
        = (mkTil ⊥ V hV xw)⁻¹ * mkTil ⊥ V hV (actStab ⊥ V hV ⟨t⁻¹, hts⟩ xw) := by
          rw [hg1, mul_comm]
      _ = mkTil ⊥ V hV x₀ := by
          show _ = mkTil ⊥ V hV (xw⁻¹ * actStab ⊥ V hV ⟨t⁻¹, hts⟩ xw)
          rw [map_mul, map_inv]
  have hcard := S.card_fixed_le_of_singular_commutator hgnorm hgord (w := mkTil ⊥ V hV xw)
    (by rw [hcomm]; exact hne1) (by rw [hcomm]; exact hsing)
  have hfix : ∀ q ∈ imgTil ⊥ V hV U, g q = q := by
    intro q hq
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil ⊥ V hV U q).1 hq
    have h1 : actStab ⊥ V hV ⟨t⁻¹, hts⟩ x = x := by
      apply IntMod.val_injective
      rw [actStab_apply_val]
      have hc := Subgroup.mem_centralizer_iff.1 htCU x.val hxU
      simp only [inv_inv]
      calc t⁻¹ * x.val * t = t⁻¹ * (x.val * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * x.val) := by rw [hc]
        _ = x.val := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    show actTil ⊥ V hV ⟨t⁻¹, hts⟩ (mkTil ⊥ V hV x) = mkTil ⊥ V hV x
    rw [actTil_mk, h1]
  have hW2 : ∀ v : Vtil ⊥ V hV, v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact S.mul_self_eq_one v
  have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [h.card_K]; norm_num
  have hrk : rk ↥(imgTil ⊥ V hV U) ≤ 2 * 2 := by
    have hle : Nat.card ↥(imgTil ⊥ V hV U) ≤ Nat.card {v : Vtil ⊥ V hV // g v = v} :=
      Nat.card_le_card_of_injective (fun q => (⟨q.1, hfix q.1 q.2⟩ : {v // g v = v}))
        (fun a b hab => Subtype.ext
          (congrArg (Subtype.val (p := fun v : Vtil ⊥ V hV => g v = v)) hab))
    have h2 := hle.trans hcard
    rw [card_eq_two_pow hW2 (imgTil ⊥ V hV U), hSK2, ← pow_mul] at h2
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
    omega
  have hq := mSub_eq_mQuot_add V U hV hUV
  have hU' := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V U hV hUV
  have hrk' := rk_top_vtil_add_mSub ⊥ V hV hP.le
  have h4 : rk (⊤ : Subgroup (Vtil ⊥ V hV)) = 8 := by
    have h5 := S.rk_top_eq (m := 2) hSK2
    omega
  have hmono : mSub (U ⊓ (⊥ : Subgroup G)) ≤ mSub (⊥ : Subgroup G) := rk_mono inf_le_right
  omega

theorem r16_35 (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) :
    (4 : ℕ∞) ≤ deltaInf D.M V ∧ (4 : ℕ∞) ≤ rMV D.M V := by
  have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
  refine ⟨?_, ?_⟩
  · unfold deltaInf deltaN
    refine le_iInf₂ fun U hU => ?_
    exact_mod_cast two_mul_le_mQuot_of_mem_calDn_bot D h61 hext h hU
  · have hrk8 : rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) + mSub (⊥ : Subgroup G) = mSub V :=
      rk_top_vtil_add_mSub ⊥ V hV hP.le
    have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [h.card_K]; norm_num
    have h4 : rk (⊤ : Subgroup (Vtil ⊥ V hV)) = 8 := by
      have h5 := S.rk_top_eq (m := 2) hSK2
      omega
    refine le_rMV_of_forall_rk_imgTil_le D h.hyp125 (b := 4) (c := 4) (by omega) ?_
    intro U _ hUC
    exact rk_imgTil_le_four D h61 hext h hUC

theorem five_le_rMV (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) : (5 : ℕ∞) ≤ rMV D.M V := by
  have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [h.card_K]; norm_num
  have hb : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M →
      rk ↥(imgTil ⊥ V hV U) ≤ 3 := by
    intro U hUV hUC
    by_contra hrk
    have hrk4 : 4 ≤ rk ↥(imgTil ⊥ V hV U) := by omega
    have hsing : ∀ u ∈ imgTil ⊥ V hV U, S.Q u = 0 := fun u hu =>
      Q_eq_zero_of_mem_imgTil_bot D h61 hext h hUC hu
    have hcard : Nat.card S.K ^ 2 ≤ Nat.card (imgTil ⊥ V hV U) := by
      rw [card_eq_two_pow hW2 (imgTil ⊥ V hV U), hSK2]
      calc (2 ^ 2) ^ 2 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ rk ↥(imgTil ⊥ V hV U) := Nat.pow_le_pow_right (by norm_num) hrk4
    obtain ⟨P₀, hP₀le, hperf, hcardP, hstab⟩ :=
      S.exists_perfect_normalizing_of_totallySingular hsing hcard
    have hP₀ : P₀ ≤ Mbar D.M ⊥ V hV := hP₀le.trans (S.omega0_le_omega.trans h.omega_le)
    have hp5 : 5 ∣ Nat.card P₀ := by
      rw [hcardP, hSK2]
      norm_num
    have hker := five_dvd_cent D hext h
    obtain ⟨X, hXle, hXp, hXc⟩ := exists_noncyclic_normalizer_of_perfect_bar D (by norm_num)
      hV hP hUV hP₀ hperf hp5 hstab hker
    have hU2 : IsPGroup 2 U := hV.isPGroup.to_le hUV
    have hU1 : U ≠ ⊥ := by
      rintro rfl
      have hbot : imgTil ⊥ V hV (⊥ : Subgroup G) = ⊥ := by
        ext q
        rw [mem_imgTil, Subgroup.mem_bot]
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [Subgroup.mem_bot] at hx
          have hx1 : x = 1 := IntMod.val_injective hx
          rw [hx1, map_one]
        · rintro rfl
          exact ⟨1, Subgroup.one_mem _, map_one _⟩
      rw [hbot, rk_bot] at hrk4
      omega
    have hN : normalizer (U : Set G) ≤ D.M :=
      normalizer_le_of_noncyclic D h61 h.five_mem (hXle.trans inf_le_left) hXp hXc hU1 hU2
        (hXle.trans inf_le_right)
    exact hUC ((Subgroup.centralizer_le_normalizer (U : Set G)).trans hN)
  have hrk8 : mSub V = 8 := by
    have h1 := rk_top_vtil_add_mSub ⊥ V hV hP.le
    rw [rk_top, rk, S.card_eq, h.card_K] at h1
    have h0 : mSub (⊥ : Subgroup G) = 0 := rk_bot
    rw [h0] at h1
    have h2 : padicValNat 2 ((4 : ℕ) ^ 4) = 8 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, padicValNat.prime_pow]
      norm_num
    omega
  exact le_rMV_of_forall_rk_imgTil_le D h.hyp125 (b := 3) (c := 5) (by omega) hb

end OmegaFourSetting

theorem barSub_mem_calABar_of_gammaSet_bot_gen (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V : Subgroup G} (h : Hyp125 D ⊥ V) {p : ℕ}
    (hp : p ∈ D.sig)
    (hcent : ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer ({v} : Set G)))
    {i k : ℕ} (hr : ((k + i : ℕ) : ℕ∞) ≤ rMV D.M V)
    (hδ : ((k + i : ℕ) : ℕ∞) ≤ deltaInf D.M V) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) (hA1 : barSub ⊥ V h.isElemAbelian A ≠ ⊥) :
    barSub ⊥ V h.isElemAbelian A ∈ calABar k D.M ⊥ V h.isElemAbelian := by
  have hsub : mSub (⊥ : Subgroup G) = 0 := rk_bot
  refine barSub_mem_calABar_of_gammaSet_gen D hSg h1219 h hp hcent
    (fun _ _ => bot_inf_eq _) ?_ hδ hA hA1
  rw [hsub]
  simpa using hr

theorem OmegaFourSetting.barSub_mem_calABar_of_gammaSet (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (hext : DataExt D)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {i k : ℕ}
    (hr : ((k + i : ℕ) : ℕ∞) ≤ rMV D.M V)
    (hδ : ((k + i : ℕ) : ℕ∞) ≤ deltaInf D.M V) {A : Subgroup G}
    (hA : A ∈ E3.gammaSet V i D.M) (hA1 : barSub ⊥ V hV A ≠ ⊥) :
    barSub ⊥ V hV A ∈ calABar k D.M ⊥ V hV := by
  have hdvd := five_dvd_cent D hext h
  have hcent : ∀ v ∈ V, v ≠ 1 →
      1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({v} : Set G)) := by
    intro v hv _
    have hle : F11.CTilde D.M ⊥ V ≤ D.M ⊓ centralizer ({v} : Set G) := by
      intro x hx
      refine Subgroup.mem_inf.2 ⟨cTilde_le_M D.M ⊥ V hx, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := mem_cTilde_mul_inv hV h.hyp125.pairFacts.le_normalizer hx hv
      rw [Subgroup.mem_bot] at h1
      have h2 : x * v * x⁻¹ = v := mul_inv_eq_one.1 h1
      calc x * v = (x * v * x⁻¹) * x := by group
        _ = v * x := by rw [h2]
    exact s13_one_le_pRank_of_dvd _ (by norm_num)
      (hdvd.trans (Subgroup.card_dvd_of_le hle))
  exact barSub_mem_calABar_of_gammaSet_bot_gen D hSg h1219 h.hyp125 (p := 5) h.five_mem
    hcent hr hδ hA hA1

theorem cTilde_bot_le_centralizer {M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) :
    F11.CTilde M ⊥ V ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := mem_cTilde_mul_inv hV hM hx hv
  rw [Subgroup.mem_bot] at h1
  have h2 : x * v * x⁻¹ = v := mul_inv_eq_one.1 h1
  calc v * x = (x * v * x⁻¹) * x := by rw [h2]
    _ = x * v := by group

theorem OmegaFourSetting.c33Setting (D : Data G) (h61 : UC6.R6_1 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) (hext : DataExt D)
    {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {S : OmegaModel (Vtil ⊥ V hV)} (h : OmegaFourSetting D V hV S) :
    C33Setting D.M V where
  elemAbelian := hV
  normalizer_eq := h.hyp125.normalizer_eq
  orth := by
    set φ := TwelveShort.mkTilEquiv V hV with hφ
    refine ⟨S.ofEquiv φ, by rw [OmegaModel.ofEquiv_card_K, h.card_K], ?_⟩
    have h2 : (autI hV D.M).map (MulAut.congr φ).toMonoidHom ≤
        Subgroup.normalizer (((S.ofEquiv φ).omega.map (MulAut.congr φ).toMonoidHom :
          Subgroup _) : Set _) := by
      rw [← TwelveTwentyThree.barSub_bot_eq_map_autI, omega_ofEquiv_map]
      exact h.le_normalizer
    rw [autI_top_eq_of_normalizer_eq hV h.hyp125.normalizer_eq]
    exact (map_le_normalizer_map_iff (MulAut.congr φ) _ _).1 h2
  gamma_le := by
    intro i hi A hA
    by_contra hnc
    have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
    have hA1 : barSub ⊥ V hV A ≠ ⊥ := by
      intro h0
      have hle := (barSub_eq_bot_iff hV hP.le_normalizer hP.le_normalizer₀ hA.1).1 h0
      exact hnc (hle.trans (cTilde_bot_le_centralizer hV hP.le_normalizer))
    obtain ⟨hδ4, hr4⟩ := r16_35 D h61 hext h
    have hr : ((3 + i : ℕ) : ℕ∞) ≤ rMV D.M V :=
      le_trans (by exact_mod_cast (by omega : 3 + i ≤ 4)) hr4
    have hδ : ((3 + i : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
      le_trans (by exact_mod_cast (by omega : 3 + i ≤ 4)) hδ4
    have hmem := h.barSub_mem_calABar_of_gammaSet D hSg h1219 hext hr hδ hA hA1
    have hle := E3.le_aParam_of_mem_aSet (X := Mbar D.M ⊥ V hV) (A := barSub ⊥ V hV A)
      (by norm_num : 0 < 3) hmem
    have hle' : 3 ≤ aBar D.M ⊥ V hV := hle
    have := h.aBar_le
    omega
  aSet_two := by
    intro A hA hnc
    have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
    have hMN : Subgroup.normalizer (V : Set G) = D.M := h.hyp125.normalizer_eq
    have hA1 : barSub ⊥ V hV A ≠ ⊥ := by
      intro h0
      rw [TwelveTwentyThree.barSub_bot_eq_map_autI,
        Subgroup.map_eq_bot_iff_of_injective _ (MulAut.congr _).injective,
        autI_eq_bot_iff hV (hMN ▸ hA.1)] at h0
      exact hnc h0
    obtain ⟨hδ4, hr4⟩ := r16_35 D h61 hext h
    have hrk : ((2 + 2 : ℕ) : ℕ∞) ≤ rMV D.M V := by
      have : (2 + 2 : ℕ) = 4 := by norm_num
      rw [this]
      exact hr4
    have hδ' : (((2 + 2 : ℕ)) : ℕ∞) ≤ deltaInf D.M V := by
      have : (2 + 2 : ℕ) = 4 := by norm_num
      rw [this]
      exact hδ4
    have hmem := h.barSub_mem_calABar_of_gammaSet D hSg h1219 hext (i := 2) (k := 2) hrk hδ'
      hA hA1
    unfold calABar at hmem
    change barSub ⊥ V hV A ∈ E3.aSet 2 (barSub ⊥ V hV D.M) at hmem
    rw [TwelveTwentyThree.barSub_bot_eq_map_autI, TwelveTwentyThree.barSub_bot_eq_map_autI]
      at hmem
    rw [autI_top_eq_of_normalizer_eq hV hMN]
    exact (aSet_map_congr_equiv_iff (TwelveShort.mkTilEquiv V hV) 2 _ _).1 hmem
  lt_rMV := lt_of_lt_of_le (by norm_num : (4 : ℕ∞) < 5) (five_le_rMV D h61 hext h)

theorem OmegaFourSetting.five_dvd_cent_singleton (D : Data G) (hext : DataExt D)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {v : G} (hv : v ∈ V) :
    1 ≤ CFSG.Open.pRank 5 (D.M ⊓ centralizer ({v} : Set G)) := by
  have hdvd := five_dvd_cent D hext h
  have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
  have hle : F11.CTilde D.M ⊥ V ≤ D.M ⊓ centralizer ({v} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.2 ⟨cTilde_le_M D.M ⊥ V hx, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := mem_cTilde_mul_inv hV hP.le_normalizer hx hv
    rw [Subgroup.mem_bot] at h1
    have h2 : x * v * x⁻¹ = v := mul_inv_eq_one.1 h1
    calc x * v = (x * v * x⁻¹) * x := by group
      _ = v * x := by rw [h2]
  exact s13_one_le_pRank_of_dvd _ (by norm_num) (hdvd.trans (Subgroup.card_dvd_of_le hle))

theorem OmegaFourSetting.Q_eq_zero_of_mem_imgTil_of_normalizer_bot (D : Data G)
    (h61 : UC6.R6_1 D) (hext : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V : Subgroup G} {hV : IsElemAbelian 2 V}
    {S : OmegaModel (Vtil ⊥ V hV)} (h : OmegaFourSetting D V hV S) {U : Subgroup G}
    (hUV : U ≤ V) (hUN : ¬ normalizer (U : Set G) ≤ D.M) {u : Vtil ⊥ V hV}
    (hu : u ∈ imgTil ⊥ V hV U) : S.Q u = 0 := by
  obtain ⟨x, hxU, rfl⟩ := (mem_imgTil ⊥ V hV U u).1 hu
  by_contra hne
  have hC := (r16_34 D h61 hext h (x := x) hne).2
  have hx1 : x.val ≠ 1 := by
    intro h0
    apply hne
    have h1 : x = 1 := IntMod.val_injective h0
    rw [h1, map_one, S.Q_one]
  apply hUN
  intro y hy
  by_contra hyM
  have hyx : y * x.val * y⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hy x.val).1 hxU
  have hx2 : x.val ^ 2 = 1 := hV.2 x.val x.val_mem
  have hU2 : ∀ z ∈ Subgroup.zpowers x.val, z = 1 ∨ z = x.val := by
    intro z hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have horder : orderOf x.val = 2 := orderOf_eq_prime hx2 hx1
    have hmod : x.val ^ (k % (2 : ℤ)) = x.val ^ k := by
      simpa [horder] using zpow_mod_orderOf x.val k
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [h0, zpow_zero] at hmod
      rw [← hk]
      exact hmod.symm
    · right
      rw [h1, zpow_one] at hmod
      rw [← hk]
      exact hmod.symm
  have hΓ : rankThreeGamma 1 2 (Subgroup.zpowers x.val) ≤ D.M := by
    refine rankThreeGamma_le_of_normalizer_le (M := D.M) (V₀ := Subgroup.zpowers x.val)
      (Z := Subgroup.zpowers x.val) ?_ le_rfl
    intro X hX hXne
    have hZcard : Nat.card (Subgroup.zpowers x.val) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx2 hx1]
    have hXcard : Nat.card X = 2 := by
      have hdvd : Nat.card X ∣ 2 := by
        rw [← hZcard]
        exact Subgroup.card_dvd_of_le hX
      have hpos : 1 < Nat.card X := by
        have : Nontrivial ↥X := (Subgroup.nontrivial_iff_ne_bot X).2 hXne
        exact Finite.one_lt_card
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
      omega
    have hXeq : X = Subgroup.zpowers x.val :=
      Subgroup.eq_of_le_of_card_ge hX (by rw [hXcard, hZcard])
    rw [hXeq]
    have hNU : normalizer (Subgroup.zpowers x.val : Set G) ≤
        centralizer ({x.val} : Set G) := by
      intro n hn
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hmem : n * x.val * n⁻¹ ∈ Subgroup.zpowers x.val :=
        (Subgroup.mem_normalizer_iff.1 hn x.val).1 (Subgroup.mem_zpowers x.val)
      rcases hU2 (n * x.val * n⁻¹) hmem with h1 | h2
      · exfalso
        have h3 : x.val = 1 := by
          have hc := congrArg (fun z => n⁻¹ * z * n) h1
          simpa [mul_assoc] using hc
        exact hx1 h3
      · calc n * x.val = (n * x.val * n⁻¹) * n := by group
          _ = x.val * n := by rw [h2]
    exact hNU.trans hC
  have hyinv : y⁻¹ ∉ D.M := fun hh => hyM (by simpa using D.M.inv_mem hh)
  have h22 := sixteen_twentyTwo_gen D hSg h1219 hV h.five_mem
    (fun v hv _ => h.five_dvd_cent_singleton D hext hv) y⁻¹ hyinv
    (Subgroup.zpowers x.val) (Subgroup.zpowers_le.mpr x.val_mem) hΓ
  have hmem : y * x.val * y⁻¹ ∈ conjSubgroup (Subgroup.zpowers x.val) y⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have e : y⁻¹ * (y * x.val * y⁻¹) * (y⁻¹)⁻¹ = x.val := by group
    rw [e]
    exact Subgroup.mem_zpowers x.val
  have hmem' : y * x.val * y⁻¹ ∈ conjSubgroup (Subgroup.zpowers x.val) y⁻¹ ⊓ V :=
    Subgroup.mem_inf.2 ⟨hmem, hUV hyx⟩
  rw [h22, Subgroup.mem_bot] at hmem'
  apply hx1
  have e : x.val = y⁻¹ * (y * x.val * y⁻¹) * y := by group
  rw [e, hmem']
  group

theorem le_rStarMV_of_forall_rk_imgTil_le_bot (M : Subgroup G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {b c : ℕ} (hbc : b + c ≤ mSub V)
    (hb : ∀ U : Subgroup G, U ≤ V → ¬ normalizer (U : Set G) ≤ M →
      rk ↥(imgTil ⊥ V hV U) ≤ b) :
    (c : ℕ∞) ≤ rStarMV M V := by
  refine le_iInf fun U => le_iInf fun hU => ?_
  obtain ⟨hUV, hUN⟩ := hU
  have hinf : U ⊓ (⊥ : Subgroup G) = ⊥ := inf_bot_eq U
  have hmU : mSub U = rk ↥(imgTil ⊥ V hV U) := by
    have h1 := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V U hV hUV
    rw [hinf] at h1
    simpa [mSub, rk] using h1
  have hq := mSub_eq_mQuot_add V U hV hUV
  have hbU := hb U hUV hUN
  exact_mod_cast (by omega : c ≤ E3.mQuot V U)

theorem OmegaFourSetting.four_le_rStarMV (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) : (4 : ℕ∞) ≤ rStarMV D.M V := by
  have hP : PairFacts D.M ⊥ V := h.hyp125.pairFacts
  have hW2 : ∀ w : Vtil ⊥ V hV, w ^ 2 = 1 := fun w => by
    rw [pow_two]
    exact S.mul_self_eq_one w
  have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [h.card_K]; norm_num
  have hrk8 : mSub V = 8 := by
    have h1 := rk_top_vtil_add_mSub ⊥ V hV hP.le
    rw [rk_top, rk, S.card_eq, h.card_K] at h1
    have h0 : mSub (⊥ : Subgroup G) = 0 := rk_bot
    rw [h0] at h1
    have h2 : padicValNat 2 ((4 : ℕ) ^ 4) = 8 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, padicValNat.prime_pow]
      norm_num
    omega
  refine le_rStarMV_of_forall_rk_imgTil_le_bot D.M hV (b := 4) (c := 4) (by omega) ?_
  intro U hUV hUN
  have hsing : ∀ u ∈ imgTil ⊥ V hV U, S.Q u = 0 := fun u hu =>
    h.Q_eq_zero_of_mem_imgTil_of_normalizer_bot D h61 hext hSg h1219 hUV hUN hu
  have hcard := S.card_le_of_totallySingular hsing
  rw [card_eq_two_pow hW2 (imgTil ⊥ V hV U), hSK2, ← pow_mul] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hcard

theorem OmegaFourSetting.lt_rStarMV (D : Data G) (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) : (2 : ℕ∞) < rStarMV D.M V :=
  lt_of_lt_of_le (by norm_num) (h.four_le_rStarMV D h61 hext hSg h1219)

theorem OmegaFourSetting.calOStar_two_nonempty (D : Data G) (h61 : UC6.R6_1 D)
    (hext : DataExt D) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) (hw : W3Lem612 G)
    (hnc : ¬ centralizer (E3.cClos V 2 D.T : Set G) ≤ D.M) :
    (calOStar 2 D.M ⊥ V).Nonempty := by
  have hexA : ∃ A ∈ E3.gammaSet V 2 D.T, ¬ A ≤ centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hnc
    refine centralizer_cClos_le_of_commutator_eq_bot D h.hyp125 ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (E3.wClos_le_of_forall hcon)
  obtain ⟨A, hAT, hAc⟩ := hexA
  obtain ⟨hAT', g, hAg, hAm⟩ := hAT
  have hAM : A ≤ D.M := hAT'.trans D.sylowM.le
  have hAB : A ≤ BOf D.M V g := le_inf hAg hAM
  have hh : C33Hyp D.M V g :=
    ⟨by have := E3.mQuot_mono (V := conjSubgroup V g) hAB; omega,
      fun h' => hAc (hAB.trans h')⟩
  have hSet : C33Setting D.M V := h.c33Setting D h61 hSg h1219 hext
  have hr : (2 : ℕ∞) < rStarMV D.M V := h.lt_rStarMV D h61 hext hSg h1219
  exact ⟨conjSubgroup V g, g, rfl,
    hw (c33_hyp612 geoDichotomy_holds hSet hh hr) (c33_h3 (hSet.conj g) g⁻¹)⟩

theorem OmegaFourSetting.barSub_BOf_mem_aSet_two_gen (D : Data G)
    (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    {V : Subgroup G} {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {n : ℕ} (hn : n + 2 ≤ 4) {g : G}
    (hO : InCalOStar n D.M ⊥ V g) :
    barSub ⊥ V hV (BOf D.M V g) ≠ ⊥ ∧
      barSub ⊥ V hV (BOf D.M V g) ∈ E3.aSet 2 (Mbar D.M ⊥ V hV) := by
  have h64 : Hyp64 n D.M ⊥ V g := hyp64_of_hyp125 h.hyp125 hO
  have h64' : Hyp64 n D.M ⊥ V g := { h64 with elemAbelian := hV }
  have hA1 : barSub ⊥ V hV (BOf D.M V g) ≠ ⊥ := barSub_BOf_ne_bot_uncond h64'
  refine ⟨hA1, ?_⟩
  obtain ⟨hδ, hr⟩ := r16_35 D h61 hext h
  set B : Subgroup G := BOf D.M V g with hBdef
  have hi' : E3.mQuot (conjSubgroup V g) B ≤ n := by
    have h1 : E3.mQuot (conjSubgroup V g) B = E3.mQuot (conjSubgroup V g) D.M := by
      unfold E3.mQuot
      rw [hBdef, BOf, inf_comm, Subgroup.inf_relIndex_right]
    rw [h1]
    exact hO.1.2.2.1
  have hBγ : B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) D.M :=
    ⟨inf_le_right, g, inf_le_left, rfl⟩
  have hrk : ((2 + E3.mQuot (conjSubgroup V g) B : ℕ) : ℕ∞) ≤ rMV D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + E3.mQuot (conjSubgroup V g) B ≤ 4)) hr
  have hδ2 : ((2 + E3.mQuot (conjSubgroup V g) B : ℕ) : ℕ∞) ≤ deltaInf D.M V :=
    le_trans (by exact_mod_cast (by omega : 2 + E3.mQuot (conjSubgroup V g) B ≤ 4)) hδ
  exact h.barSub_mem_calABar_of_gammaSet D hSg h1219 hext hrk hδ2 hBγ hA1

theorem OmegaFourSetting.r38_mQuot_UOf_eq_bot (D : Data G)
    (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {n : ℕ} (hn : n + 2 ≤ 4) {g : G}
    (hO : InCalOStar n D.M ⊥ V g) : E3.mQuot V (UOf D.M V g) = 2 := by
  have h64 : Hyp64 n D.M ⊥ V g := hyp64_of_hyp125 h.hyp125 hO
  have h64' : Hyp64 n D.M ⊥ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hB := h.barSub_BOf_mem_aSet_two_gen D h61 hext hSg h1219 hn hO
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (⊥ : Subgroup G) := h64'.le_normalizer₀
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ BOf D.M V g, b ∉ F11.CTilde D.M ⊥ V := by
    by_contra hcon
    push Not at hcon
    exact hB.1 ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hcon)
  have hbs : b ∈ stabTil ⊥ V := (inf_le_right.trans (le_stabTil hM hM₀)) hbB
  let β : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨b, hbs⟩
  have hβ : β ∈ barSub ⊥ V hV (BOf D.M V g) := actTil_mem_barSub ⊥ V hV hbB hbs
  have hX : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil ⊥ V hV))) := h.le_normalizer
  have hU : ∀ w : Vtil ⊥ V hV, w ∈ imgTil ⊥ V hV (UOf D.M V g) ↔
      w * (β w)⁻¹ ∈ fixV (barSub ⊥ V hV (BOf D.M V g)) :=
    fun w => mem_imgTil_UOf_iff h64' hgen hbB hbC hbs w
  obtain ⟨k, hk⟩ := OmegaModel.card_eq_mul_pow_of_aSet S hX hB.2 hβ hU
  have hcardU : Nat.card (imgTil ⊥ V hV (UOf D.M V g)) *
      (imgTil ⊥ V hV (UOf D.M V g)).index = Nat.card (Vtil ⊥ V hV) :=
    Subgroup.card_mul_index _
  have hidx_eq : (imgTil ⊥ V hV (UOf D.M V g)).index = Nat.card S.K ^ k := by
    have hUpos : 0 < Nat.card (imgTil ⊥ V hV (UOf D.M V g)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hUpos (by rw [hcardU, hk])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSK2 : Nat.card S.K = 2 ^ 2 := by rw [h.card_K]; norm_num
  have hmQuot : E3.mQuot V (UOf D.M V g) = 2 * k := by
    rw [mQuot_UOf_eq_rkIdx h64' hgen, rkIdx, hidx_eq, hSK2, ← pow_mul,
      padicValNat.prime_pow]
  have hmk_le_n : 2 * k ≤ n := by
    have h1 := mQuot_UOf_le hO
    rwa [hmQuot] at h1
  have hk_lt2 : k < 2 := by
    have h1 : 2 * k < 2 * 2 := by omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have hk_ne0 : k ≠ 0 := by
    intro hk0
    apply imgTil_UOf_ne_top h64' hgen
    rw [← Subgroup.index_eq_one, hidx_eq, hk0, pow_zero]
  have hk1 : k = 1 := by omega
  rw [hmQuot, hk1, mul_one]

theorem fixV_barSub_BOf_eq_imgTil_NOf_bot {n : ℕ} {M V : Subgroup G} {g : G}
    (h : Hyp64 n M ⊥ V g) (hgen : GenHyp M V g) :
    fixV (barSub ⊥ V h.elemAbelian (BOf M V g)) =
      imgTil ⊥ V h.elemAbelian (NOf M V g) := by
  have hNV : NOf M V g ≤ V := inf_le_left.trans inf_le_left
  have h1 := imgTil_preTil ⊥ V h.elemAbelian (fixV (barSub ⊥ V h.elemAbelian (BOf M V g)))
  rw [preTil_fixV_barSub_BOf h hgen, imgTil_sup_V₀ h.elemAbelian hNV h.le] at h1
  exact h1.symm

theorem OmegaFourSetting.r38_fixV_line_bot (D : Data G)
    (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {n : ℕ} (hn : n + 2 ≤ 4) {g : G}
    (hO : InCalOStar n D.M ⊥ V g) :
    ∃ e : Vtil ⊥ V hV, e ≠ 1 ∧ S.Q e = 0 ∧
      ∀ w : Vtil ⊥ V hV, w ∈ fixV (barSub ⊥ V hV (BOf D.M V g)) ↔
        ∃ c : S.K, w = S.smul c e := by
  have h64 : Hyp64 n D.M ⊥ V g := hyp64_of_hyp125 h.hyp125 hO
  have h64' : Hyp64 n D.M ⊥ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hB := h.barSub_BOf_mem_aSet_two_gen D h61 hext hSg h1219 hn hO
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (⊥ : Subgroup G) := h64'.le_normalizer₀
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ BOf D.M V g, b ∉ F11.CTilde D.M ⊥ V := by
    by_contra hcon
    push Not at hcon
    exact hB.1 ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hcon)
  have hbs : b ∈ stabTil ⊥ V := (inf_le_right.trans (le_stabTil hM hM₀)) hbB
  let β : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨b, hbs⟩
  have hβ : β ∈ barSub ⊥ V hV (BOf D.M V g) := actTil_mem_barSub ⊥ V hV hbB hbs
  have hX : Mbar D.M ⊥ V hV ≤
      Subgroup.normalizer (S.omega : Set (MulAut (Vtil ⊥ V hV))) := h.le_normalizer
  have hU : ∀ w : Vtil ⊥ V hV, w ∈ imgTil ⊥ V hV (UOf D.M V g) ↔
      w * (β w)⁻¹ ∈ fixV (barSub ⊥ V hV (BOf D.M V g)) :=
    fun w => mem_imgTil_UOf_iff h64' hgen hbB hbC hbs w
  have hFE : fixV (barSub ⊥ V hV (BOf D.M V g)) = imgTil ⊥ V hV (NOf D.M V g) :=
    fixV_barSub_BOf_eq_imgTil_NOf_bot h64' hgen
  have hVgC : conjSubgroup V g ≤ Subgroup.centralizer (NOf D.M V g : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hV g) hy.2.1 hx
  have hUC : ¬ Subgroup.centralizer (NOf D.M V g : Set G) ≤ D.M := fun hle =>
    hO.1.1.1 (hVgC.trans hle)
  have hsing : ∀ x ∈ fixV (barSub ⊥ V hV (BOf D.M V g)), S.Q x = 0 := by
    intro x hx
    have hxN : x ∈ imgTil ⊥ V hV (NOf D.M V g) := by
      rw [← hFE]
      exact hx
    exact Q_eq_zero_of_mem_imgTil_bot D h61 hext h hUC hxN
  exact OmegaModel.exists_singular_line_of_fixV S hX hB.2 hβ hU
    (imgTil_UOf_ne_top h64' hgen) hsing

theorem OmegaFourSetting.r38_exists_aut_bot (D : Data G)
    (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {n : ℕ} (hn : n + 2 ≤ 4) {g : G}
    (hO : InCalOStar n D.M ⊥ V g) :
    ∃ a : MulAut (Vtil ⊥ V hV), a ∈ Mbar D.M ⊥ V hV ∧ a ^ 3 = 1 ∧
      ∀ w : Vtil ⊥ V hV, a w = w ↔ w ∈ fixV (barSub ⊥ V hV (BOf D.M V g)) := by
  have h64 : Hyp64 n D.M ⊥ V g := hyp64_of_hyp125 h.hyp125 hO
  have h64' : Hyp64 n D.M ⊥ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (⊥ : Subgroup G) := h64'.le_normalizer₀
  obtain ⟨Y, hYtor⟩ := exists_isFixedPointFreeTorus h64'
  have hYcard : Nat.card Y = 3 := by
    rw [hYtor.1.2.1, h.r38_mQuot_UOf_eq_bot D h61 hext hSg h1219 hn hO]
    norm_num
  have hYgt1 : 1 < Nat.card Y := by rw [hYcard]; norm_num
  have hYne : Y ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot Y).1 hYgt1
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYne
    exact ⟨y, y.2, fun h' => hy (Subtype.ext h')⟩
  have hYM : Y ≤ D.M :=
    fun z hz => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hYtor.1.1 hz)).1).2
  have hys : y ∈ stabTil ⊥ V := le_stabTil hM hM₀ (hYM hyY)
  let a : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨y, hys⟩
  have haM : a ∈ Mbar D.M ⊥ V hV := actTil_mem_barSub ⊥ V hV (hYM hyY) hys
  have hYs : Y ≤ stabTil ⊥ V := hYM.trans (le_stabTil hM hM₀)
  have haY : a ∈ barSub ⊥ V hV Y := actTil_mem_barSub ⊥ V hV hyY hys
  have haq : a ^ 3 = 1 := by
    have h1 := barSub_pow_card (V₀ := ⊥) (V := V) (Y := Y) hV hYs a haY
    rwa [hYcard] at h1
  have hyq : y ^ 3 = 1 := by
    have hmem : (⟨y, hyY⟩ : ↥Y) ^ Nat.card Y = 1 := pow_card_eq_one'
    have h1 : y ^ Nat.card Y = 1 := by
      have h' := congrArg (fun z : ↥Y => (z : G)) hmem
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h'
      exact h'
    rwa [hYcard] at h1
  refine ⟨a, haM, haq, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    obtain ⟨v, hv_eq, hv_fix⟩ := exists_fixed_lift_of_pow_eq_one hV hys (by norm_num : Odd 3)
      hyq (show actTil ⊥ V hV ⟨y, hys⟩ w = w from hw)
    have hvN : v.val ∈ NOf D.M V g := hYtor.2 y hyY hy1 v.val v.val_mem hv_fix
    have hmem : mkTil ⊥ V hV v ∈ imgTil ⊥ V hV (NOf D.M V g) :=
      (mem_imgTil ⊥ V hV (NOf D.M V g) (mkTil ⊥ V hV v)).2 ⟨v, hvN, rfl⟩
    rw [← hv_eq]
    exact imgTil_NOf_le_fixV_barSub h64' hmem
  · intro hw
    exact barSub_fixes_fixV_BOf h64' hgen hYtor.1.1 a haY w hw

theorem OmegaFourSetting.exists_order_three_fix_line (D : Data G)
    (h61 : UC6.R6_1 D) (hext : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} {S : OmegaModel (Vtil ⊥ V hV)}
    (h : OmegaFourSetting D V hV S) {g : G} (hO : InCalOStar 2 D.M ⊥ V g) :
    ∃ a : MulAut (Vtil ⊥ V hV), a ∈ Mbar D.M ⊥ V hV ∧ a ^ 3 = 1 ∧
      ∃ e : Vtil ⊥ V hV, e ≠ 1 ∧ S.Q e = 0 ∧
        ∀ w : Vtil ⊥ V hV, a w = w ↔ ∃ c : S.K, w = S.smul c e := by
  obtain ⟨a, haM, haq, hafix⟩ :=
    h.r38_exists_aut_bot D h61 hext hSg h1219 (n := 2) (by norm_num) hO
  obtain ⟨e, he1, heQ, hline⟩ :=
    h.r38_fixV_line_bot D h61 hext hSg h1219 (n := 2) (by norm_num) hO
  exact ⟨a, haM, haq, e, he1, heQ, fun w => (hafix w).trans (hline w)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
