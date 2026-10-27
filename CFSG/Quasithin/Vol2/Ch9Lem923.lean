module

public import CFSG.Quasithin.Vol2.Ch9Lem922
public import CFSG.Quasithin.Vol2.Ch9Sec1Adapt
public import CFSG.Quasithin.Vol2.Ch9Sec2J
public import CFSG.Quasithin.Background.E6Twelve
public import CFSG.Quasithin.Vol2.Ch3Sec2Wreath

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.E3
open CFSG.Quasithin.H CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem isElemAbelian2_zpowers {W : Type*} [CommGroup W] {t : MulAut W} (ht : t ^ 2 = 1) :
    IsElemAbelian2 (Subgroup.zpowers t) :=
  CFSG.Quasithin.StabLat.isElemAbelian2_zpowers ht

namespace Setup

variable (S : Setup T L I n)
include S

theorem isTISetUnder : IsTISetUnder (fsuV T I) (fsuM T L) :=
  fun _ hg hgn => absurd (S.hMN hg) hgn

theorem hypE61 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) : E6.HypE61 T (fsuM T L) (fsuV T I) :=
  hypE61_of_tiA h37 h38 h39 (stmtFSUModule_of_eight h3228) h3228 S.hyp S.isTISetUnder

theorem inf_centralizer_le_of_index_two {U : Subgroup G} (hUV : U ≤ fsuV T I)
    (hU1 : mQuot (fsuV T I) U = 1) :
    fsuM T L ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  classical
  have hV2 : IsPGroup 2 ↥(fsuV T I) := S.isPGroup_fsuV
  have hidx : U.relIndex (fsuV T I) = 2 := by rw [relIndex_eq_two_pow hV2, hU1, pow_one]
  rintro m ⟨hmM, hmU⟩
  by_contra hmC
  have hmN := S.hMN hmM
  have hmV : ∀ v ∈ fsuV T I, m * v * m⁻¹ * v⁻¹ ∈ U := by
    intro v hv
    by_cases hvU : v ∈ U
    · rw [(Subgroup.mem_centralizer_iff.mp hmU v hvU).symm, mul_inv_cancel_right, mul_inv_cancel]
      exact U.one_mem
    · have hmv : m * v * m⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp hmN v).mp hv
      have hmvU : m * v * m⁻¹ ∉ U := by
        intro h
        apply hvU
        have h2 := Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hmU) _ h
        have h3 : v = m * v * m⁻¹ := by
          calc v = m⁻¹ * (m * v * m⁻¹) * m := by group
            _ = ((m * v * m⁻¹) * m⁻¹) * m := by rw [h2]
            _ = m * v * m⁻¹ := by group
        rw [h3]
        exact h
      have hUsub : (U.subgroupOf (fsuV T I)).index = 2 := hidx
      have := (Subgroup.mul_mem_iff_of_index_two hUsub (a := ⟨m * v * m⁻¹, hmv⟩)
        (b := (⟨v, hv⟩ : ↥(fsuV T I))⁻¹)).mpr
        (iff_of_false (fun h => hmvU (Subgroup.mem_subgroupOf.mp h))
          (fun h => hvU (by simpa using Subgroup.mem_subgroupOf.mp h)))
      simpa using Subgroup.mem_subgroupOf.mp this
  have hm2 : m ^ 2 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    set w := m * v * m⁻¹ * v⁻¹ with hw
    have hwU := hmV v hv
    have hwm : m * w * m⁻¹ = w := by
      rw [← (Subgroup.mem_centralizer_iff.mp hmU w hwU)]
      group
    have hw2 : w * w = 1 := by
      have := S.hV.2 w (hUV hwU)
      rwa [pow_two] at this
    have hvw : m * v * m⁻¹ = w * v := by rw [hw]; group
    have e : m ^ 2 * v * (m ^ 2)⁻¹ = v := by
      calc m ^ 2 * v * (m ^ 2)⁻¹ = m * (m * v * m⁻¹) * m⁻¹ := by rw [pow_two]; group
        _ = m * (w * v) * m⁻¹ := by rw [hvw]
        _ = (m * w * m⁻¹) * (m * v * m⁻¹) := by group
        _ = w * (w * v) := by rw [hwm, hvw]
        _ = v := by rw [← mul_assoc, hw2, one_mul]
    calc v * m ^ 2 = (m ^ 2 * v * (m ^ 2)⁻¹) * m ^ 2 := by rw [e]
      _ = m ^ 2 * v := by group
  have hZN : Subgroup.zpowers m ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    Subgroup.zpowers_le.mpr hmN
  have hZU : U ≤ fsuV T I ⊓ Subgroup.centralizer (Subgroup.zpowers m : Set G) := by
    refine le_inf hUV fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left (Subgroup.mem_centralizer_iff.mp hmU u hu).symm k)).eq
  have hBe : IsElemAbelian2 (autI S.hV (Subgroup.zpowers m)) := by
    refine isElemAbelian2_autI_of_comm S.hV (fun b hb b' hb' => ?_) (fun b hb => ?_)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
      rw [((Commute.refl m).zpow_zpow k k').eq, mul_inv_cancel_right, mul_inv_cancel]
      exact Subgroup.one_mem _
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ hm2 _
  have hB1 : autI S.hV (Subgroup.zpowers m) ≠ ⊥ := by
    rw [Ne, autI_eq_bot_iff S.hV hZN]
    exact fun h => hmC (h (Subgroup.mem_zpowers m))
  have hrk1 : 1 ≤ rk ↥(autI S.hV (Subgroup.zpowers m)) := hBe.rk_pos hB1
  have hfix : rkIdx (fixV (autI S.hV (Subgroup.zpowers m))) ≤ 1 := by
    rw [E3.rkIdx_fixV_autI S.hV hZN, ← hU1]
    unfold mQuot
    have h1 : (fsuV T I ⊓ Subgroup.centralizer (Subgroup.zpowers m : Set G)).relIndex
        (fsuV T I) ≤ U.relIndex (fsuV T I) :=
      Subgroup.relIndex_le_of_le_left hZU (D15Proof.relIndex_ne_zero _ _)
    rw [relIndex_eq_two_pow hV2, relIndex_eq_two_pow hV2] at h1
    unfold mQuot at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  exact not_isFFModule_of_hyp702A S.hyp S.hV S.hNM ⟨autI S.hV (Subgroup.zpowers m),
    autI_mono S.hV le_top, hB1, hBe, (B1.card_le_iff IntMod.sq_eq_one hBe).mpr (by omega)⟩

theorem le_mParam (hH11 : Ch9InH11Plus) : n ≤ mParam (autI S.hV (fsuM T L)) := by
  classical
  unfold mParam
  split_ifs with heven
  · have hne : {k : ℕ | ∃ t ∈ autI S.hV (fsuM T L), orderOf t = 2 ∧
        k = rkIdx (fixV (Subgroup.zpowers t))}.Nonempty := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
      exact ⟨_, t, t.2, by rw [← Subgroup.orderOf_coe] at ht; exact ht, rfl⟩
    refine le_csInf hne fun k ⟨t, htM, ht2, hk⟩ => ?_
    have htt : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ht2
      exact absurd ht2 (by norm_num)
    have h := (S.h11 hH11 (Subgroup.zpowers_le.mpr htM) ((Subgroup.zpowers_ne_bot).mpr ht1)
      (isElemAbelian2_zpowers htt)).1
    have hrk : rk ↥(Subgroup.zpowers t) = 1 := by
      unfold rk
      rw [Nat.card_zpowers, ht2]
      exact padicValNat_self
    rw [hrk] at h
    omega
  · have := S.comm
    have hcard := Vol2.Ch10.SecA.card_fsuV_of_omegaPlus (h := S.row)
    unfold rk
    have : Nat.card (IntMod (fsuV T I) S.hV) = 2 ^ (4 * n) := hcard
    rw [this, padicValNat.prime_pow]
    omega

theorem two_le_rParam (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h1 : zQ T I = fsuV T I) :
    (2 : ℕ∞) ≤ rParam (fsuV T I) := by
  classical
  have hV2 : IsPGroup 2 ↥(fsuV T I) := S.isPGroup_fsuV
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hUV, hCU, hU1⟩ : ∃ U : Subgroup G, U ≤ fsuV T I ∧
      ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      mQuot (fsuV T I) U = 1 := by
    unfold rParam at hlt
    obtain ⟨U, hU⟩ := iInf_lt_iff.mp hlt
    obtain ⟨⟨hUV, hCU⟩, hU2⟩ := iInf_lt_iff.mp hU
    have hm : mQuot (fsuV T I) U < 2 := by exact_mod_cast hU2
    have hm0 : mQuot (fsuV T I) U ≠ 0 := by
      intro h0
      have := (mQuot_eq_zero_iff hV2 hUV).1 h0
      rw [this] at hCU
      exact hCU (Subgroup.centralizer_le_normalizer _)
    exact ⟨U, hUV, hCU, by omega⟩
  have hidx : U.relIndex (fsuV T I) = 2 := by rw [relIndex_eq_two_pow hV2, hU1, pow_one]
  obtain ⟨K, _, _, _, hK, e, ψ, hψs, hψ, hψT⟩ := S.exists_coord_adapted
  have hact : ∀ (k : ↥(fsuL0 T L)) (w : ↥(fsuV T I)),
      Om4.rho (ψ k) (e w) = e ⟨(k : G) * w * (k : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k.2) w).mp w.2⟩ := by
    intro k w
    rw [← hψ k, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    exact congrArg e (Subtype.ext (coe_conjAct_apply _ _ _))
  set UK : Subgroup (Om4.VM K) := (U.subgroupOf (fsuV T I)).map e.toMonoidHom with hUKdef
  have hUK : UK.index = 2 :=
    (Subgroup.index_map_equiv (H := U.subgroupOf (fsuV T I)) e).trans hidx
  obtain ⟨γ, P, hPB, hE11, hPinv, hPfix⟩ := exists_good_conj UK hUK
  obtain ⟨x, hx⟩ := hψs γ
  set U' := CFSG.conjugate U (x : G)⁻¹ with hU'def
  have hmem' : ∀ y : G, y ∈ U' ↔ (x : G)⁻¹ * y * x ∈ U := fun y => by
    rw [hU'def, Vol2.Ch10.SecA.mem_conjugate_iff, inv_inv]
  have hxV : (x : G) ∈ Subgroup.normalizer (fsuV T I : Set G) := S.L0_le_normalizer_V x.2
  have hU'V : U' ≤ fsuV T I := fun y hy => by
    have h2 := (Subgroup.mem_normalizer_iff.mp hxV _).mp (hUV ((hmem' y).mp hy))
    simpa [mul_assoc] using h2
  have hmemU' : ∀ w : ↥(fsuV T I), (w : G) ∈ U' ↔ e w ∈ UK.map (Om4.rho γ).toMonoidHom := by
    intro w
    have hw' : (x : G)⁻¹ * w * x ∈ fsuV T I := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) w).mp w.2
      simpa using this
    have h2 : Om4.rho γ (e ⟨_, hw'⟩) = e w := by
      rw [← hx, hact]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])
    rw [Subgroup.mem_map_equiv, hmem', ← h2, MulEquiv.symm_apply_apply, hUKdef,
      Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  have hU'1 : mQuot (fsuV T I) U' = 1 := by
    have hc : Nat.card ↥U' = Nat.card ↥U := Wr326.card_conjugate U _
    have e1 := Subgroup.relIndex_mul_card U (fsuV T I)
    have e2 := Subgroup.relIndex_mul_card U' (fsuV T I)
    rw [inf_of_le_left hUV] at e1
    rw [inf_of_le_left hU'V, hc] at e2
    have hpos : 0 < Nat.card ↥U := Nat.card_pos
    have : U'.relIndex (fsuV T I) = U.relIndex (fsuV T I) :=
      Nat.eq_of_mul_eq_mul_right hpos (e2.trans e1.symm)
    unfold mQuot
    rw [this]
    unfold mQuot at hU1
    exact hU1
  have hCU' : ¬ Subgroup.centralizer (U' : Set G) ≤ fsuM T L := by
    intro hle
    apply hCU
    intro c hc
    have hc' : (x : G) * c * (x : G)⁻¹ ∈ Subgroup.centralizer (U' : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h2 := Subgroup.mem_centralizer_iff.mp hc _ ((hmem' y).mp hy)
      calc y * ((x : G) * c * (x : G)⁻¹) = (x : G) * (((x : G)⁻¹ * y * x) * c) * (x : G)⁻¹ := by
            group
        _ = (x : G) * (c * ((x : G)⁻¹ * y * x)) * (x : G)⁻¹ := by rw [h2]
        _ = (x : G) * c * (x : G)⁻¹ * y := by group
    have h3 := S.hMN (hle hc')
    have h4 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxV) h3) hxV
    simpa [mul_assoc] using h4
  have hZU' : fsuV T I ⊓ Subgroup.centralizer (T : Set G) ≤ U' := by
    rintro z ⟨hzV, hzT⟩
    refine (hmemU' ⟨z, hzV⟩).mpr ?_
    have hfix : ∀ p ∈ (uni K).prod (uni K), Om4.rho p (e ⟨z, hzV⟩) = e ⟨z, hzV⟩ := by
      intro p hp
      rw [← hψT] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      rw [hact]
      congr 1
      refine Subtype.ext ?_
      show (t : G) * z * (t : G)⁻¹ = z
      rw [Subgroup.mem_centralizer_iff.mp hzT _ (Subgroup.mem_subgroupOf.mp ht).1,
        mul_inv_cancel_right]
    have h2 := fixV_rho_uni_prod hfix
    have h3 : e ⟨z, hzV⟩ =
        Multiplicative.ofAdd !![Multiplicative.toAdd (e ⟨z, hzV⟩) 0 0, 0; 0, 0] := by
      rw [← h2]
      rfl
    rw [h3]
    exact hE11 _
  set T₀ : Subgroup G := (P.comap ψ).map (fsuL0 T L).subtype ⊓ T with hT₀def
  have hT₀N : ∀ t ∈ T₀, ∀ y ∈ U', t * y * t⁻¹ ∈ U' := by
    rintro _ ⟨⟨k, hk, rfl⟩, -⟩ y hy
    have hyV := hU'V hy
    have h2 := (hmemU' ⟨y, hyV⟩).mp hy
    have h3 := hPinv (ψ k) hk _ h2
    rw [hact] at h3
    exact (hmemU' _).mpr h3
  have hT₀le : T₀ ≤ T ⊓ Subgroup.normalizer (U' : Set G) := by
    intro t ht
    refine ⟨ht.2, Subgroup.mem_normalizer_iff.mpr fun y => ⟨hT₀N t ht y, fun hy => ?_⟩⟩
    have h2 := hT₀N t⁻¹ (T₀.inv_mem ht) _ hy
    simpa [mul_assoc] using h2
  have hCT₀ : fsuV T I ⊓ Subgroup.centralizer (T₀ : Set G) ≤ U' := by
    rintro v ⟨hvV, hvC⟩
    refine (hmemU' ⟨v, hvV⟩).mpr (hPfix _ fun p hp => ?_)
    have hpB := hPB hp
    rw [← hψT] at hpB
    obtain ⟨t, ht, rfl⟩ := hpB
    have htT₀ : (t : G) ∈ T₀ := ⟨⟨t, hp, rfl⟩, (Subgroup.mem_subgroupOf.mp ht).1⟩
    rw [hact]
    congr 1
    refine Subtype.ext ?_
    show (t : G) * v * (t : G)⁻¹ = v
    rw [Subgroup.mem_centralizer_iff.mp hvC _ htT₀, mul_inv_cancel_right]
  have hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ T ⊓ Subgroup.normalizer (U' : Set G) :=
    fun q hq => ⟨hq.1, (Subgroup.centralizer_le_normalizer _)
      (Subgroup.centralizer_le hU'V hq.2)⟩
  have hΩ : omegaOneCenterOf (T ⊓ Subgroup.normalizer (U' : Set G)) ≤ U' :=
    (S.omegaOneCenter_le h1 hQN inf_le_left).trans
      ((inf_le_inf_left _ (Subgroup.centralizer_le hT₀le)).trans hCT₀)
  have hZne : fsuV T I ⊓ Subgroup.centralizer (T : Set G) ⊓ U' ≠ ⊥ := by
    rw [inf_eq_left.mpr hZU']
    intro h0
    apply fsuV_inf_omegaOneCenter_ne_bot S.hyp.fsu S.hV S.hN
    rw [eq_bot_iff, ← h0]
    exact inf_le_inf_left _ fun z hz => ((A4.omegaOneCenterOf_le_centerOf T hz).2)
  have hU'0 : U' ≠ ⊥ := fun h0 => hZne (by rw [h0, inf_bot_eq])
  have hΓ : U' ∈ E6.gammaE64 (fsuV T I) (fsuM T L) :=
    ⟨hU'V, hU'0, hCU', (E6.twoPrimeResidual_le_self' _).trans
      (le_inf inf_le_left (S.inf_centralizer_le_of_index_two hU'V hU'1))⟩
  exact hE610 G T (fsuM T L) (fsuV T I) U' (S.hypE61 h37 h38 h39 h3228) hΓ hU'1 (Or.inl hZne) hΩ

theorem le_rParam (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four) (h63 : ASInputs.AS_E_6_3)
    (hH11 : Ch9InH11Plus) (h1 : zQ T I = fsuV T I) : (n : ℕ∞) ≤ rParam (fsuV T I) := by
  rcases Nat.lt_or_ge 2 n with hn | hn
  · have hm := S.le_mParam hH11
    have h2 := (h63 G T (fsuM T L) (fsuV T I) S.hV (S.hypE61 h37 h38 h39 h3228) (by omega)).1
    exact le_trans (by exact_mod_cast hm) h2
  · have hn2 : n = 2 := le_antisymm hn S.two_le
    rw [hn2]
    exact S.two_le_rParam h37 h38 h39 h3228 hE610 h1

end Setup

end CFSG.Quasithin.H13.Ch9
