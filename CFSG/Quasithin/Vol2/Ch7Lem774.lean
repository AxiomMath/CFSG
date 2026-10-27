module

public import CFSG.Quasithin.Vol2.Ch7Sec77Setup
public import CFSG.Quasithin.Vol2.Ch7Fano
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11
public import CFSG.Quasithin.Background.HSL3Orb

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable (S : Setup T L I)
include S

theorem card_fsuV : Nat.card (fsuV T I) = 64 := by
  obtain ⟨e, -, -⟩ := S.exists_model
  have h : Nat.card (IntMod (fsuV T I) S.hV) = Nat.card (PairMod (ZMod 2)) :=
    Nat.card_congr e.toEquiv
  rw [SL3One.card_pairMod_two card_zmod_two] at h
  exact h

theorem card_eq_eight {J : Subgroup G} (hJV : J ≤ fsuV T I)
    (hJL : L ≤ Subgroup.normalizer (J : Set G)) (hJ1 : J ≠ ⊥) (hJV' : J ≠ fsuV T I) :
    Nat.card J = 8 := by
  obtain ⟨e, he, -⟩ := S.exists_model
  set J' := (intSub S.hV J).map e.toMonoidHom with hJ'
  have hinv : Pair.IsInv (pairSL (ZMod 2)) J' := by
    rintro y hy _ ⟨w, hw, rfl⟩
    rw [← he] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨g, hgL, rfl⟩ := (mem_autI S.hV).1 hx
    refine ⟨convI S.hV g w, ?_, ?_⟩
    · change (convI S.hV g w).val ∈ J
      rw [convI_apply_val]
      have hgL' : (g : G) ∈ L := by rw [S.hL]; exact hgL
      have hw' : w.val ∈ J := hw
      exact (Subgroup.mem_normalizer_iff.mp (hJL hgL') _).mp hw'
    · change e (convI S.hV g w) = e ((convI S.hV g) (e.symm (e w)))
      rw [MulEquiv.symm_apply_apply]
  have hcard : Nat.card J' = Nat.card J := by
    rw [Subgroup.card_map_of_injective e.injective, ← Subgroup.card_map_of_injective
      (valHom_injective S.hV), map_valHom_intSub S.hV hJV]
  rcases SL3One.isInv_eq hinv with h | h | h | h
  · exfalso
    apply hJ1
    rw [h, Subgroup.card_bot] at hcard
    exact Subgroup.card_eq_one.mp hcard.symm
  · rw [← hcard, h]
    exact SL3One.card_V₁_two card_zmod_two
  · rw [← hcard, h]
    exact SL3One.card_V₂_two card_zmod_two
  · exfalso
    apply hJV'
    rw [h, Subgroup.card_top, SL3One.card_pairMod_two card_zmod_two] at hcard
    exact Subgroup.eq_of_le_of_card_ge hJV (by rw [← hcard, S.card_fsuV]; norm_num)

theorem pCoreOf_L_le : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 L)
    exact sup_le (le_normalizer_pCoreOf 2 L)
      (S.T_le_normalizer_L.trans (normalizer_le_normalizer_pCoreOf 2 L))
  have hQ : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    have h := S.hQ
    rwa [S.fsuL0_eq] at h
  exact hQL.trans (hQ ▸ inf_le_right)

theorem card_quot (hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
  obtain ⟨e, he, -⟩ := S.exists_model
  set φ := convHom S.hV L S.L_le_normalizer_V with hφ
  have hker : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [ker_convHom, Subgroup.mem_subgroupOf]
    refine ⟨x.2, S.pCoreOf_L_le ⟨x, ?_, rfl⟩⟩
    exact hx
  set ψ := QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hker with hψ
  have hrange : ψ.range = autI S.hV L := by
    rw [← range_convHom S.hV L S.L_le_normalizer_V]
    apply le_antisymm
    · rintro _ ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : ↥L ⧸ CFSG.pCore 2 ↥L), rfl⟩
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases hs.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      apply S.fsuV_ne_bot
      rw [S.eq_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : φ ⟨l, hl⟩ = 1 := by
        have : ((⟨l, hl⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ ψ.ker := by rw [h]; exact trivial
        exact this
      rw [convHom_apply, convI_eq_one_iff] at h1
      exact (Subgroup.mem_centralizer_iff.mp h1 v hv).symm
  have hL : autI S.hV L = autI S.hV (fsuL0 T L) := by rw [← S.hL]
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hrange, hL,
    ← card_map_congrHom e, he]
  exact SL3One.card_pairSL card_zmod_two

theorem relIndex_le_three {Y : Subgroup G} (hYM : Y ≤ fsuM T L) (hYo : Odd (Nat.card Y))
    {z : G} (hzV : z ∈ fsuV T I) (hz1 : z ≠ 1)
    (hYz : Y ≤ Subgroup.centralizer ({z} : Set G)) :
    (Y ⊓ Subgroup.centralizer (fsuV T I : Set G)).relIndex Y ≤ 3 := by
  classical
  obtain ⟨e, -, hMe⟩ := S.exists_model
  have hYN : Y ≤ Subgroup.normalizer (fsuV T I : Set G) := hYM.trans S.hMN
  rw [← card_autI_eq S.hV hYN]
  have hdvd : Nat.card (autI S.hV Y) ∣ Nat.card Y :=
    Dvd.intro _ (card_autI_mul_card_inf S.hV hYN)
  have hodd : Odd (Nat.card (autI S.hV Y)) := Odd.of_dvd_nat hYo hdvd
  rw [← card_map_congrHom e (autI S.hV Y)]
  rw [← card_map_congrHom e (autI S.hV Y)] at hodd
  set Y' := (autI S.hV Y).map (congrHom e) with hY'
  have hY'N : Y' ≤ pairNorm (ZMod 2) := (Subgroup.map_mono (autI_mono S.hV le_top)).trans hMe
  have hY'L : Y' ≤ pairSL (ZMod 2) := fun y hy => by
    have hpow : y ^ Nat.card Y' = 1 := by
      have h := pow_card_eq_one' (G := ↥Y') (x := ⟨y, hy⟩)
      exact congrArg Subtype.val h
    exact SL3One.mem_pairSL_of_odd card_zmod_two (hY'N hy) hodd hpow
  have h168 : Nat.card Y' ∣ 2 ^ 3 * 21 := by
    rw [show (2 : ℕ) ^ 3 * 21 = 168 by norm_num, ← SL3One.card_pairSL card_zmod_two]
    exact Subgroup.card_dvd_of_le hY'L
  set z' : PairMod (ZMod 2) := e (IntMod.mk S.hV ⟨z, hzV⟩) with hz'
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    have h2 : IntMod.mk S.hV ⟨z, hzV⟩ = 1 := e.injective (h.trans e.map_one.symm)
    exact congrArg IntMod.val h2
  have hfix : ∀ y ∈ Y', y z' = z' := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hgY, rfl⟩ := (mem_autI S.hV).1 hx
    change e (convI S.hV g (e.symm z')) = z'
    rw [hz', MulEquiv.symm_apply_apply]
    congr 1
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hYz hgY)
    change (g : G) * z * (g : G)⁻¹ = z
    rw [h, mul_inv_cancel_right]
  have h7 : ¬ 7 ∣ Nat.card Y' := by
    intro h7
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y') 7 h7
    obtain ⟨g, hg⟩ := SL3One.exists_rho_of_mem (hY'L y.2)
    have hord : orderOf (SL3One.rho g) = 7 := by
      rw [hg]
      exact (Subgroup.orderOf_coe y).trans hy
    have hg7 : g ^ 7 = 1 := SL3One.rho_injective (by
      rw [map_pow, map_one, ← hord, pow_orderOf_eq_one])
    have hg1 : g ≠ 1 := fun h1 => by
      rw [h1, map_one, orderOf_one] at hord
      norm_num at hord
    have hfz : SL3One.rho g z' = z' := by rw [hg]; exact hfix y y.2
    have h1 : act g (Multiplicative.toAdd z'.1) = Multiplicative.toAdd z'.1 := by
      rw [← rho_fst, hfz]
    have h2 : dact g (Multiplicative.toAdd z'.2) = Multiplicative.toAdd z'.2 := by
      rw [← rho_snd, hfz]
    have e1 := fix_seven g ⟨hg7, hg1⟩ _ h1
    have e2 := dfix_seven g ⟨hg7, hg1⟩ _ h2
    exact hz'1 (Prod.ext (Multiplicative.toAdd.injective e1) (Multiplicative.toAdd.injective e2))
  have hcop8 : Nat.Coprime (Nat.card Y') (2 ^ 3) :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hodd)
  have h21 : Nat.card Y' ∣ 3 * 7 := hcop8.dvd_of_dvd_mul_left h168
  have hcop7 : Nat.Coprime (Nat.card Y') 7 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7)
  exact Nat.le_of_dvd (by norm_num) (hcop7.dvd_of_dvd_mul_right h21)

theorem L_le_normalizer_conj {t : G} (htT : t ∈ T) :
    L ≤ Subgroup.normalizer (CFSG.conjugate I t : Set G) := by
  intro l hl
  have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L htT) l).mp hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjugate_iff', mem_conjugate_iff']
  have key := Subgroup.mem_normalizer_iff.mp (S.L_le_normalizer_I hl') (t * x * t⁻¹)
  have e1 : t * (l * x * l⁻¹) * t⁻¹ = (t * l * t⁻¹) * (t * x * t⁻¹) * (t * l * t⁻¹)⁻¹ := by group
  rw [e1]
  exact key

theorem conjugate_ne_bot (t : G) : CFSG.conjugate I t ≠ ⊥ := by
  intro h
  apply S.hyp.fsu.irrPlus.2.1
  rw [eq_bot_iff]
  intro x hx
  have hx' : t⁻¹ * x * t ∈ CFSG.conjugate I t := by
    rw [mem_conjugate_iff']
    simpa [mul_assoc] using hx
  rw [h, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot]
  calc x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    _ = 1 := by rw [hx']; group

theorem not_fanoCore [IsMulCommutative ↥(fsuV T I)] :
    ¬ FanoCoreModule (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ := by
  intro hfano
  obtain ⟨t, htT, hsup, hinf, -⟩ := S.exists_twist
  have hIV : I ≤ fsuV T I := le_fsuV I T
  have hItV : CFSG.conjugate I t ≤ fsuV T I := by
    rw [← hsup]
    exact le_sup_right
  have hI1 : I ≠ ⊥ := S.hyp.fsu.irrPlus.2.1
  have hIt1 := S.conjugate_ne_bot t
  have hIneV : I ≠ fsuV T I := fun h => hIt1 (by
    rw [eq_bot_iff, ← hinf]
    exact le_inf (hItV.trans h.ge) le_rfl)
  have hItneV : CFSG.conjugate I t ≠ fsuV T I := fun h => hI1 (by
    rw [eq_bot_iff, ← hinf]
    exact le_inf le_rfl (hIV.trans h.ge))
  have h8 := S.card_eq_eight hIV S.L_le_normalizer_I hI1 hIneV
  have h8' := S.card_eq_eight hItV (S.L_le_normalizer_conj htT) hIt1 hItneV
  have hinv : ∀ {J : Subgroup G}, L ≤ Subgroup.normalizer (J : Set G) →
      Pair.IsInv (autOn L (fsuV T I)) (J.subgroupOf (fsuV T I)) := by
    intro J hJL x hx w hw
    obtain ⟨g, hgL, rfl⟩ := (mem_autI S.hV).1 hx
    rw [Subgroup.mem_subgroupOf]
    have h1 := convI_apply_val S.hV g w
    change (convI S.hV g w).val ∈ J
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp (hJL hgL) _).mp hw
  have hXc : Nat.card (I.subgroupOf (fsuV T I)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIV).toEquiv, h8]
  have hYc : Nat.card ((CFSG.conjugate I t).subgroupOf (fsuV T I)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hItV).toEquiv, h8']
  have heq := Fano.FanoCoreModule.eq_of_card_eight hfano (hinv S.L_le_normalizer_I)
    (hinv (S.L_le_normalizer_conj htT)) hXc hYc
  have hII : I = CFSG.conjugate I t := by
    have := congrArg (Subgroup.map (fsuV T I).subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hIV, Subgroup.map_subgroupOf_eq_of_le hItV] at this
  apply hI1
  rw [eq_bot_iff, ← hinf]
  exact le_inf le_rfl hII.le

theorem normalizer_le (h443 : Stmt4_4_3Orbit') {B : Subgroup G} (hBM : B ≤ fsuM T L)
    (hBV : B ≤ Subgroup.centralizer (fsuV T I : Set G)) (hB1 : B ≠ ⊥)
    (hBc : IsMulCommutative ↥B) (hBo : Odd (Nat.card B)) :
    Subgroup.normalizer (B : Set G) ≤ fsuM T L := by
  have hVLT : fsuV T I ≤ L ⊔ T := by
    have h := S.hVLT
    rwa [S.fsuL0_eq] at h
  have hRed : IsPrimeReduced 2 ((fsuV T I).subgroupOf (L ⊔ T)) := by
    have h := S.hRed
    rwa [S.fsuL0_eq] at h
  have hH := remark_4_4_2 S.hyp.fsu.simple S.hyp.fsu.nonabelian S.hyp.fsu.qtke S.hyp.fsu.sylow
    S.uniq.1.1 S.T_le_fsuM S.hyp.fsu.maximal S.hyp.fsu.faithful S.L_le_fsuM
    S.hyp.fsu.quasisimple S.fsuM_le_normalizer_L hVLT hRed S.eq_commutator S.fsuV_ne_bot hBM hBV
    hB1 hBc hBo
  rcases stmt4_4_3Orbit_iff'.mp h443 G T (fsuM T L) L B ⊥ (fsuV T I) hH with h | ⟨-, -, hcases⟩
  · exact h
  · exfalso
    rcases hcases with ⟨⟨hc, hFF⟩, -⟩ | ⟨m, hm1, hm, -⟩ | ⟨-, hc, hfano⟩
    ·
      apply not_isFFModule_of_hyp702 S.hyp S.hV S.hNM
      obtain ⟨A, hA, hA1, hA2, hcard⟩ := hFF
      exact ⟨A, hA.trans (autI_mono S.hV le_top), hA1, hA2, hcard⟩
    ·
      have h168 := S.card_quot (isSimpleGroup_of_lieModel_PSL2 hm)
      rw [Lem11.card_of_lieModel_psl_two hm] at h168
      rcases (show 2 * m = 2 ∨ 4 ≤ 2 * m by omega) with hk | hk
      · rw [hk] at h168
        norm_num at h168
      · have h1 : 2 ^ 4 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hk
        have h2 : 4 ^ 4 ≤ 4 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hk
        have h3 : 2 ^ 4 * (4 ^ 4 - 1) ≤ 2 ^ (2 * m) * (4 ^ (2 * m) - 1) :=
          Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
        rw [h168] at h3
        norm_num at h3
    ·
      exact S.not_fanoCore hfano

end Setup

end CFSG.Quasithin.H13.Sec77
