module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33FFI
public import CFSG.Quasithin.Vol2.Ch12Sec6L33FFS2
public import CFSG.Quasithin.Vol2.Ch12Sec6L33FFS3
public import CFSG.Quasithin.Vol2.Ch12Sec6L33FFS4
public import CFSG.Quasithin.Vol2.Ch12Sec6L33h

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin S126 Equiv CFSG.Quasithin.H13.A6.FFTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_t_notin_normalizer {T L H K : Subgroup G} (h2 : Case2 T L H K) :
    ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
  by_contra hcon
  push Not at hcon
  apply h2.1
  apply le_antisymm
  · apply conjClosure_le
    intro h hh z hz
    exact (Subgroup.mem_normalizer_iff.1 (hcon h hh) z).1 hz
  · exact le_conjClosure K T

theorem autOn_K0_eq_sup {T L H K A B : Subgroup G} (h2 : Case2 T L H K) {t : G} (ht : t ∈ T)
    (hKc : K ∈ cComp H) (hTH : T ≤ H) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hAH : H ≤ Subgroup.normalizer (A : Set G)) (hBH : H ≤ Subgroup.normalizer (B : Set G))
    (hK0H : conjClosure K T ≤ H)
    (hρ : CFSG.pCore 2 ↥H ≤ (actH hAH hBH).ker) :
    autOn (tildeOf A (conjClosure K T)) (tildeOf A B) =
      (S126.star H K).map (QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ) ⊔
      (S126.star H (conjSub t⁻¹ K)).map (QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ) := by
  have hcomp : (QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = actH hAH hBH := by
    ext x
    rfl
  have hstar : (S126.star H (conjClosure K T)).map
      (QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH hBH) hρ) =
      ((conjClosure K T).subgroupOf H).map (actH hAH hBH) := by
    unfold S126.star
    rw [Subgroup.map_map, hcomp]
  rw [autOn_tilde_eq_map_actH hAH hBH hK0H, ← hstar, ← sup_star_K_K2 h2 ht hKc hTH htK,
    Subgroup.map_sup]

theorem conjSub_inv_le_H {T H K : Subgroup G} (hTH : T ≤ H) (hKH : K ≤ H) {t : G} (ht : t ∈ T) :
    conjSub t⁻¹ K ≤ H := by
  intro x hx
  have h1 : (t⁻¹)⁻¹ * x * t⁻¹ ∈ H := hKH (mem_conjSub.1 hx)
  have key : t⁻¹ * ((t⁻¹)⁻¹ * x * t⁻¹) * (t⁻¹)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem (hTH ht)) h1) (H.inv_mem (H.inv_mem (hTH ht)))
  convert key using 1
  group

theorem ffSteps12633I_of (hA21 : AsA21SQTKSection) (h56 : AsB56) :
    FFSteps12633I := by
  intro G _ _ T L V _ F hH hZ H K hIs h2 h918 I hV₁I hIHU hIHN hW0 hWK
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hTH : T ≤ H := h918.T_le_H
  have hK0H : conjClosure K T ≤ H := h918.K₀_le_H
  have hK0 : H ≤ Subgroup.normalizer (conjClosure K T : Set G) := h918.K₀_normal
  have hKc : K ∈ cComp H := h918.K_cComp
  have h1 := h918.toHypF98.toHypF91
  have hO2 : pCoreOf 2 H ≠ ⊥ := fun h0 => h1.V₁_ne_bot (le_bot_iff.1 (h0 ▸
    h1.V₁_le_Vp.trans ((le_conjClosure _ _).trans h1.conjClosure_Vp_le_pCoreOf)))
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian hO2
  have hXH : conjClosure K T ⊔ T ≤ H := sup_le hK0H hTH
  have hV₁W : F.V1 ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hUN : conjClosure F.V5 H ≤ Subgroup.normalizer (F.V1 : Set G) :=
    h918.conjClosure_le_normalizer_V₁ (le_conjClosure F.V5 H)
  have hAH1 : H ≤ Subgroup.normalizer (F.V1 : Set G) := h918.H_le_normalizer_V₁
  have hBH1 : H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    le_normalizer_conjClosure I H
  have hBA1 : conjClosure I H ≤ Subgroup.normalizer (F.V1 : Set G) :=
    hIHU.trans hUN
  have hAH2 : H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    le_normalizer_conjClosure I H
  have hBH2 : H ≤ Subgroup.normalizer (conjClosure F.V5 H : Set G) :=
    le_normalizer_conjClosure F.V5 H
  have hBA2 : conjClosure F.V5 H ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    HypF91.le_normalizer_of_isElemAbelian_le h918.toHypF98.F911_3 hIHU
  have hE1 : IsElemAbelian 2 (tildeOf F.V1 (conjClosure I H)) :=
    h918.isElemAbelian_tilde_of_le hIHU
  have hE2 : IsElemAbelian 2 (tildeOf (conjClosure I H) (conjClosure F.V5 H)) :=
    h918.isElemAbelian_quotient (conjClosure I H)
  letI instE1 : CommGroup ↥(tildeOf F.V1 (conjClosure I H)) := commGroupOfElemAbelian hE1
  letI instE2 : CommGroup ↥(tildeOf (conjClosure I H) (conjClosure F.V5 H)) :=
    commGroupOfElemAbelian hE2
  obtain ⟨t₀, ht₀, ht₀K⟩ := exists_t_notin_normalizer h2
  have hcomm1 : ∀ b ∈ conjClosure I H, ∀ q ∈ pCoreOf 2 H, q * b * q⁻¹ * b⁻¹ ∈ F.V1 :=
    fun b hb q hq => comm_flip_mem (HypF91.commutator_conjClosure_le h1 b (hIHU hb) q hq)
  have hρ1 : CFSG.pCore 2 ↥H ≤ (actH hAH1 hBH1).ker := fun q hq =>
    MonoidHom.mem_ker.2 (actH_pCore_eq_one hAH1 hBH1 hcomm1 q hq)
  have hcomm2 : ∀ b ∈ conjClosure F.V5 H, ∀ q ∈ pCoreOf 2 H,
      q * b * q⁻¹ * b⁻¹ ∈ conjClosure I H :=
    fun b hb q hq => hV₁W (comm_flip_mem (HypF91.commutator_conjClosure_le h1 b hb q hq))
  have hρ2 : CFSG.pCore 2 ↥H ≤ (actH hAH2 hBH2).ker := fun q hq =>
    MonoidHom.mem_ker.2 (actH_pCore_eq_one hAH2 hBH2 hcomm2 q hq)
  have hnt1 : ∃ k ∈ conjClosure K T, ∃ hk : k ∈ H, actH hAH1 hBH1 ⟨k, hk⟩ ≠ 1 :=
    exists_actH_ne_one hAH1 hBH1 hBA1 hK0H (fun hle => hW0 (by
      rw [← hWK, tildeOf_eq_bot_of_le hle]))
  have claim1a : ¬ F9.IsStrongFFInt (tildeOf F.V1 (conjClosure K T ⊔ T))
      (tildeOf F.V1 (conjClosure I H)) hE1 := by
    intro hS
    have hFF1 := isFFModule_actH_of_isFFInt (A := F.V1) (B := conjClosure I H)
      (X := conjClosure K T ⊔ T) hXH hAH1 hBH1 (F9.IsStrongFFInt.isFFInt hS)
    obtain ⟨-, hns⟩ := sum_star_K hA21 h56 h2 ht₀ hKc hTH ht₀K hK0 hK0H hSQ
      (sq_eq_one_of_isElemAbelian hE1) (actH hAH1 hBH1) hρ1 hnt1 hFF1
    exact hns (isStrongFFModule_actH_of_isStrongFFInt hXH hAH1 hBH1 hS)
  have claim1b : ¬ F9.IsStrongFFInt
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure F.V5 H)) hE2 := by
    by_cases hUW : conjClosure F.V5 H ≤ conjClosure I H
    · intro hS
      have hbot : tildeOf (conjClosure I H) (conjClosure F.V5 H) = ⊥ :=
        tildeOf_eq_bot_of_le hUW
      haveI : Subsingleton ↥(tildeOf (conjClosure I H) (conjClosure F.V5 H)) := by
        refine ⟨fun a b => Subtype.ext ?_⟩
        have ha : (a : SecQuot (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)) ∈
            (⊥ : Subgroup _) := hbot ▸ a.2
        have hb : (b : SecQuot (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)) ∈
            (⊥ : Subgroup _) := hbot ▸ b.2
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      exact (@not_isStrongFFModule_of_subsingleton _ (commGroupOfElemAbelian hE2) this _) hS
    · intro hS
      have hnt2' : ¬ ⁅conjClosure F.V5 H, conjClosure K T⁆ ≤ conjClosure I H := by
        intro hle
        apply hUW
        have h3 : tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ ≤
            tildeOf F.V1 (conjClosure I H) := secImg_mono hle
        rw [tilde_commutator_eq F h918 h2] at h3
        exact le_of_tildeOf_le hUN hV₁W h3
      have hnt2 := exists_actH_ne_one hAH2 hBH2 hBA2 hK0H hnt2'
      have hFF2 := isFFModule_actH_of_isFFInt (A := conjClosure I H)
        (B := conjClosure F.V5 H) (X := conjClosure K T ⊔ T) hXH hAH2 hBH2
        (F9.IsStrongFFInt.isFFInt hS)
      obtain ⟨-, hns⟩ := sum_star_K hA21 h56 h2 ht₀ hKc hTH ht₀K hK0 hK0H hSQ
        (sq_eq_one_of_isElemAbelian hE2) (actH hAH2 hBH2) hρ2 hnt2 hFF2
      exact hns (isStrongFFModule_actH_of_isStrongFFInt hXH hAH2 hBH2 hS)
  have claim2 : @Omega4PlusModule _ (commGroupOfElemAbelian hE1)
      (autOn (tildeOf F.V1 (conjClosure K T)) (tildeOf F.V1 (conjClosure I H))) 2 →
      ¬ IsFFInt (tildeOf F.V1 (conjClosure K T ⊔ T)) (tildeOf F.V1 (conjClosure I H)) hE1 := by
    intro hΩ hff
    have hFF1 := isFFModule_actH_of_isFFInt (A := F.V1) (B := conjClosure I H)
      (X := conjClosure K T ⊔ T) hXH hAH1 hBH1 hff
    obtain ⟨hsum, -⟩ := sum_star_K hA21 h56 h2 ht₀ hKc hTH ht₀K hK0 hK0H hSQ
      (sq_eq_one_of_isElemAbelian hE1) (actH hAH1 hBH1) hρ1 hnt1 hFF1
    obtain ⟨ρs, hρs⟩ : ∃ ρs, ρs = QuotientGroup.lift (CFSG.pCore 2 ↥H) (actH hAH1 hBH1) hρ1 :=
      ⟨_, rfl⟩
    rw [← hρs] at hsum
    have hMp : autOn (tildeOf F.V1 (conjClosure K T)) (tildeOf F.V1 (conjClosure I H)) =
        (S126.star H K).map ρs ⊔ (S126.star H (conjSub t₀⁻¹ K)).map ρs := by
      rw [hρs]
      exact autOn_K0_eq_sup h2 ht₀ hKc hTH ht₀K hAH1 hBH1 hK0H hρ1
    have hntρ : ∃ k ∈ conjClosure K T, ∃ hk : k ∈ H,
        ρs (QuotientGroup.mk ⟨k, hk⟩) ≠ 1 := by
      obtain ⟨k, hk, hkH, hne⟩ := hnt1
      exact ⟨k, hk, hkH, by rw [hρs, QuotientGroup.lift_mk]; exact hne⟩
    have hinj : Function.Injective (ρs.comp (S126.star H K).subtype) :=
      star_K_comp_injective ht₀ hTH h2 ρs (nontriv_star h2 ht₀ hKc hTH ht₀K ρs hntρ)
    have hrange : (ρs.comp (S126.star H K).subtype).range = (S126.star H K).map ρs := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have eL : ↥(S126.star H K) ≃* ↥((S126.star H K).map ρs) :=
      (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
    have hqL : CFSG.IsQuasisimple ↥((S126.star H K).map ρs) := by
      haveI := isSimpleGroup_star_K h2
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eL
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_star_K h2)).1
    have hL1 : (S126.star H K).map ρs ≠ ⊥ := by
      intro hbot
      have hc : Nat.card ↥((S126.star H K).map ρs) = 60 := by
        rw [← star_card_K h2]
        exact (Nat.card_congr eL.toEquiv).symm
      rw [hbot, Subgroup.card_bot] at hc
      norm_num at hc
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : Fintype ↥(S126.star H K) := Fintype.ofFinite _
    have h3dvd : 3 ∣ Fintype.card ↥(S126.star H K) := by
      rw [← Nat.card_eq_fintype_card, star_card_K h2]
      norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 h3dvd
    have hb0mem : ρs x.1 ∈ (S126.star H K).map ρs := Subgroup.mem_map.2 ⟨x.1, x.2, rfl⟩
    have hb0ne : ρs x.1 ≠ 1 := by
      intro h
      have hx1 : x = 1 := hinj (show (ρs.comp (S126.star H K).subtype) x =
        (ρs.comp (S126.star H K).subtype) 1 by simpa using h)
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    have hodd : Odd (orderOf (ρs x.1)) := by
      have := orderOf_injective (ρs.comp (S126.star H K).subtype) hinj x
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at this
      rw [this, hx]
      decide
    have hcommLL : ∀ u ∈ (S126.star H K).map ρs,
        ∀ v ∈ (S126.star H (conjSub t₀⁻¹ K)).map ρs, u * v = v * u := by
      intro u hu v hv
      obtain ⟨xb, hxb, rfl⟩ := Subgroup.mem_map.1 hu
      obtain ⟨yb, hyb, rfl⟩ := Subgroup.mem_map.1 hv
      rw [← map_mul, ← map_mul, commute_star_K_K2 h2 ht₀ hKc hTH ht₀K xb hxb yb hyb]
    have hfix2 := @fixV_compl_bot_of_omega4_two ↥(tildeOf F.V1 (conjClosure I H))
      (commGroupOfElemAbelian hE1) _ (autOn (tildeOf F.V1 (conjClosure K T))
        (tildeOf F.V1 (conjClosure I H))) ((S126.star H K).map ρs)
      ((S126.star H (conjSub t₀⁻¹ K)).map ρs) hΩ hMp hcommLL hqL hL1 (ρs x.1) hb0mem hb0ne
      hodd
    rw [hfix2] at hsum
    have hbotL : (S126.star H K).map ρs ≤ ⊥ := by
      intro u hu
      rw [Subgroup.mem_bot]
      have hu1 : u = 1 := by
        apply MulEquiv.ext
        intro v
        have hw := hsum (Subgroup.subset_closure ⟨u, hu, v, rfl⟩)
        rw [Subgroup.mem_bot, mul_inv_eq_one] at hw
        rw [MulAut.one_apply]
        exact hw
      exact hu1
    exact hL1 (le_bot_iff.1 hbotL)
  have claim3 : IsFFInt
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure K T ⊔ T))
      (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
        (conjClosure F.V5 H)) hE2 →
      tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ =
        tildeOf F.V1 (conjClosure F.V5 H) →
      ∀ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) →
        ⁅⁅conjClosure F.V5 H, K⁆, conjSub t⁻¹ K⁆ ≤ conjClosure I H := by
    intro hFF htil t ht htK'
    by_cases hUW : conjClosure F.V5 H ≤ conjClosure I H
    ·
      have hK₂ : conjSub t⁻¹ K ≤ H := conjSub_inv_le_H hTH hKH ht
      have hXU : ⁅conjClosure F.V5 H, K⁆ ≤ conjClosure I H :=
        (commutator_le_conjClosure le_rfl hKH).trans hUW
      refine Subgroup.commutator_le.mpr (fun (a : G) (ha : a ∈ ⁅conjClosure F.V5 H, K⁆)
        (y : G) (hy : y ∈ conjSub t⁻¹ K) => ?_)
      have haI : a ∈ conjClosure I H := hXU ha
      have hyN : y⁻¹ ∈ Subgroup.normalizer (conjClosure I H : Set G) :=
        hAH2 (H.inv_mem (hK₂ hy))
      have hya : y * a⁻¹ * y⁻¹ ∈ conjClosure I H :=
        (Subgroup.mem_normalizer_iff.1 (hAH2 (hK₂ hy)) a⁻¹).1
          ((conjClosure I H).inv_mem haI)
      rw [commutatorElement_def]
      have e : a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) := by group
      rw [e]
      exact (conjClosure I H).mul_mem haI hya
    · have hnt3' : ¬ ⁅conjClosure F.V5 H, conjClosure K T⁆ ≤ conjClosure I H := by
        intro hle
        apply hUW
        have h3 : tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ ≤
            tildeOf F.V1 (conjClosure I H) := secImg_mono hle
        rw [htil] at h3
        exact le_of_tildeOf_le hUN hV₁W h3
      have hnt3 := exists_actH_ne_one hAH2 hBH2 hBA2 hK0H hnt3'
      have hFF2 := isFFModule_actH_of_isFFInt (A := conjClosure I H)
        (B := conjClosure F.V5 H) (X := conjClosure K T ⊔ T) hXH hAH2 hBH2 hFF
      obtain ⟨hsum, -⟩ := sum_star_K hA21 h56 h2 ht hKc hTH htK' hK0 hK0H hSQ
        (sq_eq_one_of_isElemAbelian hE2) (actH hAH2 hBH2) hρ2 hnt3 hFF2
      exact comm_comm_le_of_fix hAH2 hBH2 hBA2 hKH (conjSub_inv_le_H hTH hKH ht) hρ2 hsum
  exact ⟨⟨claim1a, claim1b⟩, claim2, claim3⟩

end CFSG.Quasithin.H13.L1233
