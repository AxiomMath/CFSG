module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310C
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8313
public import CFSG.Quasithin.Vol2.Ch8Input812Proved
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G]

namespace Ch8311

omit [Finite G] in
theorem exists_of_rParam_eq_three {V : Subgroup G} (h : E3.rParam V = 3) :
    ∃ U : Subgroup G, U ≤ V ∧ ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) ∧
      E3.mQuot V U = 3 := by
  by_contra hno
  push Not at hno
  have h4 : (4 : ℕ∞) ≤ E3.rParam V := by
    refine le_iInf₂ fun U hU => ?_
    have h3 : (3 : ℕ∞) ≤ (E3.mQuot V U : ℕ∞) := h ▸ E3.rParam_le_mQuot hU.1 hU.2
    have hne : (E3.mQuot V U : ℕ∞) ≠ 3 := by exact_mod_cast hno U hU.1 hU.2
    have hlt : (3 : ℕ∞) < (E3.mQuot V U : ℕ∞) := lt_of_le_of_ne h3 (Ne.symm hne)
    have := (ENat.add_one_le_iff (by simp : (3 : ℕ∞) ≠ ⊤)).mpr hlt
    have e : (3 : ℕ∞) + 1 = 4 := by norm_num
    rwa [e] at this
  rw [h] at h4
  norm_num at h4

theorem exists_model_sylU {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) [IsMulCommutative ↥(fsuV T I)]
    (hrow : Row711L3Wreath T L I) :
    ∃ e : IntMod (fsuV T I) hV ≃* WMod, (autI hV (fsuL0 T L)).map (congrHom e) = img ∧
      (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : (tensorPairModel SL32 SL32).RealizesMod (V := IntMod (fsuV T I) hV)
      (autI hV (fsuL0 T L)) := hrow.2
  obtain ⟨e, he⟩ := exists_model hL
  have hT := isSylowIn_top_of_fsu hyp.fsu
  have hTL₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hB : Nat.card ↥(autI hV (fsuL0 T L)) = 2 ^ 6 * 441 := by
    have h1 := card_map_congrHom e (autI hV (fsuL0 T L))
    rw [he] at h1
    exact h1.symm.trans card_img
  have hfac : (2 ^ 6 * 441 : ℕ).factorization 2 = 6 := by
    rw [Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hS : Nat.card ↥(autI hV (T ⊓ fsuL0 T L)) = 2 ^ 6 := by
    have h : Nat.card ↥(autI hV (T ⊓ fsuL0 T L)) =
        2 ^ (Nat.card ↥(autI hV (fsuL0 T L))).factorization 2 :=
      card_autOn_inf_of_sylow hT hTL₀ hTV
    rw [h, hB, hfac]
  obtain ⟨g, hg, hgS⟩ := exists_conj_l3wrSylU_le
    (S := (autI hV (T ⊓ fsuL0 T L)).map (congrHom e))
    (he ▸ Subgroup.map_mono (autI_mono hV inf_le_right)) ((card_map_congrHom e _).trans hS)
  refine ⟨e.trans g⁻¹, map_congrHom_trans_eq_img e he (img.inv_mem hg), ?_⟩
  intro x hx
  have hx' : g * x * g⁻¹ ∈ B3.cj g l3wrSylU := B3.mem_cj.2 (by
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx)
  obtain ⟨ψ, hψ, hψe⟩ := hgS hx'
  refine ⟨ψ, autI_mono hV inf_le_left hψ, MulEquiv.ext fun w => ?_⟩
  have h3 : e (ψ (e.symm (g w))) = g (x (g⁻¹ (g w))) :=
    congrArg (fun φ : MulAut WMod => φ (g w)) hψe
  change g⁻¹ (e (ψ (e.symm (g w)))) = x w
  rw [h3, MulAut.inv_apply_self, MulAut.inv_apply_self]

omit [Finite G] in
theorem card_comap_ch83Val {V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V) :
    Nat.card ↥(U.comap (ch83Val hV)) = Nat.card U :=
  Nat.card_congr
    { toFun := fun v => ⟨(v : IntMod V hV).val, v.2⟩
      invFun := fun u => ⟨IntMod.mk hV ⟨u, hUV u.2⟩, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem centralizer_le_of_offender {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    (h838 : Stmt8_3_8) (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L)
    (e : IntMod (fsuV T I) hV ≃* WMod) (he : (autI hV (fsuL0 T L)).map (congrHom e) = img)
    (hY : (U3.prod U3).map rho ≤ (autI hV T).map (congrHom e))
    {U : Subgroup G} (hUV : U ≤ fsuV T I) (hU64 : 64 ≤ Nat.card U)
    {A : Subgroup (MulAut (IntMod (fsuV T I) hV))} (hoff : IsFOneOffender (autI hV ⊤) A)
    (hfix : LeFixI hV U A) : Subgroup.centralizer (U : Set G) ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hAX, hA1, hA2⟩, hrk⟩ := hoff
  set A' := A.map (congrHom e) with hA'def
  have hAn : A' ≤ norm := by
    rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 (hAX hψ)
    exact congrHom_mem_norm e he (convI_mem_normalizer_autI hV (hNM g.2))
  have hA2' : IsElemAbelian2 A' := (isElemAbelian2_map_congrHom e).mpr hA2
  set SU := U.comap (ch83Val hV) with hSUdef
  have hSU : SU ≤ fixV A := fun v hv x hx => hfix v hv x hx
  have hSUcard : 64 ≤ Nat.card ↥SU := (card_comap_ch83Val hV hUV).symm ▸ hU64
  obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hfixA64 : Nat.card ↥(fixV A) ≤ 64 := by
    have ha2 : orderOf (congrHom e a) = 2 := by
      rw [orderOf_injective _ (congrHom_injective e)]
      exact orderOf_eq_prime (hA2.2 a haA) ha1'
    have h1 := card_fixV_le (hAn ⟨a, haA, rfl⟩) ha2
    have h2 : fixV (Subgroup.zpowers (congrHom e a)) =
        (fixV (Subgroup.zpowers a)).map e.toMonoidHom :=
      (congrArg fixV (MonoidHom.map_zpowers (congrHom e) a).symm).trans (fixV_map_congrHom e _)
    have h3 : Nat.card ↥((fixV (Subgroup.zpowers a)).map e.toMonoidHom) =
        Nat.card ↥(fixV (Subgroup.zpowers a)) := Subgroup.card_map_of_injective e.injective
    have h4 : Nat.card ↥(fixV (Subgroup.zpowers a)) ≤ 64 := by
      rw [← h3, ← h2]
      exact h1
    exact (Subgroup.card_le_of_le (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr haA))).trans h4
  have hSUeq : SU = fixV A := Subgroup.eq_of_le_of_card_ge hSU (hfixA64.trans hSUcard)
  have hcardV : Nat.card (IntMod (fsuV T I) hV) = 2 ^ 9 := by
    rw [Nat.card_congr e.toEquiv, card_WMod]
  have hA4 : 4 ≤ Nat.card ↥A := by
    have hsum := CFSG.Quasithin.rk_add_rkIdx (fixV A)
    have hrkV : rk (IntMod (fsuV T I) hV) = 9 := by
      unfold rk
      rw [hcardV, padicValNat.prime_pow]
    have hrkF : rk ↥(fixV A) ≤ 6 := by
      by_contra hlt
      push Not at hlt
      have h1 : 2 ^ rk ↥(fixV A) ∣ Nat.card ↥(fixV A) := pow_padicValNat_dvd
      have h2 := Nat.le_of_dvd Nat.card_pos h1
      have h3 : 2 ^ 7 ≤ 2 ^ rk ↥(fixV A) := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    have hrkA : 2 ≤ rk ↥A := by omega
    have h1 : 2 ^ rk ↥A ∣ Nat.card ↥A := pow_padicValNat_dvd
    have h2 := Nat.le_of_dvd Nat.card_pos h1
    have h3 : 2 ^ 2 ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) hrkA
    omega
  have hA4' : 4 ≤ Nat.card ↥A' := (card_map_congrHom e A).symm ▸ hA4
  have hfixA' : fixV A' = (fixV A).map e.toMonoidHom := fixV_map_congrHom e A
  have hfix' : 64 ≤ Nat.card ↥(fixV A') := by
    have h3 : Nat.card ↥(fixV A') = Nat.card ↥(fixV A) := by
      rw [hfixA']
      exact Subgroup.card_map_of_injective e.injective
    rw [h3, ← hSUeq]
    exact hSUcard
  obtain ⟨B, hB, y, hy, hBy⟩ := exists_aSet_map_le hY hAn hA2' hA4' hfix'
  obtain ⟨B₀, -, rfl⟩ := exists_eq_map_congrHom e hB.1
  have hB₀ : B₀ ∈ E3.aSet 2 (autI hV T) := (map_mem_aSet_iff e).mp hB
  rw [← he] at hy
  obtain ⟨ψ, hψ, rfl⟩ := hy
  obtain ⟨l, hlL, rfl⟩ := (mem_autI hV).1 hψ
  have hlU : ∀ v ∈ fixV B₀, (l : G) * v.val * (l : G)⁻¹ ∈ U := by
    intro v hv
    have hEq : fixV (B₀.map (congrHom e)) = (fixV B₀).map e.toMonoidHom := fixV_map_congrHom e B₀
    have h1 : (congrHom e (convI hV l)) (e v) ∈ fixV A' := by
      apply hBy
      exact ⟨e v, (Subgroup.ext_iff.mp hEq _).mpr ⟨v, hv, rfl⟩, rfl⟩
    have h1' := (Subgroup.ext_iff.mp hfixA' _).mp h1
    obtain ⟨w, hw, hwe⟩ := h1'
    have hwv : w = convI hV l v := by
      apply e.injective
      rw [show e w = e.toMonoidHom w from rfl, hwe]
      change e (convI hV l (e.symm (e v))) = e (convI hV l v)
      rw [MulEquiv.symm_apply_apply]
    rw [← hSUeq, hwv] at hw
    have h2 : (convI hV l v).val ∈ U := hw
    rwa [convI_apply_val] at h2
  have hCR := h838 G T L I hyp h731 hc hrow hV
  intro c hcU
  have hlM : (l : G) ∈ fsuM T L := Subgroup.le_normalizer hlL
  have hc' : (l : G)⁻¹ * c * l ∈ Subgroup.centralizer (ch83CR hV : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hvB : v ∈ fixV B₀ := B1.fixV_le_fixV (le_iSup₂_of_le B₀ hB₀ le_rfl) hv
    have h1 := Subgroup.mem_centralizer_iff.mp hcU _ (hlU v hvB)
    change v.val * ((l : G)⁻¹ * c * l) = (l : G)⁻¹ * c * l * v.val
    calc v.val * ((l : G)⁻¹ * c * l)
        = (l : G)⁻¹ * (((l : G) * v.val * (l : G)⁻¹) * c) * l := by group
      _ = (l : G)⁻¹ * (c * ((l : G) * v.val * (l : G)⁻¹)) * l := by rw [h1]
      _ = (l : G)⁻¹ * c * l * v.val := by group
  have h2 := hCR hc'
  have e2 : c = (l : G) * ((l : G)⁻¹ * c * l) * (l : G)⁻¹ := by group
  rw [e2]
  exact (fsuM T L).mul_mem ((fsuM T L).mul_mem hlM h2) ((fsuM T L).inv_mem hlM)

end Ch8311

theorem stmt8_3_11_of
    (h3228 : Stmt3_2_2_eight) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h326 : Stmt3_2_6C) (hPT : E6.ParabolicTorusFact) (h832 : Stmt8_3_2) (h838 : Stmt8_3_8)
    (h8310 : Stmt8_3_10) : Stmt8_3_11 := by
  intro G _ _ T L I hyp h731 hc hrow
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := stmtFSUModule_of_eight h3228
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hVVM]
    exact le_normalizer_conjClosure _ _
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hE : E6.HypE61 T (fsuM T L) (fsuV T I) :=
    hypE61_of_ti h37 h38 h39 hmod h3228 hyp fun g hg hgN => absurd (hMV hg) hgN
  obtain ⟨e, he, hY⟩ := Ch8311.exists_model_sylU hyp hV hrow
  have hcardV : Nat.card ↥(fsuV T I) = 2 ^ 9 := by
    have h1 : Nat.card (IntMod (fsuV T I) hV) = Nat.card WMod := Nat.card_congr e.toEquiv
    rw [card_WMod] at h1
    exact h1
  have hs := h832 G T L I hyp h731 hc hrow hV
  have hr3 : (3 : ℕ∞) ≤ E3.rParam (fsuV T I) := by
    by_contra hlt
    push Not at hlt
    unfold E3.sParam at hs
    set m := min (E3.rParam (fsuV T I)) ((E3.mParam (autI hV ⊤) : ℕ) : ℕ∞) with hm
    have hm3 : m < 3 := lt_of_le_of_lt (min_le_left _ _) hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, m = k :=
      ⟨m.toNat, (ENat.natCast_toNat (ne_top_of_lt hm3)).symm⟩
    rw [hk] at hm3 hs
    simp only [ENat.toNat_natCast] at hs
    rw [hs] at hm3
    exact absurd hm3 (lt_irrefl _)
  by_contra hr
  push Not at hr
  have hr' : E3.rParam (fsuV T I) = 3 := le_antisymm hr hr3
  obtain ⟨U, hUV, hCU, hUm⟩ := Ch8311.exists_of_rParam_eq_three hr'
  have hCUM : ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L := fun h => hCU (h.trans hMV)
  have hU64 : Nat.card U = 64 := by
    have h1 := Subgroup.relIndex_mul_card U (fsuV T I)
    rw [inf_eq_left.mpr hUV, hcardV] at h1
    have hdvd : U.relIndex (fsuV T I) ∣ 2 ^ 9 := Dvd.intro _ h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj3 : j = 3 := by
      unfold E3.mQuot at hUm
      rw [hj, padicValNat.prime_pow] at hUm
      exact hUm
    rw [hj, hj3] at h1
    omega
  have hU1 : U ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hU64
    omega
  obtain ⟨z, hz2, hzV⟩ := input8_3_z G T L I hyp h731 hc hrow
  obtain ⟨⟨K, s, hsT, hsN, hKC, hKz, F, _, _, hF4, ⟨eF⟩⟩, h1b, h1c, h2a, -, -, -⟩ :=
    h8310 G T L I hyp h731 hc hrow z hz2 hzV
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hXL0 : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hXM : ch83X T L z ≤ fsuM T L := hXL0.trans Subgroup.le_normalizer
  have hXKz : ch83X T L z ≤ ch83Kz T L z := le_conjClosure _ _
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hTKzN : T ≤ Subgroup.normalizer (ch83Kz T L z : Set G) := hTz.trans hGzKz
  have hTX : T ≤ Subgroup.normalizer (ch83X T L z : Set G) := fun t ht => by
    have h1 : t ∈ Subgroup.normalizer
        ((fsuL0 T L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) : Set G) :=
      E1.mem_normalizer_inf (hTM ht) (Subgroup.le_normalizer (hTz ht))
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [ch83X, E1.map_twoResidual, h1]
  have hKzM : ¬ ch83Kz T L z ≤ fsuM T L := fun h => h1b.2.1 (sup_le h hTM)
  have hB : ch83X T L z ⊔ (T ⊓ ch83Kz T L z) ≤ fsuM T L := sup_le hXM (inf_le_left.trans hTM)
  have hA5 : Nonempty (OTwoQuot K ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨e₅⟩ := Ch8310.a5_of_sl24 hF4
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥K).symm).trans
      (eF.trans e₅)⟩
  obtain ⟨e₁, he₁, hz, hez⟩ := exists_model_eW00 hyp hV hrow hz1 hzV
  obtain ⟨-, -, kX, hkX⟩ := Ch8310.borel_setting (mem_cComp_iff.mpr hKC) (hTsyl _ hTz) hsT hsN
    hKz hGzKz hA5 hXKz (hTX hsT) (Ch8310.nine_dvd_card_ch83X hV hN e₁ he₁ hz hez)
    fun h => hKzM (h.trans hB)
  have h9a := Ch8310.nine_dvd_card_autI_ch83X hV e₁ he₁ hz hez
  have hXN : ch83X T L z ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    hXL0.trans (le_sup_left.trans hN)
  have hXC : IsPGroup 2 ↥(ch83X T L z ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    have hcard := card_autI_mul_card_inf hV hXN
    obtain ⟨a, ha⟩ := h9a
    have h1 : 9 * (a * Nat.card ↥(ch83X T L z ⊓ Subgroup.centralizer (fsuV T I : Set G))) ∣
        9 * (16 * 2 ^ kX) := by
      have e1 : 9 * (a * Nat.card ↥(ch83X T L z ⊓ Subgroup.centralizer (fsuV T I : Set G))) =
          Nat.card ↥(ch83X T L z) := by
        rw [← hcard, ha]
        ring
      rw [e1, show 9 * (16 * 2 ^ kX) = 144 * 2 ^ kX by ring]
      exact hkX
    have h2 : Nat.card ↥(ch83X T L z ⊓ Subgroup.centralizer (fsuV T I : Set G)) ∣
        2 ^ (kX + 4) := by
      have h3 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
      have h4 := (Dvd.intro_left a rfl).trans h3
      rwa [show 16 * 2 ^ kX = 2 ^ (kX + 4) by ring] at h4
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact IsPGroup.of_card hm
  have hXTC : IsPGroup 2 ↥((ch83X T L z ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    intro y
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hyp.fsu.sylow.1
      (sup_le Subgroup.le_normalizer hTX) (sup_comm _ _) (y : G) y.2.1
    have hyk : (y : G) ^ 2 ^ k ∈ ch83X T L z ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      ⟨hk, Subgroup.pow_mem _ y.2.2 _⟩
    obtain ⟨j, hj⟩ := hXC ⟨_, hyk⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((y : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_add, pow_mul]
    exact hj'
  have hMz : fsuM T L ⊓ Subgroup.centralizer ({z} : Set G) ≤ ch83X T L z ⊔ T := by
    refine Ch8310.le_of_inf_le hTKzN (le_inf hTM hTz) (inf_le_right.trans h2a.le) ?_
      le_sup_right
    intro y hy
    have hy1 : y ∈ ch83Kz T L z ⊓ fsuM T L := ⟨hy.2, hy.1.1⟩
    rw [← h1c] at hy1
    exact (sup_le (le_sup_left : ch83X T L z ≤ ch83X T L z ⊔ T)
      (inf_le_left.trans le_sup_right) : ch83X T L z ⊔ (T ⊓ ch83Kz T L z) ≤ ch83X T L z ⊔ T) hy1
  have hCVz : Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzmem.1)
  have hCMV : IsPGroup 2 ↥(fsuM T L ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    hXTC.to_le (le_inf ((inf_le_inf_left _ hCVz).trans hMz) inf_le_right)
  apply hCUM
  have hVC : fsuV T I ≤ Subgroup.centralizer (U : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun u hu => setLike_mul_comm (hUV hu) hv
  have hCN : fsuM T L ⊓ Subgroup.centralizer (U : Set G) ≤
      Subgroup.normalizer (fsuV T I : Set G) := E6.inf_centralizer_le_normalizer_of_le hE hU1 hUV
  refine E6.e6_27 hPT hE hU1 hUV (j := 1) Nat.one_pos (by rw [hr']; norm_num) ?_ ?_ ?_
  ·
    by_contra hJ
    obtain ⟨A, ⟨hAX, hAel, hAmax⟩, hAV⟩ : ∃ A : Subgroup G,
        (A ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) ∧ IsElemAbelian 2 A ∧
          ∀ B : Subgroup G, B ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) →
            IsElemAbelian 2 B → Nat.card B ≤ 2 ^ 1 * Nat.card A) ∧
        ¬ A ≤ Subgroup.centralizer (fsuV T I : Set G) := by
      by_contra hall
      push Not at hall
      exact hJ (iSup₂_le fun A hA => le_inf (hA.1.trans inf_le_left) (hall A hA))
    have hAN : A ≤ Subgroup.normalizer (fsuV T I : Set G) := hAX.trans hCN
    have hVX : fsuV T I ≤ fsuM T L ⊓ Subgroup.centralizer (U : Set G) :=
      le_inf hE.tiSet.1 hVC
    have hsup : (A ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔ fsuV T I ≤
        fsuM T L ⊓ Subgroup.centralizer (U : Set G) := sup_le (inf_le_left.trans hAX) hVX
    have hsupel : IsElemAbelian 2 ((A ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔ fsuV T I) :=
      B2F.isElemAbelian_sup_of_commute (B2F.isElemAbelian_mono inf_le_left hAel) hV
        fun c hc v hv => (Subgroup.mem_centralizer_iff.1 hc.2 v hv).symm
    have hcard := card_le_two_mul_card_autI hV hAel hAN (by
      have h1 := hAmax _ hsup hsupel
      rwa [pow_one] at h1)
    exact hCUM (Ch8311.centralizer_le_of_offender hyp h731 hrow h838 hV hNM e he hY hUV
      hU64.ge (isFOneOffender_autI hV hAel hAN hAV hcard)
      (leFixI_of_le_autI hV (hAX.trans inf_le_right) (autI_mono hV le_rfl)))
  ·
    refine csSup_le' fun c hc => ?_
    obtain ⟨Y, B, S, hYB, hBX, hYc, hYcard, -, -, -, -⟩ := hc
    by_contra hc1
    push Not at hc1
    obtain ⟨y, hy⟩ := hYc.exists_generator
    have hyo : orderOf (y : MulAut (IntMod (fsuV T I) hV)) = 2 ^ c - 1 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYcard]
    have hyX : (y : MulAut (IntMod (fsuV T I) hV)) ∈
        autI hV (fsuM T L ⊓ Subgroup.centralizer (U : Set G)) := hBX (hYB y.2)
    obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
    have hk1 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, mul_comm]
    have hy1 : (y : MulAut (IntMod (fsuV T I) hV)) ≠ 1 := fun h1 => by
      rw [h1, orderOf_one, hpow] at hyo
      omega
    have hyodd : Odd (orderOf (y : MulAut (IntMod (fsuV T I) hV))) := by
      rw [hyo, hpow]
      exact ⟨2 ^ k - 1, by omega⟩
    set y' := congrHom e (y : MulAut (IntMod (fsuV T I) hV)) with hy'
    have hy'n : y' ∈ L3Wr.norm := by
      obtain ⟨g, -, hg⟩ := (mem_autI hV).1 hyX
      rw [hy', ← hg]
      exact congrHom_mem_norm e he (convI_mem_normalizer_autI hV (hNM g.2))
    have hy'1 : y' ≠ 1 := fun h1 => hy1 (congrHom_injective e (h1.trans (map_one _).symm))
    have hy'o : Odd (orderOf y') := by
      rw [hy', orderOf_injective _ (congrHom_injective e)]
      exact hyodd
    have h32 := card_fixV_le_of_odd hy'n hy'1 hy'o
    have hfixU : LeFixI hV U (Subgroup.zpowers (y : MulAut (IntMod (fsuV T I) hV))) :=
      leFixI_of_le_autI hV inf_le_right (Subgroup.zpowers_le.mpr hyX)
    have h64 : 64 ≤ Nat.card ↥(fixV (Subgroup.zpowers y')) := by
      have hEq : fixV (Subgroup.zpowers y') =
          (fixV (Subgroup.zpowers (y : MulAut (IntMod (fsuV T I) hV)))).map e.toMonoidHom :=
        (congrArg fixV (MonoidHom.map_zpowers (congrHom e) _).symm).trans
          (fixV_map_congrHom e _)
      have hle : U.comap (ch83Val hV) ≤
          fixV (Subgroup.zpowers (y : MulAut (IntMod (fsuV T I) hV))) :=
        fun v hv x hx => hfixU v hv x hx
      have h1 : Nat.card ↥(fixV (Subgroup.zpowers y')) =
          Nat.card ↥(fixV (Subgroup.zpowers (y : MulAut (IntMod (fsuV T I) hV)))) := by
        rw [hEq]
        exact Subgroup.card_map_of_injective e.injective
      rw [h1]
      refine le_trans ?_ (Subgroup.card_le_of_le hle)
      rw [Ch8311.card_comap_ch83Val hV hUV, hU64]
    omega
  ·
    intro X hXM hX1 _ hXodd
    exfalso
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (hCMV.to_le hXM)
    rw [hk] at hXodd
    rcases k with _ | k
    · apply hX1
      rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq X hk
    · exact Nat.not_even_iff_odd.mpr hXodd (Nat.even_pow.mpr ⟨even_two, by omega⟩)

end CFSG.Quasithin.H13
