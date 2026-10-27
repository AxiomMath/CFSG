module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10A
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod3B
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4G

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem r2_fixCount : ∀ r ∈ r2, r ≠ B6.id → fixCount r = 16 := by decide

theorem oVecL_wV : ∀ c ∈ oVecL, wV c ∈ oVecL := by decide

theorem xor_wV : ∀ c < 64, c ^^^ wV c = wV (wV c) := by decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem card_fixV_zpowers_code {C : Coding ↥V} (a : MulAut ↥V) :
    Nat.card ↥(fixV (Subgroup.zpowers a)) = fixCount (C.cB a) := by
  have := C.card_of_codes (fixV (Subgroup.zpowers a) : Set ↥V)
    ((List.range 64).filter fun c => (C.cB a).app c == c) (nodup_fixed _)
    (fun c hc => (mem_fixed.1 hc).1) (fun v => by
      rw [SetLike.mem_coe, mem_fixV_zpowers, C.apply_eq_self_iff, mem_fixed]
      exact ⟨fun h => ⟨C.cd_lt v, h⟩, fun h => h.2⟩)
  exact this

omit [IsMulCommutative ↥V] in
theorem rkIdx_eq_of_card (hV : Nat.card ↥V = 2 ^ 6) {H : Subgroup ↥V} {k : ℕ}
    (hk : Nat.card H = 2 ^ k) : rkIdx H = 6 - k := by
  have e := rk_add_rkIdx H
  have hrkV : rk ↥V = 6 := by
    unfold rk
    rw [hV, padicValNat.prime_pow]
  have hrkH : rk ↥H = k := by
    unfold rk
    rw [hk, padicValNat.prime_pow]
  omega

omit [IsMulCommutative ↥V] in
theorem card_sub_V (h : Hyp1271 G T L V) (hV : Nat.card ↥V = 2 ^ 6) (H : Subgroup ↥V) :
    ∃ k ≤ 6, Nat.card H = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥H := (isPGroup_V' h).to_subgroup H
  have e := card_eq_two_pow_of_isPGroup hp
  refine ⟨rk ↥H, ?_, e⟩
  have hd : Nat.card H ∣ Nat.card ↥V := Subgroup.card_subgroup_dvd_card H
  rw [e, hV] at hd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hd

theorem mParam_MVbar
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    E3.mParam h.hyp.MVbar = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hV64 := card_V h1222 h
  have hR2 := R2_mem_aSet h1222 h
  have hTM : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  have hev := E3.even_card_of_isPGroup (hR2.1.trans hTM)
    (E3.isPGroup_of_isElemAbelian2 hR2.2.2.1) hR2.2.1
  simp only [E3.mParam, hev, ↓reduceIte]
  have hlow : ∀ b ∈ h.hyp.MVbar, orderOf b = 2 → 2 ≤ rkIdx (fixV (Subgroup.zpowers b)) := by
    intro b hb hb2
    have hB := (MVbar_code h hC.1 hb).1
    have hb1 : b ≠ 1 := fun e => by rw [e, orderOf_one] at hb2; norm_num at hb2
    have hBsq : (C.cB b).comp (C.cB b) = B6.id := by
      rw [← C.cB_mul, ← pow_two, ← hb2, pow_orderOf_eq_one, C.cB_one]
    have h16 := cert4_inv_fix16 _ hB hBsq (fun e => hb1 (C.cB_eq_one.1 e))
    obtain ⟨k, hk6, hk⟩ := card_sub_V h hV64 (fixV (Subgroup.zpowers b))
    rw [rkIdx_eq_of_card hV64 hk]
    have hk16 : 2 ^ k ≤ 2 ^ 4 := by
      rw [← hk, card_fixV_zpowers_code (C := C)]
      exact le_of_le_of_eq h16 (by norm_num)
    have hk4 : k ≤ 4 := by
      by_contra hk4
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  obtain ⟨r, hr, hr1⟩ := r2_ne_id
  obtain ⟨a, rfl⟩ := hC.1.2 r (r2_sub r hr).1
  have haR : a ∈ autOn (R2 T L V) V := (mem_autOn_R2_iff h1222 h hC a).2 hr
  have ha2 : orderOf a = 2 := by
    apply orderOf_eq_prime
    · apply C.cB_injective
      rw [pow_two, C.cB_mul, C.cB_one]
      exact r2_sq _ hr
    · exact fun e => hr1 (by rw [e, C.cB_one])
  have hrk : rkIdx (fixV (Subgroup.zpowers a)) = 2 := by
    have hc : Nat.card ↥(fixV (Subgroup.zpowers a)) = 2 ^ 4 := by
      rw [card_fixV_zpowers_code (C := C), r2_fixCount _ hr hr1]
      norm_num
    rw [rkIdx_eq_of_card hV64 hc]
  have hmem : 2 ∈ {n : ℕ | ∃ t ∈ h.hyp.MVbar, orderOf t = 2 ∧
      n = rkIdx (fixV (Subgroup.zpowers t))} := ⟨a, hTM (hR2.1 haR), ha2, hrk.symm⟩
  apply le_antisymm (Nat.sInf_le hmem)
  obtain ⟨b, hb, hb2, he⟩ := Nat.sInf_mem ⟨2, hmem⟩
  rw [he]
  exact hlow b hb hb2

theorem centralizer_le_of_oVecL
    {t : G} (hS : Setting1273 G T L V t) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (hct : C.cd ⟨t, hS.t_mem⟩ ∈ oVecL) {v : ↥V} (hv : C.cd v ∈ oVecL) :
    Subgroup.centralizer ({(v : G)} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨g₁, hg₁, hg₁v⟩ := cert4_hyp_trans _ hv
  obtain ⟨g₂, hg₂, hg₂t⟩ := cert4_hyp_trans _ hct
  obtain ⟨a₁, rfl⟩ := hC.2 g₁ hg₁
  obtain ⟨x₁, hx₁, hx₁L, rfl⟩ := mem_autOn'.1 ((hC.1 _).2 hg₁)
  obtain ⟨x₂, hx₂L, hx₂, hx₂c⟩ := exists_L_map_to hC hg₂ (C.cd_lt _) hg₂t
  set l := x₂ * x₁ with hld
  have hlL : l ∈ L := L.mul_mem hx₂L hx₁L
  have hlN : l ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hx₂ hx₁
  have hlv : l * v * l⁻¹ = t := by
    have e := cd_conj C hlN v
    rw [conjAct_mul_code hx₂ hx₁, hg₁v, hx₂c] at e
    exact congrArg Subtype.val (C.cd_injective e)
  intro y hy
  have hly : l * y * l⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hlv]
    calc l * y * l⁻¹ * (l * ↑v * l⁻¹) = l * (y * v) * l⁻¹ := by group
      _ = l * (v * y) * l⁻¹ := by rw [hy]
      _ = l * ↑v * l⁻¹ * (l * y * l⁻¹) := by group
  have hM := hS.Gt_le hly
  have hlM : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlM) hM) hlM
  simpa [mul_assoc] using this

theorem centralizer_le_of_mem_oVecL
    {t : G} (hS : Setting1273 G T L V t) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (hct : C.cd ⟨t, hS.t_mem⟩ ∈ oVecL) {U : Subgroup G} {v : ↥V} (hvU : (v : G) ∈ U)
    (hv : C.cd v ∈ oVecL) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hvU)).trans
    (centralizer_le_of_oVecL hS hC hct hv)

theorem exists_oVecL_of_hyperplane (h : Hyp1271 G T L V)
    {C : Coding ↥V} {c : ℕ} (hc : c ∈ oVecL) {U : Subgroup G} (hm : E3.mQuot V U = 1) :
    ∃ v : ↥V, (v : G) ∈ U ∧ C.cd v ∈ oVecL := by
  have hc64 := oVecL_lt c hc
  have hw64 := wV_lt c hc64
  have hidx : (U.subgroupOf V).index = 2 := by
    have e := E3.relIndex_eq_two_pow (isPGroup_V' h) U
    rw [hm] at e
    exact e
  by_cases h1 : (C.dc c : G) ∈ U
  · exact ⟨C.dc c, h1, by rw [C.cd_dc c hc64]; exact hc⟩
  by_cases h2 : (C.dc (wV c) : G) ∈ U
  · exact ⟨C.dc (wV c), h2, by rw [C.cd_dc _ hw64]; exact oVecL_wV c hc⟩
  refine ⟨C.dc c * C.dc (wV c), ?_, ?_⟩
  · have hmul := (Subgroup.mul_mem_iff_of_index_two hidx (a := C.dc c) (b := C.dc (wV c))).2
      ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
    exact hmul
  · rw [C.cd_mul, C.cd_dc c hc64, C.cd_dc _ hw64, xor_wV c hc64]
    exact oVecL_wV _ (oVecL_wV c hc)

omit [IsMulCommutative ↥V] in
theorem exists_autOn_fix_of_ne (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {U : Subgroup G}
    (hUV : U ≤ V) (hU : U ≠ ⊥)
    (hne : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ≠
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) :
    ∃ m, ∃ hmN : m ∈ Subgroup.normalizer (V : Set G),
      m ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) ∧
      conjAct V ⟨m, hmN⟩ ≠ 1 := by
  have hle : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le hUV)
  obtain ⟨m, hmU, hmV⟩ := Set.not_subset.1 fun hsub => hne (le_antisymm hsub hle)
  have hmN := mem_normalizer_of_mem_inf_centralizer h1222 h hUV hU hmU
  refine ⟨m, hmN, hmU, fun e => hmV ?_⟩
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hmU).1, (conjAct_eq_one' hmN).1 e⟩

theorem exists_invol_fix
    (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {U : Subgroup G} (hUV : U ≤ V) (h8 : 8 ≤ Nat.card U) {m : G}
    (hmN : m ∈ Subgroup.normalizer (V : Set G))
    (hmU : m ∈ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G))
    (hm1 : conjAct V ⟨m, hmN⟩ ≠ 1) :
    ∃ k : ℕ, (conjAct V ⟨m, hmN⟩) ^ k ≠ 1 ∧ ((conjAct V ⟨m, hmN⟩) ^ k) ^ 2 = 1 ∧
      (conjAct V ⟨m, hmN⟩) ^ k ∈ h.hyp.MVbar ∧
      ∀ u : ↥V, (u : G) ∈ U → (C.cB ((conjAct V ⟨m, hmN⟩) ^ k)).app (C.cd u) = C.cd u := by
  set a := conjAct V ⟨m, hmN⟩ with had
  have haM : a ∈ h.hyp.MVbar :=
    conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hmU).1, hmN⟩) hmN
  have hfix : ∀ u : ↥V, (u : G) ∈ U → a u = u := by
    intro u hu
    apply Subtype.ext
    rw [had, conjAct_val]
    have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hmU).2 _ hu
    rw [← this, mul_inv_cancel_right]
  have hfixc : ∀ u : ↥V, (u : G) ∈ U → (C.cB a).app (C.cd u) = C.cd u := fun u hu =>
    (C.apply_eq_self_iff a u).1 (hfix u hu)
  obtain ⟨k, hk1, hk2⟩ := exists_invol_pow (MVbar_code h hC haM).1 hm1
    (h8.trans (card_le_fixCount hUV hfixc))
  refine ⟨k, hk1, hk2, Subgroup.pow_mem _ haM k, fun u hu => ?_⟩
  exact (C.apply_eq_self_iff _ u).1 (pow_apply_eq_self (hfix u hu) k)

theorem centralizer_le_M_of_mQuot_le_two
    (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) (hE612 : ASInputs.AS_E_6_12) {t : G}
    (hS : Setting1273 G T L V t) {U : Subgroup G} (hUV : U ≤ V) (hm : E3.mQuot V U ≤ 2) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨C, hC⟩ := exists_std h1222 hS.hyp
  have hct := cd_t_mem_oVecL h1222 hS.hyp hC hS.t_mem hS.orbit_t
  have hV2 := isPGroup_V' hS.hyp
  have hyper : ∀ {U₁ : Subgroup G}, E3.mQuot V U₁ = 1 →
      Subgroup.centralizer (U₁ : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    intro U₁ hU₁
    obtain ⟨v, hvU, hv⟩ := exists_oVecL_of_hyperplane hS.hyp (C := C) hct hU₁
    exact centralizer_le_of_mem_oVecL hS hC.1 hct hvU hv
  rcases (show E3.mQuot V U = 0 ∨ E3.mQuot V U = 1 ∨ E3.mQuot V U = 2 by omega) with
    h0 | h1 | h2
  · rw [(E3.mQuot_eq_zero_iff hV2 hUV).1 h0]
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hS.t_mem)).trans hS.Gt_le
  · exact hyper h1
  · by_contra hno
    have hV64 := card_V h1222 hS.hyp
    have hU16 : Nat.card U = 16 := by
      have e := E3.card_eq_two_pow_mul hV2 hUV
      rw [hV64, h2] at e
      omega
    have hU0 : U ≠ ⊥ := fun hb => by
      rw [hb, Subgroup.card_bot] at hU16
      norm_num at hU16
    have hE := hypE61_1271 h331 h1222 h3228 hS.hyp
    by_cases heq : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G) =
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)
    · obtain ⟨⟨U₁, -, -, hm₁, hno₁⟩, -⟩ :=
        hE612 G T (Subgroup.normalizer (L : Set G)) V U hE hU0 hUV heq hno
      exact hno₁ (hyper hm₁)
    · obtain ⟨m, hmN, hmU, hm1⟩ := exists_autOn_fix_of_ne h1222 hS.hyp hUV hU0 heq
      obtain ⟨k, hk1, hk2, hkM, hkfix⟩ :=
        exists_invol_fix hS.hyp hC.1 hUV (by omega) hmN hmU hm1
      set y := (conjAct V ⟨m, hmN⟩) ^ k with hyd
      have hB := (MVbar_code hS.hyp hC.1 hkM).1
      have hBsq : (C.cB y).comp (C.cB y) = B6.id := by
        rw [← C.cB_mul, ← pow_two, hk2, C.cB_one]
      have hB1 : C.cB y ≠ B6.id := fun e => hk1 (C.cB_eq_one.1 e)
      have h16 : 16 ≤ fixCount (C.cB y) := hU16 ▸ card_le_fixCount hUV hkfix
      obtain ⟨c, hc, hcB⟩ := cert4_fix16_hyp _ hB hBsq hB1 h16
      have hcU := mem_of_fixCount_le hUV hkfix
        (by rw [hU16]; exact cert4_inv_fix16 _ hB hBsq hB1) (oVecL_lt c hc) hcB
      exact hno (centralizer_le_of_mem_oVecL hS hC.1 hct hcU
        (by rw [C.cd_dc c (oVecL_lt c hc)]; exact hc))

theorem centralizer_le_normalizer_of_mQuot_le_two
    (h331 : Stmt3_3_1)
    (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) (hE612 : ASInputs.AS_E_6_12) {t : G}
    (hS : Setting1273 G T L V t) {U : Subgroup G} (hUV : U ≤ V) (hm : E3.mQuot V U ≤ 2) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    rw [mQuot_bot (card_V h1222 hS.hyp)] at hm
    omega
  intro c hc
  exact mem_normalizer_of_mem_inf_centralizer h1222 hS.hyp hUV hU0
    (Subgroup.mem_inf.2 ⟨centralizer_le_M_of_mQuot_le_two h331 h1222 h3228 hE612 hS hUV hm hc,
      hc⟩)

theorem two_lt_rParam
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight) (hE612 : ASInputs.AS_E_6_12) {t : G}
    (hS : Setting1273 G T L V t) : 2 < E3.rParam V := by
  have h3 : (3 : ℕ∞) ≤ E3.rParam V := by
    unfold E3.rParam
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨hUV, hno⟩ := hU
    by_contra hlt
    push Not at hlt
    have hm : E3.mQuot V U ≤ 2 := by
      have : E3.mQuot V U < 3 := by exact_mod_cast hlt
      omega
    exact hno (centralizer_le_normalizer_of_mQuot_le_two h331 h1222 h3228 hE612 hS hUV hm)
  exact lt_of_lt_of_le (by norm_num) h3

theorem sParam_eq_two
    (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight) (hE612 : ASInputs.AS_E_6_12) {t : G}
    (hS : Setting1273 G T L V t) (hV : IsElemAbelian 2 V) : E3.sParam hV = 2 := by
  have hNM := normalizer_V_le_M h331 h1222 hS.hyp
  have hauto : autOn (⊤ : Subgroup G) V = hS.hyp.hyp.MVbar := by
    apply le_antisymm
    · intro a ha
      obtain ⟨x, hx, -, rfl⟩ := mem_autOn'.1 ha
      exact conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨hNM hx, hx⟩) hx
    · exact A4.autOn_mono le_top
  have hm : E3.mParam (autI hV ⊤) = 2 := by
    rw [autI_eq_autOn]
    have := mParam_MVbar h1222 hS.hyp
    rw [← hauto] at this
    exact this
  have h2 : ((2 : ℕ) : ℕ∞) ≤ E3.rParam V := by
    have := two_lt_rParam h331 h1222 h3228 hE612 hS
    exact le_of_lt (by exact_mod_cast this)
  unfold E3.sParam
  rw [hm, min_eq_right h2]
  rfl

end CFSG.Quasithin.H13.S127.Mod

end
