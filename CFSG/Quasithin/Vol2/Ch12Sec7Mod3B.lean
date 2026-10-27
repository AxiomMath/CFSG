module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModU
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod3A
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7ModL

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem r1_sub_s0 : ∀ r ∈ r1, r ∈ s0 := by decide

theorem r2_sub_s0 : ∀ r ∈ r2, r ∈ s0 := by decide

theorem r2_comm' : ∀ x ∈ r2, ∀ y ∈ r2, x.comp y = y.comp x := by decide

theorem r2_fixAll : ∀ c < 64, (∀ r ∈ r2, r.app c = c) ↔ c ∈ l2c := by decide

theorem r2_ne_id : ∃ r ∈ r2, r ≠ B6.id := by decide

theorem r1_bad : ∀ r ∈ r1, r ≠ B6.id → ∃ c < 64, r.app c = c ∧ c ∉ p1c := by decide

theorem p1c_five : 5 ∈ p1c ∧ 10 ∈ p1c ∧ wV 5 = 10 ∧ wV 10 = 15 := by decide

theorem s0_pairs : ∀ x ∈ s0, ∀ y ∈ s0, x ≠ B6.id → y ≠ B6.id → x ≠ y → x.comp x = B6.id →
    y.comp y = B6.id → x.comp y = y.comp x →
    ((∀ z ∈ s0, z.comp z = B6.id → z.comp x = x.comp z → z.comp y = y.comp z → z ∈ r1) ∧
      ∀ r ∈ r1, r = B6.id ∨ r = x ∨ r = y ∨ r = x.comp y) ∨
    ((∀ z ∈ s0, z.comp z = B6.id → z.comp x = x.comp z → z.comp y = y.comp z → z ∈ r2) ∧
      ∀ r ∈ r2, r = B6.id ∨ r = x ∨ r = y ∨ r = x.comp y) := by decide

theorem card_le_of_codes {W : Type} [CommGroup W] (C : Coding W) {A : Subgroup (MulAut W)}
    {l : List B6} (hl : l.Nodup) (h : ∀ a ∈ A, C.cB a ∈ l) : Nat.card A ≤ l.length := by
  classical
  have hinj : Function.Injective (fun a : A => (⟨C.cB a, h a a.2⟩ : {B : B6 // B ∈ l})) :=
    fun a b hab => Subtype.ext (C.cB_injective (congrArg Subtype.val hab))
  have hle := Nat.card_le_card_of_injective _ hinj
  have e2 : {B : B6 // B ∈ l} ≃ ↥l.toFinset := Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup hl] at hle
  exact hle

theorem padicValNat_lt_two {n : ℕ} (h0 : n ≠ 0) (h2 : n ≤ 2) : padicValNat 2 n < 2 := by
  interval_cases n
  · exact absurd rfl h0
  · simp
  · simp

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem isPGroup_autOn_T (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) : IsPGroup 2 (autOn T V) := by
  have h2 : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (V : Set G))) :=
    h.hyp.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe (T_le_normalizer h1222 h)).symm
  exact h2.map _

omit [IsMulCommutative ↥V] in
theorem autOn_T_inf_L (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    autOn T V ⊓ autOn L V = autOn (T ⊓ L) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : autOn (T ⊓ L) V ≤ autOn T V ⊓ autOn L V :=
    le_inf (A4.autOn_mono inf_le_left) (A4.autOn_mono inf_le_right)
  have hpK : IsPGroup 2 ↥(autOn T V ⊓ autOn L V) :=
    (isPGroup_autOn_T h1222 h).to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpK
  have hd : Nat.card ↥(autOn T V ⊓ autOn L V) ∣ 1080 := by
    rw [← card_autOn_L h.hatA6 (L_le_normalizer h)]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h8 : Nat.card ↥(autOn (T ⊓ L) V) = 8 := card_autOn_inf h
  have hd8 : 8 ∣ Nat.card ↥(autOn T V ⊓ autOn L V) := h8 ▸ Subgroup.card_dvd_of_le hle
  rw [hk] at hd hd8
  have hk3 : k = 3 := by
    have h1 : k ≤ 3 := by
      by_contra hk3
      have : 2 ^ 4 ∣ 1080 := dvd_trans (pow_dvd_pow 2 (by omega)) hd
      norm_num at this
    have h2 : 3 ≤ k := by
      by_contra hk3
      have : 8 ∣ 2 ^ 2 := dvd_trans hd8 (pow_dvd_pow 2 (by omega))
      norm_num at this
    omega
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hk, hk3, h8]
  norm_num

theorem mQuot_inf_L_lt
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {A : Subgroup (MulAut ↥V)} (hA : A ≤ h.hyp.MVbar) :
    E3.mQuot A (A ⊓ autOn L V) < 2 := by
  unfold E3.mQuot
  have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
  have hi : (autOn L V).relIndex h.hyp.MVbar ≤ 2 := by
    by_cases hne : h.hyp.MVbar = autOn L V
    · rw [hne, Subgroup.relIndex_self]
      norm_num
    · have hc := card_MVbar_of_ne h hC hne
      have e := Subgroup.relIndex_mul_card (autOn L V) h.hyp.MVbar
      rw [inf_eq_left.2 hLM, card_autOn_L h.hatA6 (L_le_normalizer h), hc] at e
      omega
  have h0 : (autOn L V).relIndex h.hyp.MVbar ≠ 0 := E3.relIndex_ne_zero' _ _
  rw [Subgroup.inf_relIndex_left]
  exact padicValNat_lt_two (E3.relIndex_ne_zero' _ _)
    ((Subgroup.relIndex_le_of_le_right hA h0).trans hi)

theorem le_L_of_mem_aSet
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    {A : Subgroup (MulAut ↥V)} (hA : A ∈ E3.aSet 2 (autOn T V)) : A ≤ autOn L V := by
  obtain ⟨hAT, -, -, hAc⟩ := hA
  have hTM : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  intro a ha
  by_contra haL
  have hsemi := (MVbar_code h hC.1 (hTM (hAT ha))).2.2.2 haL
  have hfix := hAc (A ⊓ autOn L V) inf_le_left (mQuot_inf_L_lt h hC.1 (hAT.trans hTM))
  have hf : ∀ c ∈ p1c, c < 64 → C.dc c ∈ fixV A := by
    intro c hc hc64
    rw [← hfix]
    intro b hb
    obtain ⟨hbA, hbL⟩ := Subgroup.mem_inf.1 hb
    have hbs : C.cB b ∈ s0 :=
      (hC.2 b).1 (autOn_T_inf_L h1222 h ▸ Subgroup.mem_inf.2 ⟨hAT hbA, hbL⟩)
    apply C.cd_injective
    rw [C.cd_apply, C.cd_dc c hc64]
    exact (fix_s0 c hc64).2 hc _ hbs
  obtain ⟨h5, h10, hw5, hw10⟩ := p1c_five
  have c5 : (C.cB a).app 5 = 5 := by
    have := congrArg C.cd (hf 5 h5 (by norm_num) a ha)
    rwa [C.cd_apply, C.cd_dc 5 (by norm_num)] at this
  have c10 : (C.cB a).app 10 = 10 := by
    have := congrArg C.cd (hf 10 h10 (by norm_num) a ha)
    rwa [C.cd_apply, C.cd_dc 10 (by norm_num)] at this
  have := hsemi 5 (by norm_num)
  rw [c5, hw5, c10, hw10] at this
  exact absurd this (by norm_num)

theorem mem_autOn_R1_iff
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    (a : MulAut ↥V) : a ∈ autOn (R1 T L V) V ↔ C.cB a ∈ r1 := by
  rw [R1, P1, V1_eq h hC]
  exact mem_autOn_R h1222 h hC.1 p1c_lt id_mem_r1 r1_closed r1_sub r1_sq cert_n1 cert_m1 a

theorem mem_autOn_R2_iff
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    (a : MulAut ↥V) : a ∈ autOn (R2 T L V) V ↔ C.cB a ∈ r2 := by
  rw [R2, P2, V2_eq h hC]
  exact mem_autOn_R h1222 h hC.1 l2c_lt id_mem_r2 r2_closed r2_sub r2_sq cert_n2 cert_m2 a

theorem eq_R2_of_mem_aSet
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {A : Subgroup (MulAut ↥V)}
    (hA : A ∈ E3.aSet 2 (autOn T V)) : A = autOn (R2 T L V) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hAL := le_L_of_mem_aSet h1222 h hC hA
  have h2le := E3.le_mQuot_bot_of_mem_aSet hA
  obtain ⟨hAT, hA1, hAe, hAc⟩ := hA
  have hs0 : ∀ a ∈ A, C.cB a ∈ s0 := fun a ha =>
    (hC.2 a).1 (autOn_T_inf_L h1222 h ▸ Subgroup.mem_inf.2 ⟨hAT ha, hAL ha⟩)
  have hsq : ∀ a ∈ A, (C.cB a).comp (C.cB a) = B6.id := fun a ha => by
    rw [← C.cB_mul, ← pow_two, hAe.2 a ha, C.cB_one]
  have hcm : ∀ a ∈ A, ∀ b ∈ A, (C.cB a).comp (C.cB b) = (C.cB b).comp (C.cB a) :=
    fun a ha b hb => by rw [← C.cB_mul, ← C.cB_mul, hAe.1 a ha b hb]
  obtain ⟨⟨x, hxA⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA1
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  obtain ⟨y, hyA, hy1, hyx⟩ : ∃ y ∈ A, y ≠ 1 ∧ y ≠ x := by
    by_contra hno
    push Not at hno
    have hAle : A ≤ Subgroup.zpowers x := fun y hy => by
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Subgroup.one_mem _
      · rw [hno y hy hy1]
        exact Subgroup.mem_zpowers x
    have hcard := Subgroup.card_le_of_le hAle
    rw [Nat.card_zpowers, orderOf_eq_prime (hAe.2 x hxA) hx1'] at hcard
    have hm : E3.mQuot A ⊥ < 2 := by
      unfold E3.mQuot
      rw [Subgroup.relIndex_bot_left]
      exact padicValNat_lt_two Nat.card_pos.ne' hcard
    omega
  have hcx1 : C.cB x ≠ B6.id := fun e => hx1' (C.cB_eq_one.1 e)
  have hcy1 : C.cB y ≠ B6.id := fun e => hy1 (C.cB_eq_one.1 e)
  have hcxy : C.cB x ≠ C.cB y := fun e => hyx (C.cB_injective e).symm
  have hcover : ∀ l : List B6, (∀ r ∈ l, r = B6.id ∨ r = C.cB x ∨ r = C.cB y ∨
      r = (C.cB x).comp (C.cB y)) → ∀ r ∈ l, ∃ a ∈ A, C.cB a = r := by
    intro l hl r hr
    rcases hl r hr with e | e | e | e
    · exact ⟨1, A.one_mem, by rw [e, C.cB_one]⟩
    · exact ⟨x, hxA, e.symm⟩
    · exact ⟨y, hyA, e.symm⟩
    · exact ⟨x * y, A.mul_mem hxA hyA, by rw [e, C.cB_mul]⟩
  rcases s0_pairs _ (hs0 x hxA) _ (hs0 y hyA) hcx1 hcy1 hcxy (hsq x hxA) (hsq y hyA)
      (hcm x hxA y hyA) with ⟨hmax, hcov⟩ | ⟨hmax, hcov⟩
  ·
    exfalso
    have hAr1 : ∀ a ∈ A, C.cB a ∈ r1 := fun a ha =>
      hmax _ (hs0 a ha) (hsq a ha) (hcm a ha x hxA) (hcm a ha y hyA)
    have hcard : Nat.card A ≤ 4 := card_le_of_codes C r1_nodup hAr1
    have hB : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.2 hxA
    have hm : E3.mQuot A (Subgroup.zpowers x) < 2 := by
      unfold E3.mQuot
      have e := Subgroup.relIndex_mul_card (Subgroup.zpowers x) A
      rw [inf_eq_left.2 hB, Nat.card_zpowers, orderOf_eq_prime (hAe.2 x hxA) hx1'] at e
      exact padicValNat_lt_two (E3.relIndex_ne_zero' _ _) (by omega)
    have hfix := hAc _ hB hm
    obtain ⟨c, hc, hcx, hcp⟩ := r1_bad _ (hAr1 x hxA) hcx1
    have hv : C.dc c ∈ fixV (Subgroup.zpowers x) := by
      rw [mem_fixV_zpowers]
      apply C.cd_injective
      rw [C.cd_apply, C.cd_dc c hc]
      exact hcx
    rw [hfix] at hv
    apply hcp
    rw [← r1_fix c hc]
    intro r hr
    obtain ⟨a, ha, rfl⟩ := hcover r1 hcov r hr
    have := congrArg C.cd (hv a ha)
    rwa [C.cd_apply, C.cd_dc c hc] at this
  ·
    apply le_antisymm
    · intro a ha
      exact (mem_autOn_R2_iff h1222 h hC a).2
        (hmax _ (hs0 a ha) (hsq a ha) (hcm a ha x hxA) (hcm a ha y hyA))
    · intro a ha
      obtain ⟨b, hb, hba⟩ := hcover r2 hcov _ ((mem_autOn_R2_iff h1222 h hC a).1 ha)
      rw [← C.cB_injective hba]
      exact hb

theorem R2_mem_aSet
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    autOn (R2 T L V) V ∈ E3.aSet 2 (autOn T V) := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  have hR := mem_autOn_R2_iff h1222 h hC
  have h4 : Nat.card ↥(autOn (R2 T L V) V) = 4 := (lemma12_7_2_four h1222 h).2.2.1
  refine ⟨fun a ha => ?_, ?_, ⟨fun a ha b hb => ?_, fun a ha => ?_⟩, fun B hB hm => ?_⟩
  · exact A4.autOn_mono inf_le_left ((hC.2 a).2 (r2_sub_s0 _ ((hR a).1 ha)))
  · intro hb
    obtain ⟨r, hr, hr1⟩ := r2_ne_id
    obtain ⟨a, rfl⟩ := hC.1.2 r (r2_sub r hr).1
    have ha : a ∈ autOn (R2 T L V) V := (hR a).2 hr
    rw [hb, Subgroup.mem_bot] at ha
    exact hr1 (by rw [ha, C.cB_one])
  · apply C.cB_injective
    rw [C.cB_mul, C.cB_mul]
    exact r2_comm' _ ((hR a).1 ha) _ ((hR b).1 hb)
  · apply C.cB_injective
    rw [pow_two, C.cB_mul, C.cB_one]
    exact r2_sq _ ((hR a).1 ha)
  · have hB1 : B ≠ ⊥ := by
      rintro rfl
      rw [mQuot_bot (n := 2) (by rw [h4]; norm_num)] at hm
      omega
    obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    have hb1' : b ≠ 1 := fun e => hb1 (Subtype.ext e)
    have hbr := (hR b).1 (hB hbB)
    have hcb1 : C.cB b ≠ B6.id := fun e => hb1' (C.cB_eq_one.1 e)
    apply le_antisymm
    · intro v hv x hx
      have hvl : C.cd v ∈ l2c := by
        have := (C.apply_eq_self_iff b v).1 (hv b hbB)
        exact (r2_fix _ hbr hcb1 _ (C.cd_lt v)).1 this
      exact (C.apply_eq_self_iff x v).2 ((r2_fixAll _ (C.cd_lt v)).2 hvl _ ((hR x).1 hx))
    · intro v hv x hx
      exact hv x (hB hx)

theorem aParam_MVbar
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) : E3.aParam h.hyp.MVbar = 2 := by
  have hR2 := R2_mem_aSet h1222 h
  have hTM : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  have hR2M : autOn (R2 T L V) V ∈ E3.aSet 2 h.hyp.MVbar := E3.aSet_mono hTM hR2
  have hev := E3.even_card_of_isPGroup hR2M.1 (E3.isPGroup_of_isElemAbelian2 hR2M.2.2.1)
    hR2M.2.1
  have h4 : Nat.card ↥(autOn (R2 T L V) V) = 4 := (lemma12_7_2_four h1222 h).2.2.1
  simp only [E3.aParam, hev, ↓reduceIte]
  apply le_antisymm
  · refine csSup_le ⟨2, by norm_num, _, hR2M⟩ ?_
    rintro k ⟨-, A, hA⟩
    by_contra hk2
    push Not at hk2
    have hA3 : A ∈ E3.aSet 3 h.hyp.MVbar := E3.aSet_anti (by omega) _ hA
    obtain ⟨m, -, hm⟩ := exists_conj_le hTM (isPGroup_autOn_T h1222 h) (odd_index_T h1222 h)
      hA3.1 (E3.isPGroup_of_isElemAbelian2 hA3.2.2.1)
    have hA' : A.map (MulAut.congr m).toMonoidHom ∈ E3.aSet 3 (autOn T V) := by
      refine aSet_map_congr hA3 m ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, congr_eq]
      exact hm a ha
    have heq := eq_R2_of_mem_aSet h1222 h (E3.aSet_anti (by norm_num) _ hA')
    have h3 := E3.le_mQuot_bot_of_mem_aSet hA'
    rw [heq, mQuot_bot (n := 2) (by rw [h4]; norm_num)] at h3
    omega
  · exact le_csSup (E3.aSet_bddAbove _) ⟨by norm_num, _, hR2M⟩

theorem lemma12_7_3_of
    (h1222 : Stmt12_2_2) : Lemma12_7_3 := by
  intro G _ _ T L V _ h
  refine ⟨?_, aParam_MVbar h1222 h⟩
  ext A
  rw [Set.mem_singleton_iff]
  constructor
  · exact eq_R2_of_mem_aSet h1222 h
  · rintro rfl
    exact R2_mem_aSet h1222 h

end CFSG.Quasithin.H13.S127.Mod

end
