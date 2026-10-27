module

public import CFSG.RankThree.PartTwo.Sec21.FF84S47Model
public import CFSG.RankThree.PartTwo.Sec21.FF84S47Transport
public import CFSG.RankThree.PartTwo.Sec21.FF84S4UData

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8 A8s)

@[expose] def A_PiStar_stmt : Prop := PiStar A8s Pm 2 = {Ua, Ub}

@[expose] def A_U_max_stmt : Prop :=
  (Ua ∈ PiStar A8s (Subgroup.zpowers cc) 2 ∧ Ua ∈ PiStar A8s (Subgroup.zpowers dd) 2) ∧
  (Ub ∈ PiStar A8s (Subgroup.zpowers cc) 2 ∧ Ub ∈ PiStar A8s (Subgroup.zpowers dd) 2)

variable {G : Type} [Group G] [Finite G] {b : G} {L B K : Subgroup G} {b₁ b₂ : G}

private theorem mem_sup_of_comm' {Z T : Subgroup G} (hc : ∀ z ∈ Z, ∀ t ∈ T, z * t = t * z) {x : G}
    (hx : x ∈ Z ⊔ T) : ∃ z ∈ Z, ∃ t ∈ T, z * t = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ z ∈ Z, ∃ t ∈ T, z * t = x}
      mul_mem' := by
        rintro _ _ ⟨z, hz, t, ht, rfl⟩ ⟨z', hz', t', ht', rfl⟩
        refine ⟨z * z', mul_mem hz hz', t * t', mul_mem ht ht', ?_⟩
        have : t * z' = z' * t := (hc z' hz' t ht).symm
        calc z * z' * (t * t') = z * (z' * t) * t' := by group
          _ = z * (t * z') * t' := by rw [this]
          _ = z * t * (z' * t') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨z, hz, t, ht, rfl⟩
        refine ⟨z⁻¹, inv_mem hz, t⁻¹, inv_mem ht, ?_⟩
        have : t⁻¹ * z⁻¹ = z⁻¹ * t⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, (hc z hz t ht)]
        rw [mul_inv_rev, this] }
  have : Z ⊔ T ≤ S := sup_le (fun z hz => ⟨z, hz, 1, one_mem _, by simp⟩)
    (fun t ht => ⟨1, one_mem _, t, ht, by simp⟩)
  exact this hx

theorem zpow_comm_of_mem_cen {t : G} (ht : t ∈ Cen b) (i : ℤ) : b ^ i * t = t * b ^ i :=
  (Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 ht).symm i).eq

theorem cen_decomp (h : FF84Post b L B K b₁ b₂) {v : G} (hv : v ∈ Cen b) :
    ∃ i : ℤ, ∃ l ∈ L, b ^ i * l = v := by
  rw [← h.cb] at hv
  obtain ⟨z, hz, l, hl, rfl⟩ := mem_sup_of_comm' (fun z hz t ht => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact zpow_comm_of_mem_cen (h.sec.hyp.hLC ht) i) hv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨i, l, hl, rfl⟩

theorem le_L_of_isPGroup (h : FF84Post b L B K b₁ b₂) {V : Subgroup G} (hV : V ≤ Cen b)
    (hp : IsPGroup 2 V) : V ≤ L := by
  intro v hv
  obtain ⟨i, l, hl, rfl⟩ := cen_decomp h (hV hv)
  obtain ⟨k, hk⟩ := hp ⟨_, hv⟩
  have hk' : (b ^ i * l) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute (b ^ i) l := (zpow_comm_of_mem_cen (h.sec.hyp.hLC hl) i)
  rw [hcomm.mul_pow, ← zpow_natCast, ← zpow_mul, mul_eq_one_iff_eq_inv] at hk'
  have hmem : b ^ (i * (2 ^ k : ℕ)) ∈ Subgroup.zpowers b ⊓ L := by
    refine ⟨Subgroup.zpow_mem_zpowers _ _, ?_⟩
    rw [hk']
    exact L.inv_mem (L.pow_mem hl _)
  rw [h.cbL, Subgroup.mem_bot] at hmem
  have h3 : (3 : ℤ) ∣ i * (2 ^ k : ℕ) := by
    have h3 : ((orderOf b : ℕ) : ℤ) ∣ i * (2 ^ k : ℕ) := orderOf_dvd_iff_zpow_eq_one.2 hmem
    rw [h.sec.hyp.ord] at h3
    simpa using h3
  have h3' : (3 : ℤ) ∣ i := by
    have hcop : IsCoprime (3 : ℤ) ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      exact (Int.isCoprime_iff_gcd_eq_one.2 (by
        have : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
        exact_mod_cast this))
    exact hcop.dvd_of_dvd_mul_right h3
  obtain ⟨m, rfl⟩ := h3'
  have : b ^ (3 * m) = 1 := by
    rw [zpow_mul]
    have : b ^ (3 : ℤ) = 1 := by
      have := h.sec.hyp.ord
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ← this, pow_orderOf_eq_one]
    rw [this, one_zpow]
  rw [this, one_mul]
  exact hl

theorem B_le_nor_iff (h : FF84Post b L B K b₁ b₂) {V : Subgroup G} (hV : V ≤ L) :
    B ≤ Nor V ↔ B ⊓ L ≤ Nor V := by
  constructor
  · intro hB x hx
    exact hB hx.1
  · intro hBL
    apply le_nor_of_conj
    intro x hx v hv
    have hxC : x ∈ Cen b := h.sec.sylB.1 hx
    obtain ⟨i, l, hl, rfl⟩ := cen_decomp h hxC
    have hbB : b ∈ B := mem_b h.sec
    have hlB : l ∈ B := by
      have := mul_mem (inv_mem (zpow_mem hbB i)) hx
      simpa using this
    have hw : l * v * l⁻¹ ∈ V := conj_mem_of_le_nor hBL ⟨hlB, hl⟩ hv
    have hwc : l * v * l⁻¹ ∈ Cen b := h.sec.hyp.hLC (hV hw)
    have := zpow_comm_of_mem_cen hwc i
    have e : b ^ i * l * v * (b ^ i * l)⁻¹ = (b ^ i * (l * v * l⁻¹)) * (b ^ i)⁻¹ := by group
    rw [e, this]
    simpa using hw

theorem piStar_cen_iff (h : FF84Post b L B K b₁ b₂) {A A' U : Subgroup G}
    (hnor : ∀ V : Subgroup G, V ≤ L → (A ≤ Nor V ↔ A' ≤ Nor V)) :
    U ∈ PiStar (Cen b) A 2 ↔ U ∈ PiStar L A' 2 := by
  constructor
  · rintro ⟨hUC, hUp, hUn, hmax⟩
    have hUL := le_L_of_isPGroup h hUC hUp
    refine ⟨hUL, hUp, (hnor U hUL).1 hUn, fun V hUV hVL hVp hVn => ?_⟩
    exact hmax V hUV (hVL.trans h.sec.hyp.hLC) hVp ((hnor V hVL).2 hVn)
  · rintro ⟨hUL, hUp, hUn, hmax⟩
    refine ⟨hUL.trans h.sec.hyp.hLC, hUp, (hnor U hUL).2 hUn, fun V hUV hVC hVp hVn => ?_⟩
    have hVL := le_L_of_isPGroup h hVC hVp
    exact hmax V hUV hVL hVp ((hnor V hVL).1 hVn)

theorem S47_PiStar_eq (h : FF84Post b L B K b₁ b₂) :
    ∀ U : Subgroup G, U ∈ PiStar (Cen b) B 2 ↔ U ∈ PiStar L (B ⊓ L) 2 :=
  fun _ => piStar_cen_iff h fun _ hV => B_le_nor_iff h hV

theorem trX_inf_B_L (h : FF84Post b L B K b₁ b₂) (e : ↥L ≃* ↥A8s)
    (he₁ : ∀ x : ↥L, (x : G) = b₁ → ((e x : A8s) : P8) = cc)
    (he₂ : ∀ x : ↥L, (x : G) = b₂ → ((e x : A8s) : P8) = dd) :
    trX e (B ⊓ L) = Pm := by
  have hb₁ : b₁ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₁).2
  have hb₂ : b₂ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₂).2
  rw [h.sec.gen, trX_closure_pair e hb₁ hb₂, he₁ ⟨b₁, hb₁⟩ rfl, he₂ ⟨b₂, hb₂⟩ rfl]
  rfl

@[expose] def UProps (Y : Subgroup P8) : Prop :=
  IsElemAb 2 4 Y ∧ IsElemAb 2 2 (Y ⊓ Cen cc) ∧ IsElemAb 2 2 (Y ⊓ Cen dd) ∧ Y ⊓ Cen (cc * dd) = ⊥ ∧
    Y ⊓ Cen (cc * dd ^ 2) = ⊥ ∧ Y ∈ PiStar A8s (Subgroup.zpowers cc) 2 ∧
    Y ∈ PiStar A8s (Subgroup.zpowers dd) 2

theorem uProps_Ua_Ub (hmax : A_U_max_stmt) : UProps Ua ∧ UProps Ub := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, ⟨b1, b2, b3, b4, b5⟩⟩ := A_U_data_basic
  exact ⟨⟨a3, a4, a5, a6, a7, hmax.1.1, hmax.1.2⟩, ⟨b1, b2, b3, b4, b5, hmax.2.1, hmax.2.2⟩⟩

theorem props_of_trX (h : FF84Post b L B K b₁ b₂) (e : ↥L ≃* ↥A8s)
    (he₁ : ∀ x : ↥L, (x : G) = b₁ → ((e x : A8s) : P8) = cc)
    (he₂ : ∀ x : ↥L, (x : G) = b₂ → ((e x : A8s) : P8) = dd) {U : Subgroup G} (hU : U ≤ L)
    (hY : UProps (trX e U)) :
    IsElemAb 2 4 U ∧ IsElemAb 2 2 (U ⊓ Cen b₁) ∧ IsElemAb 2 2 (U ⊓ Cen b₂) ∧
      U ⊓ Cen (b₁ * b₂) = ⊥ ∧ U ⊓ Cen (b₁ * b₂ ^ 2) = ⊥ ∧
      U ∈ PiStar (Cen b) (Subgroup.zpowers b₁) 2 ∧ U ∈ PiStar (Cen b) (Subgroup.zpowers b₂) 2 := by
  have hb₁ : b₁ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₁).2
  have hb₂ : b₂ ∈ L := (Subgroup.mem_inf.1 h.sec.hb₂).2
  have e₁ := he₁ ⟨b₁, hb₁⟩ rfl
  have e₂ := he₂ ⟨b₂, hb₂⟩ rfl
  have hb₁₂ : b₁ * b₂ ∈ L := mul_mem hb₁ hb₂
  have hb₁₂' : b₁ * b₂ ^ 2 ∈ L := mul_mem hb₁ (pow_mem hb₂ 2)
  have e₁₂ : ((e ⟨b₁ * b₂, hb₁₂⟩ : A8s) : P8) = cc * dd := by
    have : (⟨b₁ * b₂, hb₁₂⟩ : ↥L) = ⟨b₁, hb₁⟩ * ⟨b₂, hb₂⟩ := rfl
    rw [this, map_mul, Subgroup.coe_mul, e₁, e₂]
  have e₁₂' : ((e ⟨b₁ * b₂ ^ 2, hb₁₂'⟩ : A8s) : P8) = cc * dd ^ 2 := by
    have : (⟨b₁ * b₂ ^ 2, hb₁₂'⟩ : ↥L) = ⟨b₁, hb₁⟩ * ⟨b₂, hb₂⟩ ^ 2 := rfl
    rw [this, map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, e₁, e₂]
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := hY
  have hUb₁ : U ⊓ Cen b₁ ≤ L := inf_le_left.trans hU
  have hUb₂ : U ⊓ Cen b₂ ≤ L := inf_le_left.trans hU
  refine ⟨(isElemAb_trX_iff e (by norm_num) hU).1 y1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (isElemAb_trX_iff e (by norm_num) hUb₁).1 ?_
    rw [trX_inf_cen e U hb₁, e₁]; exact y2
  · refine (isElemAb_trX_iff e (by norm_num) hUb₂).1 ?_
    rw [trX_inf_cen e U hb₂, e₂]; exact y3
  · refine (trX_eq_bot_iff e (inf_le_left.trans hU)).1 ?_
    rw [trX_inf_cen e U hb₁₂, e₁₂]; exact y4
  · refine (trX_eq_bot_iff e (inf_le_left.trans hU)).1 ?_
    rw [trX_inf_cen e U hb₁₂', e₁₂']; exact y5
  · rw [piStar_cen_iff h (A := Subgroup.zpowers b₁) (A' := Subgroup.zpowers b₁) (fun _ _ => Iff.rfl)]
    have hz : Subgroup.zpowers b₁ ≤ L := (Subgroup.zpowers_le).2 hb₁
    rw [trX_piStar_iff e hz hU, trX_zpowers e hb₁, e₁]; exact y6
  · rw [piStar_cen_iff h (A := Subgroup.zpowers b₂) (A' := Subgroup.zpowers b₂) (fun _ _ => Iff.rfl)]
    have hz : Subgroup.zpowers b₂ ≤ L := (Subgroup.zpowers_le).2 hb₂
    rw [trX_piStar_iff e hz hU, trX_zpowers e hb₂, e₂]; exact y7

theorem S47_transport (hA : A8Model L) (hP : A_PiStar_stmt)
    (hmax : A_U_max_stmt) (h : FF84Post b L B K b₁ b₂) :
    ∃ U₁ U₂ : Subgroup G, U₁ ≠ U₂ ∧ PiStar (Cen b) B 2 = {U₁, U₂} ∧ U₁ ⊓ U₂ = ⊥ ∧
      ∀ U ∈ PiStar (Cen b) B 2, IsElemAb 2 4 U ∧ IsElemAb 2 2 (U ⊓ Cen b₁) ∧
        IsElemAb 2 2 (U ⊓ Cen b₂) ∧ U ⊓ Cen (b₁ * b₂) = ⊥ ∧ U ⊓ Cen (b₁ * b₂ ^ 2) = ⊥ ∧
        U ∈ PiStar (Cen b) (Subgroup.zpowers b₁) 2 ∧
        U ∈ PiStar (Cen b) (Subgroup.zpowers b₂) 2 := by
  obtain ⟨e, he₁, he₂⟩ := M0_model hA h
  have hBP := trX_inf_B_L h e he₁ he₂
  have hBL : B ⊓ L ≤ L := inf_le_right
  have hUa : Ua ∈ PiStar A8s Pm 2 := by rw [hP]; exact Or.inl rfl
  have hUb : Ub ∈ PiStar A8s Pm 2 := by rw [hP]; exact Or.inr rfl
  obtain ⟨hUp, hUq⟩ := uProps_Ua_Ub hmax
  set U₁ : Subgroup G := trX e.symm Ua with hU₁
  set U₂ : Subgroup G := trX e.symm Ub with hU₂
  have hU₁L : U₁ ≤ L := trX_le _ _
  have hU₂L : U₂ ≤ L := trX_le _ _
  have hU₁e : trX e U₁ = Ua := trX_trX_symm e hUa.1
  have hU₂e : trX e U₂ = Ub := trX_trX_symm e hUb.1
  have hne : U₁ ≠ U₂ := by
    intro hc
    have : Ua = Ub := by rw [← hU₁e, ← hU₂e, hc]
    exact A_U_data_basic.1.1 this
  have hmem : ∀ U : Subgroup G, U ∈ PiStar (Cen b) B 2 ↔ U = U₁ ∨ U = U₂ := by
    intro U
    rw [S47_PiStar_eq h]
    constructor
    · intro hU
      have hUL := hU.1
      have := (trX_piStar_iff e hBL hUL).1 hU
      rw [hBP, hP] at this
      rcases this with h1 | h1
      · exact Or.inl (trX_injOn e hUL hU₁L (h1.trans hU₁e.symm))
      · exact Or.inr (trX_injOn e hUL hU₂L (h1.trans hU₂e.symm))
    · rintro (rfl | rfl)
      · refine (trX_piStar_iff e hBL hU₁L).2 ?_
        rw [hBP, hU₁e]; exact hUa
      · refine (trX_piStar_iff e hBL hU₂L).2 ?_
        rw [hBP, hU₂e]; exact hUb
  refine ⟨U₁, U₂, hne, ?_, ?_, ?_⟩
  · ext U
    rw [hmem U]
    simp
  · refine (trX_eq_bot_iff e (inf_le_left.trans hU₁L)).1 ?_
    rw [trX_inf, hU₁e, hU₂e]
    exact A_U_data_basic.1.2.1
  · intro U hU
    rcases (hmem U).1 hU with rfl | rfl
    · exact props_of_trX h e he₁ he₂ hU₁L (by rw [hU₁e]; exact hUp)
    · exact props_of_trX h e he₁ he₂ hU₂L (by rw [hU₂e]; exact hUq)

theorem ff84_4_7_of
    (h43 : FF84_4_3) (h44 : FF84_4_4) (h46 : FF84_4_6) (hP : A_PiStar_stmt)
    (hmax : A_U_max_stmt) : FF84_4_7 := by
  intro G _ _ b L B K b₁ b₂ hs
  have hpost := post_of_items h43 h44 h46 hs
  have hA : A8Model L := a8Model_of_hyp hs.hyp
  obtain ⟨U₁, U₂, hne, hPi, hbot, hU⟩ := S47_transport hA hP hmax hpost
  refine ⟨U₁, U₂, hne, hPi, hbot, fun U hUm => ?_⟩
  obtain ⟨a, b, c, -, -, d, -⟩ := hU U hUm
  exact ⟨a, b, c, Or.inl d⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
