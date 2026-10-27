module

public import CFSG.Quasithin.Recognition.HSTypeL12j
public import CFSG.Quasithin.Recognition.HSTypeL12d
public import CFSG.Quasithin.Recognition.HSTypeL12i

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.A4 CFSG.Quasithin

variable {G : Type*} [Group G]

abbrev hsR2 (V V₂ : Subgroup G) : Subgroup G := hsM V ⊓ Subgroup.centralizer (V₂ : Set G)

section Transvection

variable {V V₂ : Subgroup G} (hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
  (hV2 : ∀ x ∈ V, x * x = 1) (hV₂V : V₂ ≤ V)
  (hidx : ∀ x ∈ V, ∀ y ∈ V, x ∉ V₂ → y ∉ V₂ → x * y ∈ V₂)

@[expose] noncomputable def transvFun (w : ↥V) (v : ↥V) : ↥V :=
  haveI := Classical.dec ((v : G) ∈ V₂)
  if (v : G) ∈ V₂ then v else v * w

include hV hV2 hidx in
theorem transvFun_mul {w : ↥V} (a b : ↥V) :
    transvFun (V₂ := V₂) w (a * b) = transvFun (V₂ := V₂) w a * transvFun (V₂ := V₂) w b := by
  classical
  have hcomm : ∀ x y : ↥V, x * y = y * x := fun x y =>
    Subtype.ext (hV x x.2 y y.2)
  have hww : w * w = 1 := Subtype.ext (hV2 w w.2)
  by_cases ha : (a : G) ∈ V₂ <;> by_cases hb : (b : G) ∈ V₂
  · have hab : ((a * b : ↥V) : G) ∈ V₂ := V₂.mul_mem ha hb
    simp only [transvFun, ha, hb, hab, ↓reduceIte]
  · have hab : ((a * b : ↥V) : G) ∉ V₂ := fun h => hb (by
      have := V₂.mul_mem (V₂.inv_mem ha) h
      rwa [Subgroup.coe_mul, ← mul_assoc, inv_mul_cancel, one_mul] at this)
    simp only [transvFun, ha, hb, hab, ↓reduceIte]
    exact mul_assoc a b w
  · have hab : ((a * b : ↥V) : G) ∉ V₂ := fun h => ha (by
      have := V₂.mul_mem h (V₂.inv_mem hb)
      rwa [Subgroup.coe_mul, mul_assoc, mul_inv_cancel, mul_one] at this)
    simp only [transvFun, ha, hb, hab, ↓reduceIte]
    show a * b * w = a * w * b
    rw [mul_assoc, hcomm b w, ← mul_assoc]
  · have hab : ((a * b : ↥V) : G) ∈ V₂ := hidx a a.2 b b.2 ha hb
    simp only [transvFun, ha, hb, hab, ↓reduceIte]
    show a * b = a * w * (b * w)
    calc a * b = a * b * (w * w) := by rw [hww, mul_one]
      _ = a * w * (b * w) := by rw [mul_assoc a w, ← mul_assoc w b w, hcomm w b]; group

include hV2 in
theorem transvFun_transvFun {w : ↥V} (hw : (w : G) ∈ V₂) (a : ↥V) :
    transvFun (V₂ := V₂) w (transvFun (V₂ := V₂) w a) = a := by
  classical
  have hww : w * w = 1 := Subtype.ext (hV2 w w.2)
  by_cases ha : (a : G) ∈ V₂
  · simp only [transvFun, ha, ↓reduceIte]
  · have haw : ((a * w : ↥V) : G) ∉ V₂ := fun h => ha (by
      have := V₂.mul_mem h (V₂.inv_mem hw)
      rwa [Subgroup.coe_mul, mul_assoc, mul_inv_cancel, mul_one] at this)
    simp only [transvFun, ha, haw, ↓reduceIte]
    show a * w * w = a
    rw [mul_assoc, hww, mul_one]

@[expose] noncomputable def transvection {w : ↥V} (hw : (w : G) ∈ V₂) : MulAut ↥V where
  toFun := transvFun (V₂ := V₂) w
  invFun := transvFun (V₂ := V₂) w
  left_inv a := transvFun_transvFun hV2 hw a
  right_inv a := transvFun_transvFun hV2 hw a
  map_mul' a b := transvFun_mul hV hV2 hidx a b

theorem transvection_apply_of_mem {w : ↥V} (hw : (w : G) ∈ V₂) {a : ↥V} (ha : (a : G) ∈ V₂) :
    transvection hV hV2 hidx hw a = a := by
  classical
  show transvFun (V₂ := V₂) w a = a
  simp only [transvFun, ha, ↓reduceIte]

theorem transvection_apply_of_not_mem {w : ↥V} (hw : (w : G) ∈ V₂) {a : ↥V}
    (ha : (a : G) ∉ V₂) : transvection hV hV2 hidx hw a = a * w := by
  classical
  show transvFun (V₂ := V₂) w a = a * w
  simp only [transvFun, ha, ↓reduceIte]

end Transvection

namespace HSSetting

variable {z : G} {V V₂ : Subgroup G}

theorem centralizer_V2_le_H (hz : z ∈ V₂) :
    Subgroup.centralizer (V₂ : Set G) ≤ hsH z := fun _ hg =>
  Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg z hz).symm

theorem not_le_ZQ [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V) (hc : Nat.card V₂ = 4) :
    ¬ V₂ ≤ hsZQ z := by
  intro hle
  have hle' : V₂ ≤ Subgroup.zpowers z := fun v hv => by
    rcases h.eq_one_or_z_of_mem_V_ZQ (hV₂ hv) (hle hv) with rfl | rfl
    · exact (Subgroup.zpowers _).one_mem
    · exact Subgroup.mem_zpowers _
  have := Subgroup.card_le_of_le hle'
  rw [hc, Nat.card_zpowers, h.orderOf_z] at this
  omega

theorem isPGroup_centralizer_V2 [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V)
    (hc : Nat.card V₂ = 4) (hz : z ∈ V₂) :
    IsPGroup 2 ↥(Subgroup.centralizer (V₂ : Set G)) := by
  set C := Subgroup.centralizer (V₂ : Set G) with hC
  have hCH := centralizer_V2_le_H hz
  have hdvd : Nat.card C ∣ 2 ^ 9 * 15 := by
    have := Subgroup.card_dvd_of_le hCH
    rw [h.card_H] at this
    norm_num at this ⊢
    exact this
  have hodd : ∀ p : ℕ, p.Prime → (p = 3 ∨ p = 5) → ¬ p ∣ Nat.card C := by
    intro p hp hp35 hpd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hpd
    have hyo : orderOf (y : G) = p := by rw [Subgroup.orderOf_coe]; exact hy
    have hyH : (y : G) ∈ hsH z := hCH y.2
    have hle : V₂ ≤ hsQ z ⊓ Subgroup.centralizer ({(y : G)} : Set G) := fun v hv =>
      ⟨h.two.le (hV₂ hv), Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp y.2 v hv)⟩
    rcases hp35 with rfl | rfl
    · rw [h.centralizer_Q_eq_ZQ_of_orderOf_three hyH hyo] at hle
      exact h.not_le_ZQ hV₂ hc hle
    · rw [h.centralizer_Q_eq_ZQ_of_five hyH hyo] at hle
      exact h.not_le_ZQ hV₂ hc hle
  have h3 : Nat.Coprime (Nat.card C) 3 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (hodd 3 Nat.prime_three (Or.inl rfl))))
  have h5 : Nat.Coprime (Nat.card C) 5 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr
      (hodd 5 (by norm_num) (Or.inr rfl))))
  have h15 : Nat.Coprime (Nat.card C) 15 := by
    rw [show (15 : ℕ) = 3 * 5 by norm_num]
    exact Nat.Coprime.mul_right h3 h5
  have h2 : Nat.card C ∣ 2 ^ 9 := h15.dvd_of_dvd_mul_right hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact IsPGroup.of_card hk

theorem card_centralizer_V2_le [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V)
    (hc : Nat.card V₂ = 4) (hz : z ∈ V₂) :
    Nat.card ↥(Subgroup.centralizer (V₂ : Set G)) ≤ 256 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (V₂ : Set G) with hC
  obtain ⟨k, hk⟩ := (h.isPGroup_centralizer_V2 hV₂ hc hz).exists_card_eq
  have hCH := centralizer_V2_le_H hz
  have hdvd : 2 ^ k ∣ 2 ^ 9 * 15 := by
    have := Subgroup.card_dvd_of_le hCH
    rw [h.card_H, hk] at this
    norm_num at this ⊢
    exact this
  have hk9 : k ≤ 9 := by
    have : 2 ^ k ∣ 2 ^ 9 :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 15)).dvd_of_dvd_mul_right hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
  rw [hk]
  by_contra hlt
  have hk9' : k = 9 := by
    have : 8 < k := by
      by_contra hle
      apply hlt
      calc 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 256 := by norm_num
    omega
  obtain ⟨T, hT⟩ := h.exists_isSylowTwoOf
  have hTc := h.card_T hT
  have hTH := h.isSylowTwoOf_H hT
  have hCS : IsPGroup 2 ↥(C.subgroupOf (hsH z)) :=
    (h.isPGroup_centralizer_V2 hV₂ hc hz).of_equiv (Subgroup.subgroupOfEquivOfLe hCH).symm
  have hCidx : ¬ 2 ∣ (C.subgroupOf (hsH z)).index := by
    have h1 := (C.subgroupOf (hsH z)).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv, hk, hk9', h.card_H] at h1
    have : (C.subgroupOf (hsH z)).index = 15 := by omega
    rw [this]
    decide
  have hTS : IsPGroup 2 ↥(T.subgroupOf (hsH z)) :=
    hTH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH.1).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(hsH z) (hCS.toSylow hCidx) (hTS.toSylow hTH.2.2)
  have hconj : ∀ v ∈ V₂, (g : G) * v * (g : G)⁻¹ ∈ T ∧
      (g : G) * v * (g : G)⁻¹ ∈ Subgroup.centralizer (T : Set G) := by
    intro v hv
    have hvH : v ∈ hsH z := hCH (Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (h.comm_of_mem_V (hV₂ hw) (hV₂ hv)))
    have hvC : (⟨v, hvH⟩ : ↥(hsH z)) ∈ hCS.toSylow hCidx :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_iff.mpr fun w hw =>
        h.comm_of_mem_V (hV₂ hw) (hV₂ hv))
    have hmem : g * ⟨v, hvH⟩ * g⁻¹ ∈ (g • hCS.toSylow hCidx : Sylow 2 ↥(hsH z)) := by
      rw [mem_smul_sylow', show g⁻¹ * (g * ⟨v, hvH⟩ * g⁻¹) * g = ⟨v, hvH⟩ by group]
      exact hvC
    rw [hg] at hmem
    refine ⟨hmem, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have htH : t ∈ hsH z := hTH.1 ht
    have htmem : (⟨t, htH⟩ : ↥(hsH z)) ∈ (g • hCS.toSylow hCidx : Sylow 2 ↥(hsH z)) := by
      rw [hg]
      exact ht
    rw [mem_smul_sylow'] at htmem
    have hc' : ((g⁻¹ * ⟨t, htH⟩ * g : ↥(hsH z)) : G) ∈ C := htmem
    have hcv := Subgroup.mem_centralizer_iff.mp hc' v hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcv
    calc t * ((g : G) * v * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * t * (g : G)) * v) * (g : G)⁻¹ := by group
      _ = (g : G) * (v * ((g : G)⁻¹ * t * (g : G))) * (g : G)⁻¹ := by rw [hcv]
      _ = (g : G) * v * (g : G)⁻¹ * t := by group
  have hle : V₂ ≤ Subgroup.zpowers z := by
    intro v hv
    obtain ⟨hvT, hvc⟩ := hconj v hv
    have hv2 : (g : G) * v * (g : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) = 1 := by
      rw [show (g : G) * v * (g : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) =
        (g : G) * (v * v) * (g : G)⁻¹ by group, h.mul_self_of_mem_V (hV₂ hv), mul_one,
        mul_inv_cancel]
    by_cases hv1 : v = 1
    · rw [hv1]
      exact (Subgroup.zpowers z).one_mem
    · have hne : (g : G) * v * (g : G)⁻¹ ≠ 1 := fun h1 => hv1 (by
        calc v = (g : G)⁻¹ * ((g : G) * v * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h1]; group)
      have hz' := h.eq_z_of_mem_center_T hT hvT hvc hv2 hne
      have hgz : (g : G) * z * (g : G)⁻¹ = z := by
        have := Subgroup.mem_centralizer_singleton_iff.mp g.2
        rw [this, mul_inv_cancel_right]
      have : v = z := by
        have e : (g : G) * v * (g : G)⁻¹ = (g : G) * z * (g : G)⁻¹ := by rw [hz', hgz]
        exact mul_left_cancel (mul_right_cancel e)
      rw [this]
      exact Subgroup.mem_zpowers z
  have := Subgroup.card_le_of_le hle
  rw [hc, Nat.card_zpowers, h.orderOf_z] at this
  omega

theorem mul_mem_V2 [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V) (hc : Nat.card V₂ = 4) :
    ∀ x ∈ V, ∀ y ∈ V, x ∉ V₂ → y ∉ V₂ → x * y ∈ V₂ := by
  have hidx : (V₂.subgroupOf V).index = 2 := by
    have h1 := (V₂.subgroupOf V).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂).toEquiv, hc, h.card_V] at h1
    omega
  intro x hx y hy hxn hyn
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    ⟨fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hxn,
      fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hyn⟩
  exact Subgroup.mem_subgroupOf.mp this

theorem index_V2 [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V) (hc : Nat.card V₂ = 4) :
    (V₂.subgroupOf V).index = 2 := by
  have h1 := (V₂.subgroupOf V).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₂).toEquiv, hc, h.card_V] at h1
  omega

theorem exists_mem_V_not_mem_V2 [Finite G] (h : HSSetting z V) (hc : Nat.card V₂ = 4) :
    ∃ v ∈ V, v ∉ V₂ := by
  by_contra hne
  push Not at hne
  have := Subgroup.card_le_of_le (fun v hv => hne v hv : V ≤ V₂)
  rw [hc, h.card_V] at this
  omega

theorem card_R2 [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V) (hc : Nat.card V₂ = 4) :
    Nat.card ↥(hsR2 V V₂) = 256 := by
  have hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => h.comm_of_mem_V hx hy
  have hV2 : ∀ x ∈ V, x * x = 1 := fun x hx => h.mul_self_of_mem_V hx
  have hidx := h.mul_mem_V2 hV₂ hc
  have hR₂N : hsR2 V V₂ ≤ Subgroup.normalizer (V : Set G) := inf_le_left
  have hrel := Subgroup.relIndex_mul_card (hsR2 V V₂ ⊓ Subgroup.centralizer (V : Set G))
    (hsR2 V V₂)
  rw [← card_autOn_eq_relIndex hR₂N, inf_right_comm, inf_idem] at hrel
  have hker : hsR2 V V₂ ⊓ Subgroup.centralizer (V : Set G) = hsP V := by
    rw [← h.centralizer_V_eq]
    refine le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) (fun x hx => ⟨⟨hx.1, ?_⟩, hx.2⟩)
    exact Subgroup.centralizer_le hV₂ hx.2
  rw [hker, h.card_P] at hrel
  have hle4 : Nat.card (autOn (hsR2 V V₂) V) ≤ 4 :=
    hc ▸ card_autOn_le_of_centralizes hR₂N inf_le_right (h.index_V2 hV₂ hc)
  obtain ⟨v₀, hv₀V, hv₀⟩ := h.exists_mem_V_not_mem_V2 hc
  have hge4 : 4 ≤ Nat.card (autOn (hsR2 V V₂) V) := by
    have hmem : ∀ w : ↥V₂, transvection hV hV2 hidx (w := ⟨w, hV₂ w.2⟩) w.2 ∈
        autOn (hsR2 V V₂) V := by
      intro w
      have htop : transvection hV hV2 hidx (w := ⟨w, hV₂ w.2⟩) w.2 ∈ autOn (hsM V) V := by
        rw [h.autOn_M_eq_top]
        exact Subgroup.mem_top _
      obtain ⟨m, hm⟩ := (mem_autOn_iff (le_refl _)).mp htop
      have hmC : (m : G) ∈ Subgroup.centralizer (V₂ : Set G) := by
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have e := congrArg (fun α : MulAut ↥V => ((α ⟨v, hV₂ hv⟩ : ↥V) : G)) hm
        rw [actionOn_apply_coe, transvection_apply_of_mem hV hV2 hidx _ hv] at e
        calc v * (m : G) = (m : G) * v * (m : G)⁻¹ * (m : G) := by rw [e]
          _ = (m : G) * v := by group
      refine (mem_autOn_iff hR₂N).mpr ⟨⟨m, m.2, hmC⟩, ?_⟩
      rw [← hm]
      ext v
      rfl
    let f : ↥V₂ → ↥(autOn (hsR2 V V₂) V) := fun w => ⟨_, hmem w⟩
    have hf : Function.Injective f := by
      intro w w' e
      have e' := congrArg (fun α : ↥(autOn (hsR2 V V₂) V) => (((α : MulAut ↥V) ⟨v₀, hv₀V⟩ :
        ↥V) : G)) e
      simp only [f] at e'
      rw [transvection_apply_of_not_mem hV hV2 hidx _ hv₀,
        transvection_apply_of_not_mem hV hV2 hidx _ hv₀] at e'
      simp only [Subgroup.coe_mul] at e'
      exact Subtype.ext (mul_left_cancel e')
    have := Nat.card_le_card_of_injective f hf
    rwa [hc] at this
  have h4 : Nat.card (autOn (hsR2 V V₂) V) = 4 := le_antisymm hle4 hge4
  rw [h4] at hrel
  omega

theorem centralizer_V2_eq [Finite G] (h : HSSetting z V) (hV₂ : V₂ ≤ V)
    (hc : Nat.card V₂ = 4) (hz : z ∈ V₂) :
    Subgroup.centralizer (V₂ : Set G) = hsR2 V V₂ :=
  (Subgroup.eq_of_le_of_card_ge (inf_le_right : hsR2 V V₂ ≤ _) (by
    rw [h.card_R2 hV₂ hc]
    exact h.card_centralizer_V2_le hV₂ hc hz)).symm

end HSSetting

end CFSG.Quasithin.HSType
