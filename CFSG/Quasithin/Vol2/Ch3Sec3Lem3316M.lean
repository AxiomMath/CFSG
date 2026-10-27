module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316J

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise

namespace L3316

variable {G : Type} [Group G] [Finite G]

theorem j1_step {T M L D : Subgroup G} (h : Hyp331 G T M L D) (hJ1 : FactJ1Norm3312)
    {Y Kc : Subgroup G} (hY : Y ∈ lFamilyOf L T) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hO : pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥) (hKc : Kc ∈ cComp (Y ⊔ T ⊔ D)) (hYK : Y ≤ Kc)
    (hHK : Y ⊔ T ⊔ D ≤ Subgroup.normalizer (Kc : Set G))
    (hc : A312C15 (modO2Image (Y ⊔ T ⊔ D) Y) (modO2Image (Y ⊔ T ⊔ D) Kc))
    {x : G} (hx3 : orderOf x = 3) (hxL : x ∈ L) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hxy : ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 Y) :
    Kc ≤ Subgroup.normalizer ((⁅T, Subgroup.zpowers x⁆ : Subgroup G) : Set G) ∧
      ⁅T, Subgroup.zpowers x⁆ ≤ T ∧ ⁅T, Subgroup.zpowers x⁆ ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₁ := Y ⊔ T ⊔ D with hH₁
  have hYH : Y ≤ H₁ := le_sup_left.trans le_sup_left
  have hTH : T ≤ H₁ := le_sup_right.trans le_sup_left
  have hDH : D ≤ H₁ := le_sup_right
  set X := Subgroup.zpowers x with hXdef
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3, pow_one])
  have hXT : X ≤ Subgroup.normalizer (T : Set G) := (Subgroup.zpowers_le).mpr hxT
  have hxH : x ∈ H₁ := by
    have : x ∈ T ⊔ D := by rw [← h.ND]; exact hxT
    exact (sup_le hTH hDH) this
  have hXH : X ≤ H₁ := (Subgroup.zpowers_le).mpr hxH
  obtain ⟨⟨eY⟩, ⟨eK⟩⟩ := hc
  have hKH : Kc ≤ H₁ := le_of_mem_cComp hKc
  have hKn : (modO2Image H₁ Kc).Normal := L3312.modO2Image_normal hKH hHK
  let πY : ↥Y →* ↥(modO2Image H₁ Y) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H₁)).comp (Subgroup.inclusion hYH)).codRestrict _
      (fun y => ⟨⟨y, hYH y.2⟩, y.2, rfl⟩)
  have hπY : Function.Surjective πY := by
    rintro ⟨_, ⟨⟨y, hyH⟩, hy, rfl⟩⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hOYH : ∀ o ∈ pCoreOf 2 Y, ∀ hoH : o ∈ H₁, (⟨o, hoH⟩ : ↥H₁) ∈ CFSG.pCore 2 ↥H₁ := by
    intro o ho hoH
    set f : ↥Y →* alternatingGroup (Fin 5) := eY.toMonoidHom.comp πY with hfdef
    have hfs : Function.Surjective f := eY.surjective.comp hπY
    have hW : (CFSG.pCore 2 ↥Y).map f = ⊥ := by
      have : ((CFSG.pCore 2 ↥Y).map f).Normal := (CFSG.pCore_normal (p := 2) (G := ↥Y)).map f hfs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Y).map f) with h1 | h1
      · exact h1
      · exfalso
        have h2 := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map f
        rw [h1] at h2
        obtain ⟨k, hk⟩ := (h2.of_equiv Subgroup.topEquiv).exists_card_eq
        rw [card_alt 5 (by norm_num)] at hk
        have h3 : 3 ∣ 2 ^ k := by rw [← hk]; decide
        have := Nat.prime_three.dvd_of_dvd_pow h3
        norm_num at this
    rw [pCoreOf] at ho
    obtain ⟨o', ho', rfl⟩ := ho
    have h1 : f o' ∈ (CFSG.pCore 2 ↥Y).map f := ⟨o', ho', rfl⟩
    rw [hW, Subgroup.mem_bot] at h1
    have h2 : πY o' = 1 := eY.injective (by rw [map_one]; exact h1)
    have h3 : (QuotientGroup.mk (⟨o', hoH⟩ : ↥H₁) : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = 1 :=
      congrArg Subtype.val h2
    exact (QuotientGroup.eq_one_iff _).mp h3
  let ψ : (↥H₁ ⧸ CFSG.pCore 2 ↥H₁) →* MulAut ↥(modO2Image H₁ Kc) := MulAut.conjNormal
  have hInn : (MulAut.conj : ↥(modO2Image H₁ Kc) →* MulAut ↥(modO2Image H₁ Kc)).range ≤
      ψ.range := by
    rintro _ ⟨n, rfl⟩
    exact ⟨_, MulAut.conjNormal_val⟩
  have H3 : L3312.Hyp3312 G T M L D Y := ⟨h, hY, hO⟩
  have hS := L3312.isSylowTwoOf_map_range ψ H3.isSylowTwoOf_modO2Image_T
  have hYK' : modO2Image H₁ Y ≤ modO2Image H₁ Kc := Subgroup.map_mono fun y hy => hYK hy
  have hSB : (modO2Image H₁ T).map ψ ≤ MulAction.stabilizer (MulAut ↥(modO2Image H₁ Kc))
      ((modO2Image H₁ Y).subgroupOf (modO2Image H₁ Kc)) := by
    rintro _ ⟨tb, htb, rfl⟩
    obtain ⟨⟨t, htX⟩, ht, rfl⟩ := htb
    refine (L3312.conjNormal_mem_stabilizer_iff hYK' _).mpr ?_
    exact L3312.mk_mem_normalizer_modO2Image htX (hTY ht)
  have hB5 : IsAlt 5 ↥((modO2Image H₁ Y).subgroupOf (modO2Image H₁ Kc)) :=
    ⟨(Subgroup.subgroupOfEquivOfLe hYK').trans eY⟩
  have hJ := (hJ1 _ ⟨eK⟩ ψ.range _ _ hInn hS hB5 hSB).2
  set xb : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁ := QuotientGroup.mk ⟨x, hxH⟩ with hxbdef
  have hψx : ψ xb = 1 := by
    refine hJ (ψ xb) ⟨xb, rfl⟩ ?_ ?_
    · have hxb3 : orderOf xb ∣ 3 := by
        have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥H₁)) (⟨x, hxH⟩ : ↥H₁)
        rw [Subgroup.orderOf_mk, hx3] at this
        exact this
      have h1 : orderOf (ψ xb) ∣ 3 := (orderOf_map_dvd ψ xb).trans hxb3
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h <;> rw [h] <;> decide
    · rintro ⟨b, hbK⟩ hb
      obtain ⟨⟨y, hyH⟩, hy, hyb⟩ := hb
      have hyb' : (QuotientGroup.mk ⟨y, hyH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = b := hyb
      apply Subtype.ext
      show xb * b * xb⁻¹ = b
      rw [← hyb']
      have hc := hOYH _ (hxy y hy)
        (H₁.mul_mem (H₁.mul_mem (H₁.mul_mem hxH hyH) (H₁.inv_mem hxH)) (H₁.inv_mem hyH))
      have h2 : (QuotientGroup.mk (⟨x, hxH⟩ * ⟨y, hyH⟩ * (⟨x, hxH⟩ : ↥H₁)⁻¹ *
          (⟨y, hyH⟩ : ↥H₁)⁻¹) : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) = 1 := (QuotientGroup.eq_one_iff _).mpr hc
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, mul_inv_eq_one] at h2
      exact h2
  have hxK : ∀ k ∈ Kc, ∀ hkH : k ∈ H₁,
      xb * QuotientGroup.mk ⟨k, hkH⟩ = QuotientGroup.mk ⟨k, hkH⟩ * xb := by
    intro k hk hkH
    have h1 := congrArg (fun φ : MulAut ↥(modO2Image H₁ Kc) =>
      ((φ ⟨QuotientGroup.mk ⟨k, hkH⟩, ⟨⟨k, hkH⟩, hk, rfl⟩⟩ : ↥(modO2Image H₁ Kc)) :
        ↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) hψx
    simp only [MulAut.one_apply] at h1
    change xb * QuotientGroup.mk ⟨k, hkH⟩ * xb⁻¹ = QuotientGroup.mk ⟨k, hkH⟩ at h1
    calc xb * QuotientGroup.mk ⟨k, hkH⟩ =
          (xb * QuotientGroup.mk ⟨k, hkH⟩ * xb⁻¹) * xb := by group
      _ = QuotientGroup.mk ⟨k, hkH⟩ * xb := by rw [h1]
  set Cb := Subgroup.centralizer ((modO2Image H₁ Kc : Subgroup (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) :
    Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) with hCb
  have hxC : xb ∈ Cb := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨k, hkH⟩, hk, rfl⟩
    exact (hxK k hk hkH).symm
  have hCn : Cb.Normal := Subgroup.normal_centralizer
  set Wb := modO2Image H₁ T ⊓ Cb with hWb
  have hCbN : ∀ g, g ∈ Subgroup.normalizer (Cb : Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁)) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hCn]
    exact Subgroup.mem_top g
  set Nmap : Subgroup G := ((Subgroup.normalizer (Wb : Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H₁))).map H₁.subtype with hNmap
  have hYN : Y ≤ Nmap := by
    intro y hy
    refine ⟨⟨y, hYH hy⟩, ?_, rfl⟩
    show (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) ∈
      Subgroup.normalizer (Wb : Set (↥H₁ ⧸ CFSG.pCore 2 ↥H₁))
    have hyK : (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) ∈ modO2Image H₁ Kc :=
      ⟨⟨y, hYH hy⟩, hYK hy, rfl⟩
    apply mem_normalizer_of_map_le
    rintro _ ⟨w, hw, rfl⟩
    have hc : (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * w =
        w * QuotientGroup.mk ⟨y, hYH hy⟩ := Subgroup.mem_centralizer_iff.mp hw.2 _ hyK
    show (QuotientGroup.mk ⟨y, hYH hy⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * w *
      (QuotientGroup.mk ⟨y, hYH hy⟩)⁻¹ ∈ Wb
    rw [hc, mul_inv_cancel_right]
    exact hw
  have hTDN : ∀ g ∈ T ⊔ D, g ∈ Nmap := by
    have key : ∀ g, ∀ hg : g ∈ H₁, g ∈ Subgroup.normalizer (T : Set G) →
        g ∈ Nmap := by
      intro g hg hgT
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      exact L3316.mem_normalizer_inf (L3312.mk_mem_normalizer_modO2Image hg hgT) (hCbN _)
    intro g hg
    have hgH : g ∈ H₁ := (sup_le hTH hDH) hg
    have hgN : g ∈ Subgroup.normalizer (T : Set G) := by rw [h.ND]; exact hg
    exact key g hgH hgN
  have hHN : H₁ ≤ Nmap := sup_le (sup_le hYN (fun t ht => hTDN t (Subgroup.mem_sup_left ht)))
    (fun d hd => hTDN d (Subgroup.mem_sup_right hd))
  have hWn : Wb.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    intro hb _
    obtain ⟨hh, rfl⟩ := QuotientGroup.mk_surjective hb
    obtain ⟨hh', hh'N, hh'e⟩ := hHN hh.2
    have : hh' = hh := Subtype.ext hh'e
    rw [← this]
    exact hh'N
  have hW2 : IsPGroup 2 ↥Wb := by
    have hT2 : IsPGroup 2 ↥(modO2Image H₁ T) :=
      (h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm).map _
    exact hT2.to_le inf_le_left
  have hWbot : Wb = ⊥ := by
    have h1 : Wb ≤ CFSG.pCore 2 (↥H₁ ⧸ CFSG.pCore 2 ↥H₁) := le_sSup ⟨hWn, hW2⟩
    rwa [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, le_bot_iff] at h1
  have hxTc : ∀ t ∈ T, ∀ htH : t ∈ H₁,
      (QuotientGroup.mk ⟨t, htH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * xb =
        xb * QuotientGroup.mk ⟨t, htH⟩ := by
    intro t ht htH
    set tb : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁ := QuotientGroup.mk ⟨t, htH⟩
    have hcT' : tb * xb * tb⁻¹ * xb⁻¹ ∈ modO2Image H₁ T := by
      have hm : t * x * t⁻¹ * x⁻¹ ∈ T := by
        have := (Subgroup.mem_normalizer_iff.mp hxT t⁻¹).mp (T.inv_mem ht)
        have h2 := T.mul_mem ht this
        simpa [mul_assoc] using h2
      refine ⟨⟨t * x * t⁻¹ * x⁻¹, H₁.mul_mem (H₁.mul_mem (H₁.mul_mem htH hxH) (H₁.inv_mem htH))
        (H₁.inv_mem hxH)⟩, hm, ?_⟩
      rfl
    have hcC : tb * xb * tb⁻¹ * xb⁻¹ ∈ Cb :=
      Cb.mul_mem (hCn.conj_mem _ hxC tb) (Cb.inv_mem hxC)
    have h1 : tb * xb * tb⁻¹ * xb⁻¹ ∈ Wb := ⟨hcT', hcC⟩
    rw [hWbot, Subgroup.mem_bot] at h1
    have h2 : tb * xb * tb⁻¹ = xb := mul_inv_eq_one.mp h1
    calc tb * xb = (tb * xb * tb⁻¹) * tb := by group
      _ = xb * tb := by rw [h2]
  set R₁ := pCoreOf 2 H₁ with hR₁def
  have hT2 : IsPGroup 2 ↥T := h.sylow.1
  have hTsH : IsSylowTwoOf T H₁ :=
    ⟨hTH, hT2, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  have hR₁T : R₁ ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsH
  have hR₁2 : IsPGroup 2 ↥R₁ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H₁
  have hHR : H₁ ≤ Subgroup.normalizer (R₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H₁
  have hpow : ∀ g ∈ H₁, ∀ hgH : g ∈ H₁,
      (QuotientGroup.mk ⟨g, hgH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) * xb = xb * QuotientGroup.mk ⟨g, hgH⟩ →
      ∀ x' ∈ X, g * x' * g⁻¹ * x'⁻¹ ∈ R₁ := by
    intro g _ hgH hgx x' hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
    have hxk : x ^ k ∈ H₁ := H₁.zpow_mem hxH k
    have hc : Commute (QuotientGroup.mk ⟨g, hgH⟩ : ↥H₁ ⧸ CFSG.pCore 2 ↥H₁) (xb ^ k) :=
      (Commute.zpow_right hgx k)
    have hmem : (⟨g, hgH⟩ * ⟨x, hxH⟩ ^ k * (⟨g, hgH⟩ : ↥H₁)⁻¹ * ((⟨x, hxH⟩ : ↥H₁) ^ k)⁻¹ :
        ↥H₁) ∈ CFSG.pCore 2 ↥H₁ := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, QuotientGroup.mk_zpow,
        hc.eq, mul_inv_cancel_right, mul_inv_cancel]
    rw [hR₁def, pCoreOf]
    exact ⟨_, hmem, by simp⟩
  have hTXR : ⁅T, X⁆ ≤ R₁ := by
    rw [Subgroup.commutator_le]
    intro t ht x' hx'
    rw [commutatorElement_def]
    exact hpow t (hTH ht) (hTH ht) (hxTc t ht (hTH ht)) x' hx'
  have hQR : ⁅R₁, X⁆ = ⁅T, X⁆ := commutator_eq_of_le hT2 hX3 hXT hR₁T hTXR
  have hnormPX : ∀ P : Subgroup G, ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) →
      g * x * g⁻¹ * x⁻¹ ∈ P → g ∈ Subgroup.normalizer ((P ⊔ X : Subgroup G) : Set G) := by
    intro P g hgP hgx
    apply mem_normalizer_of_map_le
    have hPg : P.map (MulAut.conj g).toMonoidHom = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgP
    rw [Subgroup.map_sup, hPg, hXdef, MonoidHom.map_zpowers]
    refine sup_le le_sup_left ((Subgroup.zpowers_le).mpr ?_)
    have h1 : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
    show g * x * g⁻¹ ∈ P ⊔ X
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hgx)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hKQ : Kc ≤ Subgroup.normalizer ((⁅T, X⁆ : Subgroup G) : Set G) := by
    intro k hk
    have hkH := hKH hk
    have hkx : k * x * k⁻¹ * x⁻¹ ∈ R₁ :=
      hpow k hkH hkH (hxK k hk hkH).symm x (Subgroup.mem_zpowers x)
    rw [← hQR]
    exact mem_normalizer_commutator hR₁2 hX3 (hXH.trans hHR) (hHR hkH)
      (hnormPX R₁ k (hHR hkH) hkx)
  have hQ2 : IsPGroup 2 ↥(⁅T, X⁆ : Subgroup G) := by
    refine hT2.to_le ?_
    rw [Subgroup.commutator_le]
    intro t ht x' hx'
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.mp (hXT hx') t⁻¹).mp (T.inv_mem ht)
    have h2 := T.mul_mem ht this
    simpa [mul_assoc] using h2
  have hQ1 : (⁅T, X⁆ : Subgroup G) ≠ ⊥ := by
    intro hQ
    have hcen := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQ
    have hxC' : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
      refine ⟨Subgroup.mem_sup_left hxL, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hrT : r ∈ T := (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf) hr
      exact (Subgroup.mem_centralizer_iff.mp (hcen hrT) x (Subgroup.mem_zpowers x)).symm
    have hx2 := h.toSetup331.charTwo hxC'
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨x, hx2⟩
    have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hx3] at h1
    have := Nat.prime_three.dvd_of_dvd_pow h1
    norm_num at this
  have hQ2 : ⁅T, X⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro t ht x' hx'
    rw [commutatorElement_def]
    have := (Subgroup.mem_normalizer_iff.mp (hXT hx') t⁻¹).mp (T.inv_mem ht)
    have h2 := T.mul_mem ht this
    simpa [mul_assoc] using h2
  refine ⟨hKQ, hQ2, fun hQ => ?_⟩
  have hcen := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hQ
  have hxC' : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
    refine ⟨Subgroup.mem_sup_left hxL, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hrT : r ∈ T := (EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf) hr
    exact (Subgroup.mem_centralizer_iff.mp (hcen hrT) x (Subgroup.mem_zpowers x)).symm
  have hx2 := h.toSetup331.charTwo hxC'
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)) ⟨x, hx2⟩
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
  rw [hx3] at h1
  have := Nat.prime_three.dvd_of_dvd_pow h1
  norm_num at this

theorem eq_of_two_pow_modEq_nineteen {m c : ℕ} (hcm : c ≤ m) (hm : m ≤ 17)
    (h : 2 ^ m ≡ 2 ^ c [MOD 19]) : c = m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hcm
  have h1 : 2 ^ c * 2 ^ d ≡ 2 ^ c * 1 [MOD 19] := by rwa [← pow_add, mul_one]
  have h2 : 2 ^ d ≡ 1 [MOD 19] :=
    Nat.ModEq.cancel_left_of_coprime (Nat.Coprime.pow_right c (by norm_num : Nat.Coprime 19 2)) h1
  have hd : d ≤ 17 := by omega
  interval_cases d <;> simp_all [Nat.ModEq]

theorem mem_centralizer_of_card_le {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hcard : Nat.card ↥Q ≤ 2 ^ 17) {k : G} (hk : k ∈ Subgroup.normalizer (Q : Set G))
    (hk19 : orderOf k = 19) : k ∈ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  set kn : ↥(Subgroup.normalizer (Q : Set G)) := ⟨k, hk⟩ with hkn
  set P : Subgroup ↥(Subgroup.normalizer (Q : Set G)) := Subgroup.zpowers kn with hP
  have hkn19 : orderOf kn = 19 := by rw [hkn, Subgroup.orderOf_mk, hk19]
  have hP19 : IsPGroup 19 ↥P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hkn19, pow_one])
  have hmod := hP19.card_modEq_card_fixedPoints ↥Q
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  have hC : Nat.card (MulAction.fixedPoints ↥P ↥Q) = Nat.card ↥(FixedPoints.subgroup ↥P ↥Q) := rfl
  obtain ⟨c, hc, hcC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hm ▸ Subgroup.card_subgroup_dvd_card (FixedPoints.subgroup ↥P ↥Q))
  rw [hC, hcC, hm] at hmod
  have hm17 : m ≤ 17 := by
    rw [hm] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
  have hcm := eq_of_two_pow_modEq_nineteen hc hm17 hmod
  have htop : FixedPoints.subgroup ↥P ↥Q = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hcC, hm, hcm])
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have h1 : (⟨q, hq⟩ : ↥Q) ∈ FixedPoints.subgroup ↥P ↥Q := htop ▸ Subgroup.mem_top _
  have h2 := (FixedPoints.mem_subgroup ↥P ↥Q _).mp h1 ⟨kn, Subgroup.mem_zpowers kn⟩
  have h3 : k * q * k⁻¹ = q := congrArg Subtype.val h2
  calc q * k = (k * q * k⁻¹) * k := by rw [h3]
    _ = k * q := by group

theorem le_centralizer_of_card_le {H Kc : Subgroup G}
    (hKc : Kc ∈ cComp H) (hHK : H ≤ Subgroup.normalizer (Kc : Set G))
    (hJ : IsSporadic .J1 ↥(modO2Image H Kc)) {Q : Subgroup G} (hQ : IsPGroup 2 ↥Q)
    (hcard : Nat.card ↥Q ≤ 2 ^ 17) (hKQ : Kc ≤ Subgroup.normalizer (Q : Set G)) :
    Kc ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  obtain ⟨eK⟩ := hJ
  have hKH : Kc ≤ H := le_of_mem_cComp hKc
  have hKn : (modO2Image H Kc).Normal := L3312.modO2Image_normal hKH hHK
  have hJs : IsSimpleGroup ↥(modO2Image H Kc) := by
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .J1) :=
      CFSG.Sporadic.J1.isSimpleGroup_J1
    have hnt : Nontrivial ↥(modO2Image H Kc) := by
      rw [← Finite.one_lt_card_iff_nontrivial, Nat.card_congr eK.toEquiv]
      rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) = 175560 from
        CFSG.Sporadic.J1.card_J1]
      norm_num
    exact IsSimpleGroup.isSimpleGroup_of_surjective eK.symm.toMonoidHom eK.symm.surjective
  let πK : ↥Kc →* ↥(modO2Image H Kc) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hKH)).codRestrict _
      (fun k => ⟨⟨k, hKH k.2⟩, k.2, rfl⟩)
  have hπK : Function.Surjective πK := by
    rintro ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker2 : ∀ k : ↥Kc, πK k = 1 → ∃ j : ℕ, k ^ 2 ^ j = 1 := by
    intro k hk
    have h1 : (QuotientGroup.mk (⟨k, hKH k.2⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1 :=
      congrArg Subtype.val hk
    obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
      ⟨_, (QuotientGroup.eq_one_iff _).mp h1⟩
    refine ⟨j, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) hj
    simpa using this
  have h19 : 19 ∣ Nat.card ↥Kc := by
    have h1 : Nat.card ↥(modO2Image H Kc) ∣ Nat.card ↥Kc := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective πK hπK).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    rw [Nat.card_congr eK.toEquiv, show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J1) =
      175560 from CFSG.Sporadic.J1.card_J1] at h1
    exact (by norm_num : 19 ∣ 175560).trans h1
  have : Fintype ↥Kc := Fintype.ofFinite _
  obtain ⟨k, hk19⟩ := exists_prime_orderOf_dvd_card (G := ↥Kc) 19
    (by rw [← Nat.card_eq_fintype_card]; exact h19)
  have hkC : (k : G) ∈ Subgroup.centralizer (Q : Set G) :=
    mem_centralizer_of_card_le hQ hcard (hKQ k.2) (by rw [Subgroup.orderOf_coe, hk19])
  set C : Subgroup ↥Kc := (Subgroup.centralizer (Q : Set G)).subgroupOf Kc with hCdef
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hc ⊢
    intro q hq
    have hgQ := hKQ g.2
    have hq' : (g : G)⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hgQ) q).mp hq
      simpa using this
    have h1 := hc _ hq'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc q * ((g : G) * c * (g : G)⁻¹) = (g : G) * (((g : G)⁻¹ * q * g) * c) * (g : G)⁻¹ := by
          group
      _ = (g : G) * (c * ((g : G)⁻¹ * q * g)) * (g : G)⁻¹ := by rw [h1]
      _ = (g : G) * c * (g : G)⁻¹ * q := by group
  have hCtop : C.map πK = ⊤ := by
    have : (C.map πK).Normal := hCn.map πK hπK
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map πK) with h1 | h1
    · exfalso
      have h2 : πK k ∈ C.map πK := ⟨k, hkC, rfl⟩
      rw [h1, Subgroup.mem_bot] at h2
      obtain ⟨j, hj⟩ := hker2 k h2
      have h3 : orderOf k ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj
      rw [hk19] at h3
      have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        ((by norm_num : Nat.Prime 19).dvd_of_dvd_pow h3)
      norm_num at this
    · exact h1
  have hq2 : IsPGroup 2 (↥Kc ⧸ C) := by
    intro z
    obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : πK k' ∈ C.map πK := hCtop ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hck⟩ := h1
    obtain ⟨j, hj⟩ := hker2 (c⁻¹ * k') (by rw [map_mul, map_inv, hck, inv_mul_cancel])
    refine ⟨j, ?_⟩
    have h2 : (QuotientGroup.mk k' : ↥Kc ⧸ C) = QuotientGroup.mk (c⁻¹ * k') := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff c).mpr hc,
        inv_one, one_mul]
    rw [h2, ← QuotientGroup.mk_pow, hj, QuotientGroup.mk_one]
  have hKp : Group.IsPerfect ↥Kc := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hKc)
  have hQp : Group.IsPerfect (↥Kc ⧸ C) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective C)
  have hsub : Subsingleton (↥Kc ⧸ C) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isNilpotent (↥Kc ⧸ C) hq2.isNilpotent
  intro k' hk'
  have h1 : (QuotientGroup.mk (⟨k', hk'⟩ : ↥Kc) : ↥Kc ⧸ C) = 1 := Subsingleton.elim _ _
  have h2 : (⟨k', hk'⟩ : ↥Kc) ∈ C := (QuotientGroup.eq_one_iff (N := C) _).mp h1
  exact h2

end L3316

end CFSG.Quasithin.H13
