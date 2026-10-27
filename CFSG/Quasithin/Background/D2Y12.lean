module

public import CFSG.Quasithin.Background.D2Y11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {V : Type*} [CommGroup V] [Finite V]

section End

variable {X : Subgroup (MulAut V)}

theorem fixV_z_le_fixV_x (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X)
    (hX1 : ∀ Y ∈ Xk X 1, False) {t x z : MulAut V} (h : InvPair X t x) (hg : Good X t x z) :
    fixV (Subgroup.zpowers z) ≤ fixV (Subgroup.zpowers x) := by
  obtain ⟨hxo, hzo, hxz, hne, hsup⟩ := Good.E9 hV c hX1 h hg
  have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  obtain ⟨-, hinf, -, -⟩ := commV_card_three hV hzc
  intro w hw g hg'
  have hxP : x ∈ centR X x := mem_centR.mpr ⟨h.hx, rfl⟩
  have hgP : g ∈ centR X x := (Subgroup.zpowers_le.mpr hxP) hg'
  have h1 : g w * w⁻¹ ∈ commV (centR X x) := Subgroup.subset_closure ⟨g, hgP, w, rfl⟩
  rw [hg.hU] at h1
  have h2 : g w ∈ fixV (Subgroup.zpowers z) := by
    refine fixV_smul_mem (fun p hp => ?_) hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hcomm : Commute g z := hg.comm g hgP z hg.hz
    have e : g⁻¹ * z ^ m * g = z ^ m := by
      have := (hcomm.zpow_right m).eq
      rw [mul_assoc, ← this, inv_mul_cancel_left]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) m
  have h3 : g w * w⁻¹ ∈ fixV (Subgroup.zpowers z) :=
    (fixV (Subgroup.zpowers z)).mul_mem h2 ((fixV (Subgroup.zpowers z)).inv_mem hw)
  have h4 : g w * w⁻¹ ∈ commV (Subgroup.zpowers z) ⊓ fixV (Subgroup.zpowers z) := ⟨h1, h3⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h4
  exact h4

omit [Finite V] in
theorem mul_mem_kerMod {t₁ t₂ z : MulAut V}
    (hZ : ∀ h ∈ X, h * z * h⁻¹ ∈ Subgroup.zpowers z) (h1 : t₁ ∈ X) (h2 : t₂ ∈ X)
    (hc1 : t₁ * z = z * t₁) (hc2 : t₂ * z = z * t₂)
    (hr1 : ∀ r ∈ pCoreOf 3 X, t₁ * r * t₁⁻¹ * r ∈ Subgroup.zpowers z)
    (hr2 : ∀ r ∈ pCoreOf 3 X, t₂ * r * t₂⁻¹ * r ∈ Subgroup.zpowers z) :
    t₁ * t₂ ∈ kerMod X z := by
  refine ⟨X.mul_mem h1 h2, ?_, fun r hr => ?_⟩
  · rw [mul_assoc, hc2, ← mul_assoc, hc1, mul_assoc]
  · have hA₂ := hr2 r hr
    have hB₁ := hr1 r⁻¹ ((pCoreOf 3 X).inv_mem hr)
    have e : (t₁ * t₂) * r * (t₁ * t₂)⁻¹ * r⁻¹ =
        (t₁ * (t₂ * r * t₂⁻¹ * r) * t₁⁻¹) * (t₁ * r⁻¹ * t₁⁻¹ * r⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_zpowers_mem (hZ t₁ h1) hA₂) hB₁

theorem good_z_eq (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) {t x z t' x' z' : MulAut V}
    (h : InvPair X t x) (hg : Good X t x z) (h' : InvPair X t' x') (hg' : Good X t' x' z') :
    Subgroup.zpowers z' = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hne := exists_normR_not_centR (D2_29 hV c hX1 hg htwo)
  have hne' := exists_normR_not_centR (D2_29 hV c hX1 hg' htwo)
  have hz'R : z' ∈ pCoreOf 3 X := (mem_centR.mp hg'.hz).1
  have hzc' := z_central hV c hX1 h' hg' hne'
  have hmem := central_cube_mem_Z hV c hX1 h hg hne hz'R (fun r hr => hzc' r hr)
  obtain ⟨-, hzo, -⟩ := Good.E9 hV c hX1 h hg
  have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  exact zpowers_eq_of_prime_card hzc hmem hg'.hz1

theorem X_normalizes_z (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) {t x z : MulAut V}
    (h : InvPair X t x) (hg : Good X t x z) :
    ∀ h' ∈ X, h' * z * h'⁻¹ ∈ Subgroup.zpowers z := by
  intro g hgX
  have hne := exists_normR_not_centR (D2_29 hV c hX1 hg htwo)
  have hzc := z_central hV c hX1 h hg hne
  have hzR : z ∈ pCoreOf 3 X := (mem_centR.mp hg.hz).1
  have hR : g * z * g⁻¹ ∈ pCoreOf 3 X :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hgX) z).mp hzR
  refine central_cube_mem_Z hV c hX1 h hg hne hR (fun r hr => ?_)
  have hr' : g⁻¹ * r * g ∈ pCoreOf 3 X := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X (X.inv_mem hgX)) r).mp hr
    simpa using this
  have h1 := hzc _ hr'
  calc g * z * g⁻¹ * r = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by rw [h1]
    _ = r * (g * z * g⁻¹) := by group

theorem tinv_data (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) {t x z : MulAut V}
    (h : InvPair X t x) (hg : Good X t x z) {t' : MulAut V} (ht' : t' ∈ TInv X) :
    t' * z = z * t' ∧ ∀ r ∈ pCoreOf 3 X, t' * r * t'⁻¹ * r ∈ Subgroup.zpowers z := by
  obtain ⟨x', hx'R, hx'1, hinv'⟩ := exists_inverted hV c ht'
  have h' : InvPair X t' x' := ⟨ht', hx'R, hx'1, hinv'⟩
  obtain ⟨z₁, hg₁⟩ := exists_good hV c hX1 htwo h'
  have hRQ := normR_eq_pCoreOf hV c hX1 htwo h' hg₁
  have heq := good_z_eq hV c hX1 htwo h hg h' hg₁
  constructor
  · have hz_in : z ∈ Subgroup.zpowers z₁ := by rw [heq]; exact Subgroup.mem_zpowers z
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz_in
    rw [← hk]
    exact ((show Commute t' z₁ from hg₁.tz).zpow_right k).eq
  · intro r hr
    rw [← heq]
    exact normR_refl hV c hX1 h' hg₁ (by rw [hRQ]; exact hr)

theorem X_eq_sup (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) {t x z : MulAut V}
    (h : InvPair X t x) (hg : Good X t x z) : X = pCoreOf 3 X ⊔ Subgroup.zpowers t := by
  have hz3 : z ^ 3 = 1 := hg.cube z hg.hz
  have hZ := X_normalizes_z hV c hX1 htwo h hg
  have hKR := kerMod_le_pCoreOf hV c hz3 hZ
  have hd₀ := tinv_data hV c hX1 htwo h hg h.ht
  apply le_antisymm
  · calc X = Subgroup.closure (TInv X) := c.closure_eq.symm
      _ ≤ pCoreOf 3 X ⊔ Subgroup.zpowers t := by
        rw [Subgroup.closure_le]
        intro t' ht'
        have hd := tinv_data hV c hX1 htwo h hg ht'
        have hK := mul_mem_kerMod hZ ht'.1 h.ht.1 hd.1 hd₀.1 hd.2 hd₀.2
        have hR := hKR hK
        have e : t' = (t' * t) * t⁻¹ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hR)
          (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)))
  · exact sup_le (pCoreOf_le 3 X) (Subgroup.zpowers_le.mpr h.ht.1)

theorem rk_V_eq_six (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) {t x z : MulAut V}
    (h : InvPair X t x) (hg : Good X t x z) : rk V = 6 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfix : fixV (Subgroup.zpowers z) = ⊥ := by
    refine eq_bot_of_le_fixV_inverted hV c hX1 (fun x' hx' hx'1 ⟨t', ht', hinv'⟩ => ?_)
    have h' : InvPair X t' x' := ⟨ht', hx', hx'1, hinv'⟩
    obtain ⟨z₁, hg₁⟩ := exists_good hV c hX1 htwo h'
    have heq := good_z_eq hV c hX1 htwo h hg h' hg₁
    have := fixV_z_le_fixV_x hV c hX1 h' hg₁
    rw [heq] at this
    exact this
  obtain ⟨-, hzo, -⟩ := Good.E9 hV c hX1 h hg
  have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  obtain ⟨-, -, hrk, -⟩ := commV_card_three hV hzc
  rw [hfix, rk_bot] at hrk
  have := hg.rk6
  omega

theorem commutator_mem_frattini_map {F : Subgroup (MulAut V)} (hF : IsPGroup 3 F)
    {a b : MulAut V} (ha : a ∈ F) (hb : b ∈ F) :
    a * b * a⁻¹ * b⁻¹ ∈ (frattini ↥F).map F.subtype := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (IsPGroup 3 ↥F) := ⟨hF⟩
  have hc : ((⟨a, ha⟩ : ↥F) * (⟨b, hb⟩ : ↥F) * (⟨a, ha⟩ : ↥F)⁻¹ * (⟨b, hb⟩ : ↥F)⁻¹) ∈
      frattini ↥F :=
    CFSG.commutator_le_frattini_of_isPGroup (p := 3)
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  exact ⟨_, hc, rfl⟩

theorem D2_17_case4 (hV : ∀ v : V, v ^ 2 = 1) (c : CycCtx X) (hX1 : ∀ Y ∈ Xk X 1, False)
    (htwo : ∃ Y₁ ∈ Yinv X, ∃ Y₂ ∈ Yinv X, Y₁ ≠ Y₂) :
    Nat.card (fittingOf X) = 27 ∧ (∀ f ∈ fittingOf X, f ^ 3 = 1) ∧
      (∃ f ∈ fittingOf X, ∃ g ∈ fittingOf X, f * g ≠ g * f) ∧
      (∃ t ∈ X, orderOf t = 2 ∧
        (∀ f ∈ fittingOf X,
          t * f * t⁻¹ * f ∈ (frattini ↥(fittingOf X)).map (fittingOf X).subtype) ∧
        X = fittingOf X ⊔ Subgroup.zpowers t) ∧ rk V = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have htwo' := htwo
  obtain ⟨Y₁, hY₁, -⟩ := htwo'
  obtain ⟨x, t, h, -, -, -⟩ := Yinv_data hV c hX1 hY₁
  obtain ⟨z, hg⟩ := exists_good hV c hX1 htwo h
  have h229 := D2_29 hV c hX1 hg htwo
  have hne := exists_normR_not_centR h229
  have hRQ := normR_eq_pCoreOf hV c hX1 htwo h hg
  have hcard := card_normR hV c hX1 h hg hne
  have hF : fittingOf X = pCoreOf 3 X := c.fittingOf_eq hV
  have hFp : IsPGroup 3 (fittingOf X) := by rw [hF]; exact pCoreOf_isPGroup 3 X
  obtain ⟨hxo, hzo, hxz, hne', hsup⟩ := Good.E9 hV c hX1 h hg
  have hzc : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  obtain ⟨q, hq, hqP⟩ := hne
  have hζq1 : q * x * q⁻¹ * x⁻¹ ≠ 1 := by
    intro e
    apply hqP
    have h2 : q * x * q⁻¹ = x := mul_inv_eq_one.mp e
    exact mem_centR.mpr ⟨hq.1, mul_inv_eq_iff_eq_mul.mp h2⟩
  have hqF : q ∈ fittingOf X := by rw [hF]; exact hq.1
  have hxF : x ∈ fittingOf X := by rw [hF]; exact h.hx
  have hζΦ := commutator_mem_frattini_map hFp hqF hxF
  have hζz := normR_x_mod_z hV c hX1 h hg hq
  have hzeq : Subgroup.zpowers (q * x * q⁻¹ * x⁻¹) = Subgroup.zpowers z :=
    zpowers_eq_of_prime_card hzc hζz hζq1
  have hzΦ : Subgroup.zpowers z ≤ (frattini ↥(fittingOf X)).map (fittingOf X).subtype := by
    rw [← hzeq]
    exact Subgroup.zpowers_le.mpr hζΦ
  refine ⟨?_, ?_, ?_, ⟨t, h.ht.1, orderOf_eq_prime h.ht.2.2.1 h.ht.2.1, ?_, ?_⟩,
    rk_V_eq_six hV c hX1 htwo h hg⟩
  · rw [hF, ← hRQ]
    exact hcard
  · intro f hf
    rw [hF, ← hRQ] at hf
    exact normR_cube hV c hX1 h hg hf
  · refine ⟨q, hqF, x, hxF, fun e => hqP (mem_centR.mpr ⟨hq.1, e⟩)⟩
  · intro f hf
    have hfR : f ∈ normR X x := by rw [hRQ, ← hF]; exact hf
    exact hzΦ (normR_refl hV c hX1 h hg hfR)
  · rw [hF]
    exact X_eq_sup hV c hX1 htwo h hg

end End

end CFSG.Quasithin
