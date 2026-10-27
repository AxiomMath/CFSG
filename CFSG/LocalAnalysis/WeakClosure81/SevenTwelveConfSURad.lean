module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSUElt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] {σ : F ≃+* F} {m : ℕ}

@[expose] def suConfRad (e : Fin m → F) : Subgroup ↥(SUid σ m) where
  carrier := {g | g • e = e ∧ ∀ v, herm σ e v = 0 → ∃ a : F, g • v = v + a • e}
  mul_mem' := by
    rintro g h ⟨hge, hg⟩ ⟨hhe, hh⟩
    refine ⟨by rw [mul_smul, hhe, hge], fun v hv => ?_⟩
    obtain ⟨a, ha⟩ := hh v hv
    obtain ⟨b, hb⟩ := hg v hv
    refine ⟨b + a, ?_⟩
    rw [mul_smul, ha, smul_add, smul_comm g a e, hge, hb]
    module
  one_mem' := ⟨one_smul _ _, fun v _ => ⟨0, by rw [one_smul, zero_smul, add_zero]⟩⟩
  inv_mem' := by
    rintro g ⟨hge, hg⟩
    have hge' : g⁻¹ • e = e := by
      conv_lhs => rw [← hge]
      rw [inv_smul_smul]
    refine ⟨hge', fun v hv => ?_⟩
    have hw : herm σ e (g⁻¹ • v) = 0 := by
      have h := herm_smul_smul σ g e (g⁻¹ • v)
      rw [hge, smul_inv_smul] at h
      rw [← h, hv]
    obtain ⟨a, ha⟩ := hg (g⁻¹ • v) hw
    rw [smul_inv_smul] at ha
    have h2 : g⁻¹ • v = v - a • e := by
      rw [eq_sub_iff_add_eq]
      exact ha.symm
    exact ⟨-a, by rw [h2]; module⟩

theorem mem_suConfRad {e : Fin m → F} {g : ↥(SUid σ m)} :
    g ∈ suConfRad e ↔ g • e = e ∧ ∀ v, herm σ e v = 0 → ∃ a : F, g • v = v + a • e :=
  Iff.rfl

private lemma suConfRad_add_self [CharP F 2] (x : Fin m → F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [← two_smul F x, h2, zero_smul]

private lemma suConfRad_neg_eq [CharP F 2] (x : Fin m → F) : -x = x := by
  funext i
  exact CharTwo.neg_eq (x i)

private lemma inv_smul_eq_of_smul_eq {e : Fin m → F} {g : ↥(SUid σ m)} {a : F} (ha : a ≠ 0)
    (hg : g • e = a • e) : g⁻¹ • e = a⁻¹ • e := by
  have h : e = a • (g⁻¹ • e) := by
    have h := congrArg (fun x => g⁻¹ • x) hg
    rwa [inv_smul_smul, smul_comm g⁻¹ a e] at h
  have h2 : a⁻¹ • e = g⁻¹ • e := by
    calc a⁻¹ • e = a⁻¹ • (a • (g⁻¹ • e)) := congrArg (fun x => a⁻¹ • x) h
      _ = (a⁻¹ * a) • (g⁻¹ • e) := by rw [smul_smul]
      _ = g⁻¹ • e := by rw [inv_mul_cancel₀ ha, one_smul]
  exact h2.symm

private lemma conj_mem_suConfRad {e : Fin m → F} {g q : ↥(SUid σ m)} {a : F} (ha : a ≠ 0)
    (hg : g • e = a • e) (hq : q ∈ suConfRad e) : g * q * g⁻¹ ∈ suConfRad e := by
  have hge : g⁻¹ • e = a⁻¹ • e := inv_smul_eq_of_smul_eq ha hg
  rw [mem_suConfRad]
  constructor
  · rw [mul_smul, mul_smul, hge, smul_comm q a⁻¹ e, hq.1, smul_comm g a⁻¹ e, hg, smul_smul,
      inv_mul_cancel₀ ha, one_smul]
  · intro v hv
    have hw : herm σ e (g⁻¹ • v) = 0 := by
      have h := herm_smul_smul σ g e (g⁻¹ • v)
      rw [hg, smul_inv_smul, herm_smul_left, hv, mul_zero] at h
      exact h.symm
    obtain ⟨b, hb⟩ := hq.2 (g⁻¹ • v) hw
    refine ⟨b * a, ?_⟩
    rw [mul_smul, mul_smul, hb, smul_add, smul_inv_smul, smul_comm g b e, hg, smul_smul]

private lemma eq_of_add_eq_zero [CharP F 2] {s : F} (hs : s + σ s = 0) : σ s = s := by
  have h2 : s + s = 0 := CharTwo.add_self_eq_zero s
  exact add_left_cancel (hs.trans h2.symm)

variable (e : Fin m → F)

theorem isPGroup_suConfRad [CharP F 2] : IsPGroup 2 (suConfRad (σ := σ) e) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  apply ext_smul
  intro v
  rw [one_smul]
  set G : ↥(SUid σ m) := (g : ↥(SUid σ m)) with hG
  have hge : G • e = e := by rw [hG]; exact g.2.1
  have hgq : ∀ v, herm σ e v = 0 → ∃ a : F, G • v = v + a • e := by
    intro v hv
    rw [hG]
    exact g.2.2 v hv
  change (G ^ 4) • v = v
  set w : Fin m → F := G • v + v with hw
  have hper : herm σ e w = 0 := by
    rw [hw, herm_add_right]
    have h1 : herm σ e (G • v) = herm σ e v := by
      simpa only [hge] using herm_smul_smul σ G e v
    rw [h1]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨a, ha⟩ := hgq w hper
  have hg2 : (G ^ 2) • v = v + a • e := by
    have hsplit : G • (G • v) = G • w + G • v := by
      rw [hw, smul_add, add_assoc, suConfRad_add_self, add_zero]
    rw [pow_two, mul_smul, hsplit, ha, hw]
    calc ((G • v + v) + a • e) + G • v = (G • v + G • v) + (v + a • e) := by abel
      _ = 0 + (v + a • e) := by rw [suConfRad_add_self]
      _ = v + a • e := by rw [zero_add]
  have hg2e : (G ^ 2) • e = e := by rw [pow_two, mul_smul, hge, hge]
  rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, mul_smul]
  rw [hg2, smul_add, smul_comm, hg2e, hg2]
  calc (v + a • e) + a • e = v + (a • e + a • e) := by rw [add_assoc]
    _ = v + 0 := by rw [suConfRad_add_self]
    _ = v := by rw [add_zero]

theorem suTv_mem_suConfRad (hσ : IsUnitaryInvolution σ) (he : herm σ e e = 0) (a s : F)
    (hs : s + σ s = 0) : suTv hσ (a • e) s ∈ suConfRad e := by
  have ha : herm σ (a • e) (a • e) = 0 := by
    rw [herm_smul_left, herm_smul_right, he, mul_zero, mul_zero]
  rw [mem_suConfRad]
  refine ⟨?_, fun v hv => ⟨0, ?_⟩⟩
  · simp only [suTv_smul hσ ha hs, herm_smul_left, he, mul_zero, zero_smul, add_zero]
  · simp only [suTv_smul hσ ha hs, herm_smul_left, hv, mul_zero, zero_smul, add_zero]

theorem commute_suConfT_of_mem_suConfRad [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (he : herm σ e e = 0) {g : ↥(SUid σ m)} (hg : g ∈ suConfRad e) :
    g * suConfT hσ e = suConfT hσ e * g := by
  have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
  have hconj : g * suConfT hσ e * g⁻¹ = suConfT hσ e := by
    rw [suConfT, suTv_conj hσ g he h1, hg.1]
  calc g * suConfT hσ e = g * suConfT hσ e * 1 := by rw [mul_one]
    _ = g * suConfT hσ e * (g⁻¹ * g) := by rw [inv_mul_cancel]
    _ = (g * suConfT hσ e * g⁻¹) * g := by group
    _ = suConfT hσ e * g := by rw [hconj]

theorem mem_normalizer_suConfRad {g : ↥(SUid σ m)} {a : F} (ha : a ≠ 0) (hg : g • e = a • e) :
    g ∈ Subgroup.normalizer (suConfRad (σ := σ) e : Set ↥(SUid σ m)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    exact conj_mem_suConfRad ha hg hq
  · intro hq
    have hg' : g⁻¹ • e = a⁻¹ • e := inv_smul_eq_of_smul_eq ha hg
    have h := conj_mem_suConfRad (inv_ne_zero ha) hg' hq
    have hq' : q = g⁻¹ * (g * q * g⁻¹) * g := by group
    rwa [hq']

@[expose] def suCenter (hσ : IsUnitaryInvolution σ) (H : Subgroup ↥(SUid σ m))
    (a : Fin m → F) : Prop :=
  herm σ a a = 0 ∧ ∀ s : F, s + σ s = 0 → suTv hσ a s ∈ H

variable {hσ : IsUnitaryInvolution σ} {e} {f : Fin m → F} {c : F}

private lemma herm_shift_self {y : Fin m → F} (hinvol : ∀ c, σ (σ c) = c)
    (he : herm σ e e = 0) (hf : herm σ f f = 0) (hef : herm σ e f = 1)
    (hye : herm σ e y = 0) (hyf : herm σ f y = 0) (α : F) :
    herm σ (f + y + α • e) (f + y + α • e) = herm σ y y + (α + σ α) := by
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hinvol, hef, map_one]
  have hye' : herm σ y e = 0 := herm_eq_zero_comm σ hinvol hye
  have hyf' : herm σ y f = 0 := herm_eq_zero_comm σ hinvol hyf
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hf, he,
    hye, hyf, hye', hyf', hef, hfe, mul_zero, mul_one, zero_mul, add_zero, zero_add]
  ring

theorem suConf_center_f [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) {H : Subgroup ↥(SUid σ m)}
    (hn : suConfN hσ e f c ∈ H) (hCe : suCenter hσ H e) : suCenter hσ H f := by
  refine ⟨hf, fun s' hs' => ?_⟩
  have hσs' : σ s' = s' := eq_of_add_eq_zero hs'
  set s : F := c * c * s' with hsdef
  have hs : s + σ s = 0 := by
    rw [hsdef, map_mul, map_mul, hcσ, hσs']
    exact CharTwo.add_self_eq_zero (c * c * s')
  have hmem : suConfN hσ e f c * suTv hσ e s * (suConfN hσ e f c)⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hn (hCe.2 s hs)) (H.inv_mem hn)
  have hkey : suConfN hσ e f c * suTv hσ e s * (suConfN hσ e f c)⁻¹ = suTv hσ f s' := by
    rw [suTv_conj hσ (suConfN hσ e f c) he hs, (suConfN_apply he hf hef hcσ hc).1,
      suTv_smul_vec hσ hf hs c⁻¹]
    congr 1
    rw [hsdef, map_inv₀, hcσ]
    field_simp
  rwa [hkey] at hmem

theorem suConf_center_shift [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) {H : Subgroup ↥(SUid σ m)} (hQ : suConfRad e ≤ H)
    (hCf : suCenter hσ H f) {y : Fin m → F} (hye : herm σ e y = 0) (hyf : herm σ f y = 0)
    {c' : F} (hc' : c' + σ c' = herm σ y y) : suCenter hσ H (f + y + c' • e) := by
  have hc'' : c' + σ c' = -herm σ y y := by
    rw [CharTwo.neg_eq]
    exact hc'
  have hiso : herm σ (f + y + c' • e) (f + y + c' • e) = 0 := by
    rw [herm_shift_self hσ.invol he hf hef hye hyf c', hc']
    exact CharTwo.add_self_eq_zero _
  set g : ↥(SUid σ m) := eichler hσ.invol he hye hc'' with hgdef
  have hge : g • e = e := eichler_smul_self hσ.invol he hye hc''
  have hgQ : g ∈ suConfRad e := by
    rw [mem_suConfRad]
    refine ⟨hge, fun v hv => ⟨herm σ y v, ?_⟩⟩
    rw [hgdef, eichler_smul hσ.invol he hye hc'', hv, zero_smul, add_zero,
      sub_eq_add_neg, suConfRad_neg_eq]
  have hgH : g ∈ H := hQ hgQ
  refine ⟨hiso, fun s hs => ?_⟩
  have hmem : g * suTv hσ f s * g⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hgH (hCf.2 s hs)) (H.inv_mem hgH)
  have hgf : g • f = f + y + c' • e := by
    rw [hgdef, eichler_smul hσ.invol he hye hc'', hef, herm_eq_zero_comm σ hσ.invol hyf,
      one_smul, zero_smul, sub_zero]
    abel
  have hkey : g * suTv hσ f s * g⁻¹ = suTv hσ (f + y + c' • e) s := by
    rw [suTv_conj hσ g hf hs, hgf]
  rwa [hkey] at hmem

theorem suConf_center_hyp [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) {H : Subgroup ↥(SUid σ m)} (hQ : suConfRad e ≤ H)
    (hCf : suCenter hσ H f) {a : Fin m → F} (ha : herm σ a a = 0) (hea : herm σ e a ≠ 0) :
    suCenter hσ H a := by
  have hfe : herm σ f e = 1 := by rw [herm_conj σ hσ.invol, hef, map_one]
  set d : F := herm σ e a with hddef
  have hd : d ≠ 0 := hea
  set a' : Fin m → F := d⁻¹ • a with ha'def
  have ha'a' : herm σ a' a' = 0 := by
    rw [ha'def, herm_smul_left, herm_smul_right, ha, mul_zero, mul_zero]
  have hea' : herm σ e a' = 1 := by
    rw [ha'def, herm_smul_right, ← hddef, inv_mul_cancel₀ hd]
  set α : F := herm σ f a' with hαdef
  set y : Fin m → F := a' - α • e - f with hydef
  have hye : herm σ e y = 0 := by
    rw [hydef, herm_sub_right, herm_sub_right, hea', herm_smul_right, he, mul_zero, hef,
      sub_zero, sub_self]
  have hyf : herm σ f y = 0 := by
    rw [hydef, herm_sub_right, herm_sub_right, ← hαdef, herm_smul_right, hfe, mul_one, hf,
      sub_self, sub_zero]
  have ha'repr : a' = f + y + α • e := by
    rw [hydef]
    abel
  have hα : α + σ α = herm σ y y := by
    have h0 : herm σ y y + (α + σ α) = 0 := by
      have h := ha'a'
      rw [ha'repr, herm_shift_self hσ.invol he hf hef hye hyf α] at h
      exact h
    have h1 : α + σ α + herm σ y y = 0 := by rw [add_comm]; exact h0
    calc α + σ α = (α + σ α) + (herm σ y y + herm σ y y) := by
          rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (α + σ α + herm σ y y) + herm σ y y := by abel
      _ = herm σ y y := by rw [h1, zero_add]
  have hca' : suCenter hσ H a' := by
    have h := suConf_center_shift he hf hef hQ hCf hye hyf hα
    rwa [← ha'repr] at h
  refine ⟨ha, fun s hs => ?_⟩
  have htr : (σ d * d * s) + σ (σ d * d * s) = 0 := by
    rw [map_mul, map_mul, hσ.invol, eq_of_add_eq_zero hs, mul_comm d (σ d)]
    exact CharTwo.add_self_eq_zero _
  have hda : d • a' = a := by
    rw [ha'def, smul_smul, mul_inv_cancel₀ hd, one_smul]
  have hsmulvec : suTv hσ a s = suTv hσ a' (σ d * d * s) := by
    rw [← hda]
    rw [suTv_smul_vec hσ (a := a') ha'a' hs d]
  rw [hsmulvec]
  exact hca'.2 (σ d * d * s) htr

theorem suConf_center_all [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) {H : Subgroup ↥(SUid σ m)} (hQ : suConfRad e ≤ H)
    (hCe : suCenter hσ H e) (hCf : suCenter hσ H f) {a : Fin m → F} (ha : herm σ a a = 0) :
    suCenter hσ H a := by
  by_cases hea : herm σ e a = 0
  · by_cases ha0 : a = 0
    · subst a
      refine ⟨by simp, fun s hs => ?_⟩
      have h0 : suTv hσ (0 : Fin m → F) s = 1 := by
        apply ext_smul
        intro v
        rw [suTv_smul hσ (by simp) hs, herm_zero_left, mul_zero, zero_smul, add_zero,
          one_smul]
      rw [h0]
      exact H.one_mem
    · have he0 : e ≠ 0 := by
        rintro rfl
        rw [herm_zero_left] at hef
        exact zero_ne_one hef
      obtain ⟨d, hd_iso, hed, had⟩ := exists_cno hσ (a := e) (b := a) he0 he ha0
      have hdCenter : suCenter hσ H d := suConf_center_hyp he hf hef hQ hCf hd_iso hed
      have h1 : (1 : F) + σ 1 = 0 := by rw [map_one]; exact CharTwo.add_self_eq_zero 1
      have hgH : suTv hσ d 1 ∈ H := hdCenter.2 1 h1
      set g : ↥(SUid σ m) := suTv hσ d 1 with hgdef
      have hga : g • a = a + herm σ d a • d := by
        rw [hgdef, suTv_smul hσ hd_iso h1, one_mul]
      have hga_iso : herm σ (g • a) (g • a) = 0 := by
        rw [herm_smul_smul, ha]
      have hda : herm σ d a ≠ 0 := by
        intro h
        apply had
        rw [herm_conj σ hσ.invol, h, map_zero]
      have hga_e : herm σ e (g • a) ≠ 0 := by
        rw [hga, herm_add_right, herm_smul_right, hea, zero_add]
        exact mul_ne_zero hda hed
      have hgaCenter : suCenter hσ H (g • a) :=
        suConf_center_hyp he hf hef hQ hCf hga_iso hga_e
      refine ⟨ha, fun s hs => ?_⟩
      have hmem : g⁻¹ * suTv hσ (g • a) s * g ∈ H :=
        H.mul_mem (H.mul_mem (H.inv_mem hgH) (hgaCenter.2 s hs)) hgH
      have hkey : g⁻¹ * suTv hσ (g • a) s * g = suTv hσ a s := by
        have h1' : g⁻¹ * suTv hσ (g • a) s * g =
            g⁻¹ * suTv hσ (g • a) s * (g⁻¹)⁻¹ := by rw [inv_inv]
        rw [h1', suTv_conj hσ g⁻¹ hga_iso hs, inv_smul_smul]
      rwa [hkey] at hmem
  · exact suConf_center_hyp he hf hef hQ hCf ha hea

theorem suConf_eq_top_of_center (hσ : IsUnitaryInvolution σ) {H : Subgroup ↥(SUid σ m)}
    (hm : 2 ≤ m) (h3 : m = 3 → ∃ s : F, s ≠ 0 ∧ σ s * s ≠ 1)
    (hall : ∀ a, herm σ a a = 0 → suCenter hσ H a) : H = ⊤ := by
  have hTH : T σ m ≤ H := by
    change Subgroup.closure (tvSet σ m) ≤ H
    rw [Subgroup.closure_le]
    rintro g ⟨a, c, ha, hc, hg⟩
    have hgs : g = suTv hσ a c := by
      apply ext_smul
      intro v
      rw [hg v, suTv_smul hσ ha hc]
    rw [hgs]
    exact (hall a ha).2 c hc
  have htop := T_eq_top hσ hm h3
  rw [htop] at hTH
  exact eq_top_iff.mpr hTH

theorem suConf_gen [CharP F 2] (he : herm σ e e = 0) (hf : herm σ f f = 0)
    (hef : herm σ e f = 1) (hcσ : σ c = c) (hc : c ≠ 0) (hm : 2 ≤ m)
    (h3 : m = 3 → ∃ s : F, s ≠ 0 ∧ σ s * s ≠ 1) (H : Subgroup ↥(SUid σ m))
    (hn : suConfN hσ e f c ∈ H) (hQ : suConfRad e ≤ H) : H = ⊤ := by
  have hCe : suCenter hσ H e := ⟨he, fun s hs => by
    simpa using hQ (suTv_mem_suConfRad e hσ he 1 s hs)⟩
  have hCf := suConf_center_f he hf hef hcσ hc hn hCe
  exact suConf_eq_top_of_center hσ hm h3 fun a ha => suConf_center_all he hf hef hQ hCe hCf ha

end CFSG.LocalAnalysis.WeakClosure81

end
