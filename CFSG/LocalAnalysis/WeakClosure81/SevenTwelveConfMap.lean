module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelve

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {X X' : Type} [Group X] [Group X']

@[expose] def sevenTwelveGen (S : Subgroup X) (g₂ g₃ : X) : Subgroup X :=
  S ⊔ conjSubgroup S g₂ ⊔ conjSubgroup S g₃

theorem sevenTwelve_conjSubgroup_zpowers (t g : X) :
    conjSubgroup (Subgroup.zpowers t) g = Subgroup.zpowers (g⁻¹ * t * g) := by
  rw [conjSubgroup, MonoidHom.map_zpowers]
  congr 1
  change (MulAut.conj g⁻¹) t = g⁻¹ * t * g
  rw [MulAut.conj_apply, inv_inv]

theorem sevenTwelve_map_conjSubgroup (φ : X →* X') (A : Subgroup X) (g : X) :
    (conjSubgroup A g).map φ = conjSubgroup (A.map φ) (φ g) := by
  rw [conjSubgroup, conjSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply,
    MulAut.conj_apply, inv_inv, map_mul]

theorem map_sevenTwelveGen (φ : X →* X') (S : Subgroup X) (g₂ g₃ : X) :
    (sevenTwelveGen S g₂ g₃).map φ = sevenTwelveGen (S.map φ) (φ g₂) (φ g₃) := by
  unfold sevenTwelveGen
  rw [Subgroup.map_sup, Subgroup.map_sup, sevenTwelve_map_conjSubgroup,
    sevenTwelve_map_conjSubgroup]

private lemma sevenTwelveMap_zpowers_eq_of_sq_eq_one {a x : X'} (ha : a * a = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, ha]
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, ha2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, ha2, one_zpow]
    simp

private lemma sevenTwelveMap_conj_sq_eq_one {t g : X} (ht : t * t = 1) :
    (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
  rw [show (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g by group, ht]
  group

private lemma sevenTwelveMap_commute_of_commutator_mem_ker {φ : X →* X'}
    (hcen : φ.ker ≤ Subgroup.center X) (hinv : ∀ z ∈ φ.ker, z * z = 1 → z = 1)
    {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hc : ⁅a, b⁆ ∈ φ.ker) :
    Commute a b := by
  have hcent : ⁅a, b⁆ ∈ Subgroup.center X := hcen hc
  have hbc : b * ⁅a, b⁆ = ⁅a, b⁆ * b := Subgroup.mem_center_iff.mp hcent b
  have hsq_a : (a * b * a⁻¹) * (a * b * a⁻¹) = 1 := by
    rw [show (a * b * a⁻¹) * (a * b * a⁻¹) = a * (b * b) * a⁻¹ by group, hb]
    group
  have hsq : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
    have h : (⁅a, b⁆ * b) * (⁅a, b⁆ * b) = ⁅a, b⁆ * ⁅a, b⁆ := by
      calc (⁅a, b⁆ * b) * (⁅a, b⁆ * b)
          = ⁅a, b⁆ * (b * ⁅a, b⁆) * b := by group
        _ = ⁅a, b⁆ * (⁅a, b⁆ * b) * b := by rw [hbc]
        _ = (⁅a, b⁆ * ⁅a, b⁆) * (b * b) := by group
        _ = (⁅a, b⁆ * ⁅a, b⁆) * 1 := by rw [hb]
        _ = ⁅a, b⁆ * ⁅a, b⁆ := by rw [mul_one]
    rw [← h]
    rw [show ⁅a, b⁆ * b = a * b * a⁻¹ by rw [commutatorElement_def]; group]
    exact hsq_a
  exact commutatorElement_eq_one_iff_commute.mp (hinv _ hc hsq)

private lemma sevenTwelveMap_eq_one_or_eq_of_map_mem {φ : X →* X'}
    (hcen : φ.ker ≤ Subgroup.center X) (hinv : ∀ z ∈ φ.ker, z * z = 1 → z = 1)
    {t x : X} (ht : t * t = 1) (hx : x * x = 1)
    (hmem : φ x ∈ Subgroup.zpowers (φ t)) : x = 1 ∨ x = t := by
  have hφt : φ t * φ t = 1 := by rw [← map_mul, ht, map_one]
  rcases sevenTwelveMap_zpowers_eq_of_sq_eq_one hφt hmem with h1 | h1
  · left
    exact hinv x (by rw [MonoidHom.mem_ker]; exact h1) hx
  · right
    have hzker : x * t⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have hzmem : x * t⁻¹ ∈ Subgroup.center X := hcen hzker
    have hzt : x = (x * t⁻¹) * t := by group
    have hzz : x * x = (x * t⁻¹) * (x * t⁻¹) := by
      conv_lhs => rw [hzt]
      calc ((x * t⁻¹) * t) * ((x * t⁻¹) * t)
          = (x * t⁻¹) * (t * (x * t⁻¹)) * t := by group
        _ = (x * t⁻¹) * ((x * t⁻¹) * t) * t := by
              rw [Subgroup.mem_center_iff.mp hzmem t]
        _ = ((x * t⁻¹) * (x * t⁻¹)) * (t * t) := by group
        _ = ((x * t⁻¹) * (x * t⁻¹)) * 1 := by rw [ht]
        _ = (x * t⁻¹) * (x * t⁻¹) := by rw [mul_one]
    have hzsq : (x * t⁻¹) * (x * t⁻¹) = 1 := by rw [← hzz, hx]
    have hz1 : x * t⁻¹ = 1 := hinv _ hzker hzsq
    rw [hzt, hz1, one_mul]

private lemma sevenTwelveMap_commutator_zpowers_eq_bot {φ : X →* X'}
    (hcen : φ.ker ≤ Subgroup.center X) (hinv : ∀ z ∈ φ.ker, z * z = 1 → z = 1)
    {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (h : ⁅Subgroup.zpowers (φ a), Subgroup.zpowers (φ b)⁆ = ⊥) :
    ⁅Subgroup.zpowers a, Subgroup.zpowers b⁆ = ⊥ := by
  have hcommute : φ a * φ b = φ b * φ a := by
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hmem : φ a ∈ Subgroup.centralizer (Subgroup.zpowers (φ b) : Set X') :=
      Subgroup.zpowers_le.mp hle
    exact (Subgroup.mem_centralizer_iff.mp hmem (φ b) (Subgroup.mem_zpowers (φ b))).symm
  have hker : ⁅a, b⁆ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcommute
  have hcomm : Commute a b := sevenTwelveMap_commute_of_commutator_mem_ker hcen hinv ha hb hker
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hcomm.zpow_right m).symm

theorem sevenTwelveConfig_map (φ : X →* X') (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center X) (hinv : ∀ z ∈ φ.ker, z * z = 1 → z = 1)
    {t g₂ g₃ y : X} (ht : t * t = 1) {W T : Subgroup X}
    (h : SevenTwelveConfig (Subgroup.zpowers t) g₂ g₃ y W T) :
    SevenTwelveConfig (Subgroup.zpowers (φ t)) (φ g₂) (φ g₃) (φ y) (W.map φ) (T.map φ) := by
  let x₂ : X := g₂⁻¹ * t * g₂
  let x₃ : X := g₃⁻¹ * t * g₃
  have hx₂ : conjSubgroup (Subgroup.zpowers t) g₂ = Subgroup.zpowers x₂ :=
    sevenTwelve_conjSubgroup_zpowers t g₂
  have hx₃ : conjSubgroup (Subgroup.zpowers t) g₃ = Subgroup.zpowers x₃ :=
    sevenTwelve_conjSubgroup_zpowers t g₃
  have hx₂sq : x₂ * x₂ = 1 := sevenTwelveMap_conj_sq_eq_one ht
  have hx₃sq : x₃ * x₃ = 1 := sevenTwelveMap_conj_sq_eq_one ht
  have hS : (Subgroup.zpowers t).map φ = Subgroup.zpowers (φ t) := MonoidHom.map_zpowers φ t
  have hφt : φ t * φ t = 1 := by rw [← map_mul, ht, map_one]
  have hconj₂ : Subgroup.zpowers (φ x₂) = conjSubgroup (Subgroup.zpowers (φ t)) (φ g₂) := by
    rw [← MonoidHom.map_zpowers, ← hx₂, sevenTwelve_map_conjSubgroup, hS]
  have hconj₃ : Subgroup.zpowers (φ x₃) = conjSubgroup (Subgroup.zpowers (φ t)) (φ g₃) := by
    rw [← MonoidHom.map_zpowers, ← hx₃, sevenTwelve_map_conjSubgroup, hS]
  have hLmap : (sevenTwelveGen (Subgroup.zpowers t) g₂ g₃).map φ =
      sevenTwelveGen (Subgroup.zpowers (φ t)) (φ g₂) (φ g₃) := by
    rw [map_sevenTwelveGen, hS]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro heq
    have hmem : φ x₂ ∈ Subgroup.zpowers (φ t) := by
      rw [← heq, ← hconj₂]
      exact Subgroup.mem_zpowers (φ x₂)
    rcases sevenTwelveMap_eq_one_or_eq_of_map_mem hcen hinv ht hx₂sq hmem with h1 | h1
    · refine h.ne ?_
      have hbot : Subgroup.zpowers (φ t) = ⊥ := by
        rw [← heq, ← hconj₂, h1, map_one, Subgroup.zpowers_one_eq_bot]
      have htker : t ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subgroup.zpowers_eq_bot.mp hbot
      have ht1 : t = 1 := hinv t htker ht
      rw [hx₂, h1, Subgroup.zpowers_one_eq_bot, ht1, Subgroup.zpowers_one_eq_bot]
    · refine h.ne ?_
      rw [hx₂, h1]
  ·
    intro hcomm
    rw [← hconj₃] at hcomm
    have hcom := sevenTwelveMap_commutator_zpowers_eq_bot hcen hinv ht hx₃sq hcomm
    rw [← hx₃] at hcom
    exact h.comm₁₃ hcom
  ·
    intro hcomm
    rw [← hconj₂, ← hconj₃] at hcomm
    have hcom := sevenTwelveMap_commutator_zpowers_eq_bot hcen hinv hx₂sq hx₃sq hcomm
    rw [← hx₂, ← hx₃] at hcom
    exact h.comm₂₃ hcom
  ·
    change ⁅sevenTwelveGen (Subgroup.zpowers (φ t)) (φ g₂) (φ g₃),
        sevenTwelveGen (Subgroup.zpowers (φ t)) (φ g₂) (φ g₃)⁆ =
        sevenTwelveGen (Subgroup.zpowers (φ t)) (φ g₂) (φ g₃)
    rw [← hLmap, ← Subgroup.map_commutator,
      show ⁅sevenTwelveGen (Subgroup.zpowers t) g₂ g₃,
          sevenTwelveGen (Subgroup.zpowers t) g₂ g₃⁆ =
          sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ from h.perfect]
  ·
    exact h.w_two.map φ
  ·
    simpa only [MonoidHom.map_zpowers] using Subgroup.map_mono (f := φ) h.le_w
  ·
    simpa only [sevenTwelve_map_conjSubgroup, MonoidHom.map_zpowers] using
      Subgroup.map_mono (f := φ) h.le_w₂
  ·
    have hmap := Subgroup.map_mono (f := φ) h.w_le
    rwa [Subgroup.map_sup, Subgroup.map_sup, sevenTwelve_map_conjSubgroup,
      sevenTwelve_map_conjSubgroup, MonoidHom.map_zpowers] at hmap
  ·
    exact h.t_two.map φ
  ·
    have hle : T.map φ ≤ Subgroup.normalizer (Subgroup.zpowers (φ t) : Set X') := by
      have hmap := (Subgroup.map_mono (f := φ) h.t_le).trans
        (Subgroup.le_normalizer_map (H := Subgroup.zpowers t) φ)
      rwa [hS] at hmap
    exact hle
  ·
    change sevenTwelveGen (Subgroup.zpowers (φ t)) (φ g₂) (φ g₃) ⊔ T.map φ = ⊤
    rw [← hLmap, ← Subgroup.map_sup,
      show sevenTwelveGen (Subgroup.zpowers t) g₂ g₃ ⊔ T = ⊤ from h.gen]
    exact Subgroup.map_top_of_surjective φ hφ
  ·
    have hmap := Subgroup.mem_map_of_mem φ h.y_mem
    rwa [Subgroup.map_sup, Subgroup.map_sup, sevenTwelve_map_conjSubgroup,
      sevenTwelve_map_conjSubgroup, MonoidHom.map_zpowers] at hmap
  ·
    exact (Subgroup.le_normalizer_map (H := T) φ) (Subgroup.mem_map_of_mem φ h.y_t)
  ·
    exact (Subgroup.le_normalizer_map (H := W) φ) (Subgroup.mem_map_of_mem φ h.y_w)
  ·
    intro hy
    have hmem : φ (y * t * y⁻¹) ∈ Subgroup.zpowers (φ t) := by
      have hnorm := (Subgroup.mem_normalizer_iff.mp hy (φ t)).mp (Subgroup.mem_zpowers (φ t))
      simpa only [map_mul, map_inv] using hnorm
    have hysq : (y * t * y⁻¹) * (y * t * y⁻¹) = 1 := by
      rw [show (y * t * y⁻¹) * (y * t * y⁻¹) = y * (t * t) * y⁻¹ by group, ht]
      group
    rcases sevenTwelveMap_eq_one_or_eq_of_map_mem hcen hinv ht hysq hmem with h1 | h1
    · refine h.y_s ?_
      have ht1 : t = 1 := by
        calc t = y⁻¹ * (y * t * y⁻¹) * y := by group
          _ = 1 := by rw [h1]; group
      rw [ht1, Subgroup.zpowers_one_eq_bot, Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top y
    · refine h.y_s ?_
      have hfix : y⁻¹ * t * y = t := by
        calc y⁻¹ * t * y = y⁻¹ * (y * t * y⁻¹) * y := by rw [h1]
          _ = t := by group
      exact conjSubgroup_eq_iff_mem_normalizer.mp (by
        rw [sevenTwelve_conjSubgroup_zpowers, hfix])

theorem sevenTwelveConfig_mulEquiv (e : X ≃* X') {t g₂ g₃ y : X} (ht : t * t = 1)
    {W T : Subgroup X} (h : SevenTwelveConfig (Subgroup.zpowers t) g₂ g₃ y W T) :
    SevenTwelveConfig (Subgroup.zpowers (e t)) (e g₂) (e g₃) (e y) (W.map (e : X →* X'))
      (T.map (e : X →* X')) := by
  refine sevenTwelveConfig_map (e : X →* X') e.surjective ?_ ?_ ht h
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    rw [e.injective (hz.trans (map_one e).symm)]
    exact Subgroup.one_mem _
  · intro z hz _
    rw [MonoidHom.mem_ker] at hz
    exact e.injective (hz.trans (map_one e).symm)

end CFSG.LocalAnalysis.WeakClosure81

end
