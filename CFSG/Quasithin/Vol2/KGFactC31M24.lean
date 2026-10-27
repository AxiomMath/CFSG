module

public import CFSG.Quasithin.Vol2.KGFactC31M24Det

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

theorem prime_dvd_m24 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 244823040) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  have h' : p ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5); omega
          · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h5); omega
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h4)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1)))

theorem sylow_of_order {x : G₀} {p : ℕ} [Fact p.Prime]
    (hx : orderOf x = p) (hpi : ¬ p ∣ 244823040 / p) :
    IsPGroup p (Subgroup.zpowers x) ∧ ¬ p ∣ (Subgroup.zpowers x).index := by
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  refine ⟨IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one]), ?_⟩
  have h := (Subgroup.zpowers x).card_mul_index
  rw [hcardx, CFSG.Sporadic.Schreier.m24_card] at h
  rw [← h, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos] at hpi
  exact hpi

theorem inspC31SporadicAt_m24 :
    CFSG.Quasithin.InspC31SporadicAt .M24 := by
  intro A _ _ S M₀ R M V hSn hSs hCS hM₀S hper _ _ hR2 hRM hMN hM₀R hsyl hVM₀ hVne hV hcomm hVc
    _ hNR _
  have h : Setup S M₀ R M V :=
    ⟨hSn, hSs, hper, hR2, hRM, hMN, hM₀R, hsyl, hVM₀, hVne, hV, hcomm, hVc, hNR⟩
  obtain ⟨e⟩ := id hSs
  let e' : ↥S ≃* G₀ := e
  let ι₀ : G₀ →* A := S.subtype.comp e'.symm.toMonoidHom
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective.comp e'.symm.injective
  have hι₀S : ι₀.range = S := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩; exact (e'.symm g).2
    · intro hx; exact ⟨e' ⟨x, hx⟩, by simp [ι₀]⟩
  have hA : Nat.card A ≤ Nat.card S :=
    calc Nat.card A ≤ Nat.card (MulAut ↥S) := card_le_card_mulAut hSn hCS
      _ = Nat.card (MulAut G₀) := Nat.card_congr (MulAut.congr e').toEquiv
      _ ≤ Nat.card G₀ := CFSG.Sporadic.Schreier.m24_mulAut_card
      _ = Nat.card S := by rw [Nat.card_congr e'.toEquiv]
  have hStop : S = ⊤ :=
    Subgroup.eq_top_of_card_eq S (le_antisymm (Subgroup.card_le_card_group S) hA)
  have hι : Iso ι₀ := ⟨hι₀, hι₀S.trans hStop⟩
  have hne : ⁅V, M₀⁆ ≠ ⊥ := by rw [hcomm]; exact hVne
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm hper h.hM₀V hne
  have hy1 : y ≠ 1 := fun h1 => hyt (by rw [h1, one_mul, inv_one, mul_one])
  have hyR : y ∉ R := not_mem_of_odd hR2 hp hp5 ⟨k, hyk⟩ hy1
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := fun j => by
    have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.hM₀V hy) j) t).mp ht
    exact h.V_comm t ht _ hm
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := hV.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  obtain ⟨y₀, rfl⟩ := hι.surj y
  obtain ⟨t₀, rfl⟩ := hι.surj t
  have hyk₀ : y₀ ^ p ^ k = 1 := hι₀ (by rw [map_pow, hyk, map_one])
  have hpd : p ∣ 244823040 := by
    by_contra hpd
    have : y₀ = 1 := eq_one_of_pow_of_not_dvd hp
      (by rwa [CFSG.Sporadic.Schreier.m24_card]) ⟨k, hyk₀⟩
    exact hy1 (by rw [this, map_one])
  have key : ∀ (x : G₀), orderOf x = p → ¬ p ∣ 244823040 / p → ∃ g t₁ : G₀,
      (ι₀.comp (MulAut.conj g).toMonoidHom) x ∈ Subgroup.zpowers (ι₀ y₀) ∧
        x * t₁ * x⁻¹ ≠ t₁ ∧ orderOf t₁ = 2 ∧
        (∀ j : ℕ, t₁ * (x ^ j * t₁ * x⁻¹ ^ j) = x ^ j * t₁ * x⁻¹ ^ j * t₁) ∧
        orbSub (ι₀ y₀) (ι₀ t₀) = (orbSub x t₁).map (ι₀.comp (MulAut.conj g).toMonoidHom) := by
    intro x hx hpi
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hP, hPi⟩ := sylow_of_order hx hpi
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi ⟨k, hyk₀⟩
    set f : G₀ →* A := ι₀.comp (MulAut.conj g).toMonoidHom with hfdef
    have hf : Function.Injective f := hι₀.comp (MulAut.conj g).injective
    have hconj : ∀ z : G₀, f (g⁻¹ * z * g) = ι₀ z := fun z => by
      rw [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    have hfy : f (g⁻¹ * y₀ * g) = ι₀ y₀ := hconj y₀
    have hft : f (g⁻¹ * t₀ * g) = ι₀ t₀ := hconj t₀
    generalize g⁻¹ * y₀ * g = y₁ at hg hfy
    generalize g⁻¹ * t₀ * g = t₁ at hft
    have hy₁1 : y₁ ≠ 1 := fun h1 => hy1 (by rw [← hfy, h1, map_one])
    have hxy : x ∈ Subgroup.zpowers y₁ := mem_zpowers_of_prime hp hx hg hy₁1
    have hmv₁ : y₁ * t₁ * y₁⁻¹ ≠ t₁ := fun h1 => hyt (by
      have := congrArg f h1
      rwa [map_mul, map_mul, map_inv, hfy, hft] at this)
    have hcm₁ : ∀ j : ℕ, t₁ * (y₁ ^ j * t₁ * y₁⁻¹ ^ j) = y₁ ^ j * t₁ * y₁⁻¹ ^ j * t₁ :=
      fun j => hf (by
        simp only [map_mul, map_pow, map_inv, hfy, hft]
        exact hcommA j)
    obtain ⟨hmv, hcm⟩ := bad_of_zpowers hg hxy hmv₁ hcm₁
    refine ⟨g, t₁, ?_, hmv, ?_, hcm, ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxy
      rw [map_zpow, hfy]
      exact Subgroup.zpow_mem_zpowers _ _
    · rw [← ht2, ← hft, orderOf_injective f hf]
    · rw [← hfy, ← hft, ← orbSub_map, orbSub_eq_of_zpowers hg hxy]
  rcases prime_dvd_m24 hp hp5 hpd with rfl | rfl | rfl | rfl
  ·
    obtain ⟨g, t₁, -, hmv, hord, hcm, hU⟩ := key x5 orderOf_x5 (by norm_num)
    have hf := hι.conj g
    rcases orbSub_cases5 hord hmv (fun j _ => hcm j) with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
    · exact case_s32 h (hf.conj c) hy ht ⟨k, hyk⟩ hy1 (by rw [hU, hc, Subgroup.map_map])
    · exact case_s16 h (hf.conj c) hy ht ⟨k, hyk⟩ hy1 (by rw [hU, hc, Subgroup.map_map])
    · exact case_o h (hf.conj c) hy ht hyR (by rw [hU, hc, Subgroup.map_map])
  ·
    obtain ⟨g, t₁, hx7, hmv, hord, hcm, hU⟩ := key x7 orderOf_x7 (by norm_num)
    have hf := hι.conj g
    rcases orbSub_cases7 hord hmv (fun j _ => hcm j) with
      ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | hc | hc | hc
    · exact (case_u4 h (hf.conj c) hy ht (by rw [hU, hc, Subgroup.map_map])).elim
    · exact (case_r2 h (hf.conj c) hy ht (by rw [hU, hc, Subgroup.map_map])).elim
    · exact case_o h (hf.conj c) hy ht hyR (by rw [hU, hc, Subgroup.map_map])
    · exact (case_u6 h (hf.conj c) hy ht (by rw [hU, hc, Subgroup.map_map])).elim
    · exact case_frame h hf hy ht ⟨k, hyk⟩ hy1 hyR hx7
        (fun hvC hvU hW hW2 => frame_cases12 hvC hvU hW hW2) (by rw [hU, hc])
    · exact case_frame h hf hy ht ⟨k, hyk⟩ hy1 hyR hx7
        (fun hvC hvU hW hW2 => frame_cases17 hvC hvU hW hW2) (by rw [hU, hc])
    · exact case_frame h hf hy ht ⟨k, hyk⟩ hy1 hyR hx7
        (fun hvC hvU hW hW2 => frame_cases18 hvC hvU hW hW2) (by rw [hU, hc])
  ·
    obtain ⟨g, t₁, -, hmv, hord, hcm, -⟩ := key x11 orderOf_x11 (by norm_num)
    exact (not_bad11 hord hmv fun j _ => hcm j).elim
  ·
    obtain ⟨g, t₁, -, hmv, hord, hcm, -⟩ := key x23 orderOf_x23 (by norm_num)
    exact (not_bad23 hord hmv fun j _ => hcm j).elim

end CFSG.Quasithin.KGC31.M24

end
