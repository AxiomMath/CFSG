module

public import CFSG.Quasithin.Vol2.KGFactC31M23Mod

public section

namespace CFSG.Quasithin.KGC31.M23

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

theorem prime_dvd_m23 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 10200960) :
    p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 * 23 := by norm_num; exact h
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
    (hx : orderOf x = p) (hpi : ¬ p ∣ 10200960 / p) :
    IsPGroup p (Subgroup.zpowers x) ∧ ¬ p ∣ (Subgroup.zpowers x).index := by
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  refine ⟨IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one]), ?_⟩
  have h := (Subgroup.zpowers x).card_mul_index
  rw [hcardx, CFSG.Sporadic.Schreier.m23_card] at h
  rw [← h, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos] at hpi
  exact hpi

theorem inspC31SporadicAt_m23 :
    CFSG.Quasithin.InspC31SporadicAt .M23 := by
  intro A _ _ S M₀ R M V hSn hSs hCS hM₀S hper _ _ hR2 hRM hMN hM₀R hsyl hVM₀ hVne hV hcomm hVc
    _ hNR _
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
      _ ≤ Nat.card G₀ := CFSG.Sporadic.Schreier.m23_mulAut_card
      _ = Nat.card S := by rw [Nat.card_congr e'.toEquiv]
  have hA2 : Nat.card A ≤ 2 * Nat.card S := by omega
  have hne : ⁅V, M₀⁆ ≠ ⊥ := by rw [hcomm]; exact hVne
  have hM₀V := le_normalizer_of_comm hcomm
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm hper hM₀V hne
  obtain ⟨hVO, hOR, hRC, -⟩ := orb_facts hR2 hRM hMN hM₀R hsyl hVM₀ hV hcomm hVc hNR
  set y₀ : G₀ := e' ⟨y, hM₀S hy⟩ with hy₀def
  set t₀ : G₀ := e' ⟨t, hM₀S (hVM₀ ht)⟩ with ht₀def
  have hy₀ : ι₀ y₀ = y := by simp [ι₀, y₀]
  have ht₀ : ι₀ t₀ = t := by simp [ι₀, t₀]
  have hyk₀ : y₀ ^ p ^ k = 1 := hι₀ (by rw [map_pow, hy₀, hyk, map_one])
  have hcommA : ∀ j : ℕ, t * (y ^ j * t * y⁻¹ ^ j) = y ^ j * t * y⁻¹ ^ j * t := fun j => by
    have hm : y ^ j * t * y⁻¹ ^ j ∈ V := by
      rw [inv_pow]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (hM₀V hy) j) t).mp ht
    have := hV.1.is_comm.comm ⟨t, ht⟩ ⟨_, hm⟩
    simpa using congrArg Subtype.val this
  have ht2 : orderOf t = 2 := by
    apply orderOf_eq_prime
    · rw [sq]
      have := hV.2 t ht
      rwa [sq] at this
    · intro h1
      apply hyt
      rw [h1, mul_one, mul_inv_cancel]
  have hpd : p ∣ 10200960 := by
    by_contra hpd
    have : y₀ = 1 := eq_one_of_pow_of_not_dvd hp
      (by rwa [CFSG.Sporadic.Schreier.m23_card]) ⟨k, hyk₀⟩
    apply hyt
    rw [← hy₀, this, map_one, one_mul, inv_one, mul_one]
  have key : ∀ (x : G₀), orderOf x = p → ¬ p ∣ 10200960 / p → ∃ (g y₁ t₁ : G₀),
      y₁ ∈ Subgroup.zpowers x ∧ y₁ * t₁ * y₁⁻¹ ≠ t₁ ∧ orderOf t₁ = 2 ∧
        (∀ j : ℕ, t₁ * (y₁ ^ j * t₁ * y₁⁻¹ ^ j) = y₁ ^ j * t₁ * y₁⁻¹ ^ j * t₁) ∧
        orbSub y t = (orbSub y₁ t₁).map (ι₀.comp (MulAut.conj g).toMonoidHom) := by
    intro x hx hpi
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨hP, hPi⟩ := sylow_of_order hx hpi
    obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi ⟨k, hyk₀⟩
    set f : G₀ →* A := ι₀.comp (MulAut.conj g).toMonoidHom with hfdef
    have hf : Function.Injective f := hι₀.comp (MulAut.conj g).injective
    have hconj : ∀ z : G₀, f (g⁻¹ * z * g) = ι₀ z := fun z => by
      rw [hfdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    have hfy : f (g⁻¹ * y₀ * g) = y := by rw [hconj, hy₀]
    have hft : f (g⁻¹ * t₀ * g) = t := by rw [hconj, ht₀]
    generalize g⁻¹ * y₀ * g = y₁ at hg hfy
    generalize g⁻¹ * t₀ * g = t₁ at hft
    refine ⟨g, y₁, t₁, hg, fun h => hyt ?_, ?_, fun j => hf ?_, ?_⟩
    · have := congrArg f h
      rwa [map_mul, map_mul, map_inv, hfy, hft] at this
    · rw [← ht2, ← hft, orderOf_injective f hf]
    · simp only [map_mul, map_pow, map_inv, hfy, hft]
      exact hcommA j
    · rw [orbSub_map, hfy, hft]
  have hinj : ∀ ψ : G₀ ≃* G₀, Function.Injective (ι₀.comp ψ.toMonoidHom) ∧
      (ι₀.comp ψ.toMonoidHom).range = S := fun ψ => by
    refine ⟨hι₀.comp ψ.injective, ?_⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, ← MonoidHom.range_eq_map,
      hι₀S]
  have hconj : ∀ (g c : G₀) {U : Subgroup G₀}, orbSub y t = ((U.map (MulAut.conj c).toMonoidHom).map
      (ι₀.comp (MulAut.conj g).toMonoidHom)) →
      orbSub y t = U.map (ι₀.comp ((MulAut.conj c).trans (MulAut.conj g)).toMonoidHom) := by
    intro g c U hU
    rw [hU, Subgroup.map_map]
    rfl
  rcases prime_dvd_m23 hp hp5 hpd with rfl | rfl | rfl | rfl
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x5 orderOf_x5 (by norm_num)
    rcases orbSub_cases5 hg hord hmv (fun j _ => hcm j) with ⟨c, h⟩ | ⟨c, h⟩
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj ((MulAut.conj c).trans (MulAut.conj g))
      obtain ⟨hVe, hOe, hMe, -, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_duad (hconj g c hU)
      exact concl_duad hSs hMN hRM _ hi hVe hOe hMe hCe (hVO.trans hOR) hRC
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj ((MulAut.conj c).trans (MulAut.conj g))
      obtain ⟨hVe, hOe, hMe, -, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_w (hconj g c hU)
      exact concl_w hSs hper hMN hcomm _ hi hVe hOe hMe hCe
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x7 orderOf_x7 (by norm_num)
    rcases orbSub_cases7 hg hord hmv (fun j _ => hcm j) with ⟨c, h⟩ | ⟨c, h⟩ | ⟨c, h⟩
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj ((MulAut.conj c).trans (MulAut.conj g))
      obtain ⟨hVe, hOe, hMe, -, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_e8 (hconj g c hU)
      exact concl_e8 hSs hMN hRM hcomm _ hi hVe hOe hMe hCe (hVO.trans hOR) hRC
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj ((MulAut.conj c).trans (MulAut.conj g))
      obtain ⟨hVe, hOe, hMe, -, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_w (hconj g c hU)
      exact concl_w hSs hper hMN hcomm _ hi hVe hOe hMe hCe
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj ((MulAut.conj c).trans (MulAut.conj g))
      obtain ⟨hVe, hOe, hMe, hCe⟩ := config_s hA hR2 hRM hMN hM₀R hsyl hVM₀ hV hcomm hVc hNR
        hy ht hyt _ hi hr (hconj g c hU)
      exact concl_w hSs hper hMN hcomm _ hi hVe hOe hMe hCe
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, -⟩ := key x11 orderOf_x11 (by norm_num)
    exact (not_bad11 hg hord hmv fun j _ => hcm j).elim
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, -⟩ := key x23 orderOf_x23 (by norm_num)
    exact (not_bad23 hg hord hmv fun j _ => hcm j).elim

end CFSG.Quasithin.KGC31.M23

end
