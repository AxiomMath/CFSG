module

public import CFSG.Quasithin.Vol2.KGFactC31M22Mod
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22

public section

namespace CFSG.Quasithin.KGC31.M22

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31

theorem prime_dvd_m22 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 443520) :
    p = 5 ∨ p = 7 ∨ p = 11 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1))

theorem sylow_of_order {x : G₀} {p : ℕ} [Fact p.Prime]
    (hx : orderOf x = p) (hpi : ¬ p ∣ 443520 / p) :
    IsPGroup p (Subgroup.zpowers x) ∧ ¬ p ∣ (Subgroup.zpowers x).index := by
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hx]
  refine ⟨IsPGroup.of_card (n := 1) (by rw [hcardx, pow_one]), ?_⟩
  have h := (Subgroup.zpowers x).card_mul_index
  rw [hcardx, CFSG.Sporadic.Mathieu.card_M22] at h
  rw [← h, Nat.mul_div_cancel_left _ (Fact.out : p.Prime).pos] at hpi
  exact hpi

theorem inspC31SporadicAt_m22 :
    CFSG.Quasithin.InspC31SporadicAt .M22 := by
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
  have hcS : Subgroup.center ↥S = ⊥ := by
    refine eq_bot_iff.mpr fun z hz => ?_
    have hz' : e' z ∈ Subgroup.center G₀ := Subgroup.mem_center_iff.mpr fun g => by
      obtain ⟨g', rfl⟩ := e'.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    rw [CFSG.Sporadic.Schreier.m22_center_eq_bot', Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e'.injective (hz'.trans (map_one e').symm)
  have hA2 : Nat.card A ≤ 2 * Nat.card S :=
    calc Nat.card A ≤ Nat.card (MulAut ↥S) := card_le_card_mulAut hSn hCS
      _ = Nat.card (MulAut G₀) := Nat.card_congr (MulAut.congr e').toEquiv
      _ ≤ 2 * Nat.card G₀ := CFSG.Sporadic.Schreier.m22_mulAut_card
      _ = 2 * Nat.card S := by rw [Nat.card_congr e'.toEquiv]
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
  have hpd : p ∣ 443520 := by
    by_contra hpd
    have : y₀ = 1 := eq_one_of_pow_of_not_dvd hp
      (by rwa [CFSG.Sporadic.Mathieu.card_M22]) ⟨k, hyk₀⟩
    apply hyt
    rw [← hy₀, this, map_one, one_mul, inv_one, mul_one]
  have key : ∀ (x : G₀), orderOf x = p → ¬ p ∣ 443520 / p → ∃ (g y₁ t₁ : G₀),
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
  rcases prime_dvd_m22 hp hp5 hpd with rfl | rfl | rfl
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x5 orderOf_x5 (by norm_num)
    rcases orbSub_cases5 hg hord hmv (fun j _ => hcm j) with h | h | h
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj (MulAut.conj g)
      obtain ⟨hVe, hOe, hMe, hRe, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_duad hU
      exact concl_duad hSs hcS hM₀S hMN hRM hcomm _ hi hVe hOe hMe hCe (hVO.trans hOR) hRC
    · rw [h] at hU
      obtain ⟨hi, hr⟩ := hinj (MulAut.conj g)
      obtain ⟨hVe, hOe, hMe, hRe, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_hex hU
      exact concl_hex hSs hcS hM₀S hper hMN hcomm _ hi hVe hOe hMe hCe
    · rw [h, Subgroup.map_map] at hU
      obtain ⟨hi, hr⟩ := hinj ((MulAut.conj cHex).trans (MulAut.conj g))
      have hU' : orbSub y t = (eSub basis_hex).map
          (ι₀.comp ((MulAut.conj cHex).trans (MulAut.conj g)).toMonoidHom) := by
        rw [hU]; rfl
      obtain ⟨hVe, hOe, hMe, hRe, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
        hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_hex hU'
      exact concl_hex hSs hcS hM₀S hper hMN hcomm _ hi hVe hOe hMe hCe
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, hU⟩ := key x7 orderOf_x7 (by norm_num)
    rw [orbSub_cases7 hg hord hmv (fun j _ => hcm j)] at hU
    obtain ⟨hi, hr⟩ := hinj (MulAut.conj g)
    obtain ⟨hVe, hOe, hMe, hRe, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
      hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_e8 hU
    exact concl_e8 hSs hcS hM₀S hMN hRM hcomm _ hi hVe hOe hMe hCe (hVO.trans hOR) hRC
  ·
    obtain ⟨g, y₁, t₁, hg, hmv, hord, hcm, -⟩ := key x11 orderOf_x11 (by norm_num)
    exact (not_bad11 hg hord hmv fun j _ => hcm j).elim

end CFSG.Quasithin.KGC31.M22

end
