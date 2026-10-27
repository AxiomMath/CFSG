module

public import CFSG.Quasithin.Vol2.KGFactC31HSMod
public import CFSG.Quasithin.Vol2.KGFactC31HSCases

public section

namespace CFSG.Quasithin.KGC31.HS

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.RankThree.Native

theorem prime_dvd_hs {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 44352000) :
    p = 5 ∨ p = 7 ∨ p = 11 := by
  have h' : p ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hp).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4); omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h2))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1))

theorem inspC31SporadicAt_hs :
    CFSG.Quasithin.InspC31SporadicAt .HS := by
  intro A _ _ S M₀ R M V hSn hSs hCS hM₀S hper _ _ hR2 hRM hMN hM₀R hsyl hVM₀ hVne hV hcomm hVc
    _ hNR _
  obtain ⟨e⟩ := id hSs
  let e' : ↥S ≃* G₀ := e.trans hs100Equiv
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
    rw [center_eq_bot, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e'.injective (hz'.trans (map_one e').symm)
  have hA2 : Nat.card A ≤ 2 * Nat.card S :=
    calc Nat.card A ≤ Nat.card (MulAut ↥S) := card_le_card_mulAut hSn hCS
      _ = Nat.card (MulAut G₀) := Nat.card_congr (MulAut.congr e').toEquiv
      _ ≤ 2 * Nat.card G₀ := card_mulAut_le
      _ = 2 * Nat.card S := by rw [Nat.card_congr e'.toEquiv]
  have hne : ⁅V, M₀⁆ ≠ ⊥ := by rw [hcomm]; exact hVne
  have hM₀V := le_normalizer_of_comm hcomm
  obtain ⟨p, hp, hp5, y, hy, ⟨k, hyk⟩, t, ht, hyt⟩ :=
    exists_pElement_not_comm hper hM₀V hne
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
  have hmove₀ : y₀ * t₀ * y₀⁻¹ ≠ t₀ := fun h => hyt (by
    have := congrArg ι₀ h
    rwa [map_mul, map_mul, map_inv, hy₀, ht₀] at this)
  have ht₀2 : orderOf t₀ = 2 := by rw [← ht2, ← ht₀, orderOf_injective ι₀ hι₀]
  have hcomm₀ : ∀ j : ℕ, t₀ * (y₀ ^ j * t₀ * y₀⁻¹ ^ j) = y₀ ^ j * t₀ * y₀⁻¹ ^ j * t₀ :=
    fun j => hι₀ (by simp only [map_mul, map_pow, map_inv, hy₀, ht₀]; exact hcommA j)
  have horb : orbSub y t = (orbSub y₀ t₀).map ι₀ := by rw [orbSub_map, hy₀, ht₀]
  have hpd : p ∣ 44352000 := by
    by_contra hpd
    have : y₀ = 1 := eq_one_of_pow_of_not_dvd hp (by rwa [card_G₀]) ⟨k, hyk₀⟩
    apply hyt
    rw [← hy₀, this, map_one, one_mul, inv_one, mul_one]
  have hinj : ∀ ψ : G₀ ≃* G₀, Function.Injective (ι₀.comp ψ.toMonoidHom) ∧
      (ι₀.comp ψ.toMonoidHom).range = S := fun ψ => by
    refine ⟨hι₀.comp ψ.injective, ?_⟩
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, ← MonoidHom.range_eq_map,
      hι₀S]
  rcases prime_dvd_hs hp hp5 hpd with rfl | rfl | rfl
  ·
    obtain ⟨s, hs, hU⟩ := orbSub_cases5 ⟨k, hyk₀⟩ ht₀2 hmove₀ hcomm₀
    obtain ⟨hi, hr⟩ := hinj (conjR s hs)
    have hU' : orbSub y t = (eSub basis_u16).map (ι₀.comp (conjR s hs).toMonoidHom) := by
      rw [horb, hU, Subgroup.map_map]
    obtain ⟨hVe, hOe, hMe, -, hCe⟩ := config_of_ref hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl
      hVM₀ hV hcomm hVc hNR hy ht hyt _ hi hr refData_u16 hU'
    exact concl_a6 hSs hcS hM₀S hper hMN hcomm _ hi hVe hOe hMe hCe
  ·
    obtain ⟨s, hs, hU⟩ := orbSub_cases7 ⟨k, hyk₀⟩ ht₀2 hmove₀ hcomm₀
    obtain ⟨hi, hr⟩ := hinj (conjR s hs)
    have hU' : orbSub y t = (eSub basis_u8).map (ι₀.comp (conjR s hs).toMonoidHom) := by
      rw [horb, hU, Subgroup.map_map]
    obtain ⟨hVe, hOe, hMe, hRe⟩ := config_u8 hSn hA2 hM₀S hper hR2 hRM hMN hM₀R hsyl hVM₀ hV
      hcomm hVc hNR hy ht hyt _ hi hr hU'
    exact concl_z4 hSs hcS hM₀S hMN hcomm _ hi hVe hOe hMe hRe
  ·
    exact (not_bad11 ⟨k, hyk₀⟩ ht₀2 hmove₀ hcomm₀).elim

end CFSG.Quasithin.KGC31.HS

end
