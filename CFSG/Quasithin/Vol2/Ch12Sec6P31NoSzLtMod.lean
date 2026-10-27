module

public import CFSG.Quasithin.H13.A6S13816h

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Quasithin

namespace SzMod

variable {W : Type} [CommGroup W]

theorem trivial_mod_fix [Finite W] (hSzE : SzEnd) {Mp L : Subgroup (MulAut W)} {σ t : MulAut W}
    (hσ3 : ∃ k : ℕ, σ ^ 3 ^ k = 1) (hσMp : ∀ m ∈ Mp, σ * m = m * σ) (hLMp : L ≤ Mp)
    (htL : ∀ h ∈ L, t * h * t⁻¹ ∈ Mp) (htMp : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp)
    (htMp' : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp)
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤) {f : ℕ}
    (hSz : BinaryNaturalSz L (commV L) (commV L ⊓ fixV Mp) f) :
    ∀ w : W, σ w * w⁻¹ ∈ fixV Mp := by
  have hσL : ∀ h ∈ L, σ * h = h * σ := fun h hh => hσMp h (hLMp hh)
  obtain ⟨σ', hσ'⟩ : ∃ σ', σ' = t⁻¹ * σ * t := ⟨_, rfl⟩
  have hσ'3 : ∃ k : ℕ, σ' ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hσ3
    refine ⟨k, ?_⟩
    rw [hσ', show t⁻¹ * σ * t = t⁻¹ * σ * t⁻¹⁻¹ by rw [inv_inv], conj_pow, hk, mul_one,
      mul_inv_cancel]
  have hσ'L : ∀ h ∈ L, σ' * h = h * σ' := by
    intro h hh
    have e := hσMp _ (htL h hh)
    calc σ' * h = t⁻¹ * (σ * (t * h * t⁻¹)) * t := by rw [hσ']; group
      _ = t⁻¹ * ((t * h * t⁻¹) * σ) * t := by rw [e]
      _ = h * σ' := by rw [hσ']; group
  have hσF : ∀ u ∈ fixV Mp, σ u ∈ fixV Mp := fun u hu => map_mem_fixV hσMp hu
  have htF : ∀ u ∈ fixV Mp, t u ∈ fixV Mp := fun u hu => map_mem_fixV_of_conj htMp' hu
  have htF' : ∀ u ∈ fixV Mp, t⁻¹ u ∈ fixV Mp := fun u hu =>
    map_mem_fixV_of_conj (fun m hm => by simpa using htMp m hm) hu
  have hσ'F : ∀ u ∈ fixV Mp, σ' u ∈ fixV Mp := fun u hu => by
    rw [hσ', MulAut.mul_apply, MulAut.mul_apply]
    exact htF' _ (hσF _ (htF u hu))
  have h1 := hSzE W L (commV L) (commV L ⊓ fixV Mp) f hSz σ hσ3
    (fun u hu => map_mem_commV hσL hu) (fun u hu => ⟨map_mem_commV hσL hu.1, hσF u hu.2⟩) hσL
  have h2 := hSzE W L (commV L) (commV L ⊓ fixV Mp) f hSz σ' hσ'3
    (fun u hu => map_mem_commV hσ'L hu) (fun u hu => ⟨map_mem_commV hσ'L hu.1, hσ'F u hu.2⟩)
    hσ'L
  let Q : Subgroup W :=
    { carrier := {w | σ w * w⁻¹ ∈ fixV Mp}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        have e : σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
          rw [map_mul, mul_inv]
          ac_rfl
        show σ (a * b) * (a * b)⁻¹ ∈ fixV Mp
        rw [e]
        exact (fixV Mp).mul_mem ha hb
      inv_mem' := fun {a} ha => by
        have e : σ a⁻¹ * a⁻¹⁻¹ = (σ a * a⁻¹)⁻¹ := by
          rw [map_inv, inv_inv, mul_inv, inv_inv]
        show σ a⁻¹ * a⁻¹⁻¹ ∈ fixV Mp
        rw [e]
        exact (fixV Mp).inv_mem ha }
  have hUQ : commV L ≤ Q := fun u hu => (h1 u hu).2
  have hUtQ : (commV L).map t.toMonoidHom ≤ Q := by
    rintro _ ⟨u, hu, rfl⟩
    have e : σ (t u) = t (σ' u) := by
      rw [hσ', MulAut.mul_apply, MulAut.mul_apply]
      simp
    show σ (t u) * (t u)⁻¹ ∈ fixV Mp
    rw [e, ← map_inv, ← map_mul]
    exact htF _ (h2 u hu).2
  have hFQ : fixV Mp ≤ Q := fun u hu => (fixV Mp).mul_mem (hσF u hu) ((fixV Mp).inv_mem hu)
  have htop : (⊤ : Subgroup W) ≤ Q := by
    rw [hsum.1]
    exact sup_le (sup_le hUQ hUtQ) hFQ
  exact fun w => htop (Subgroup.mem_top w)

theorem false_of_szEnd_grp [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hSzE : SzEnd)
    {Mp L : Subgroup (MulAut W)} {t : MulAut W} {Y : Type*} [Group Y] (ρ : Y →* MulAut W)
    (E : Subgroup Y) [Finite E] (hodd : Odd (Nat.card E))
    (hE3 : ∀ e ∈ E, ∃ k : ℕ, ρ e ^ 3 ^ k = 1) (hfpf : ∀ w : W, (∀ e ∈ E, ρ e w = w) → w = 1)
    (hEMp : ∀ e ∈ E, ∀ m ∈ Mp, ρ e * m = m * ρ e) (hLMp : L ≤ Mp)
    (htL : ∀ h ∈ L, t * h * t⁻¹ ∈ Mp) (htMp : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp)
    (htMp' : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp)
    (hsum : IsSumMod (fixV Mp) (commV L) ((commV L).map t.toMonoidHom) ⊤) {f : ℕ}
    (hSz : BinaryNaturalSz L (commV L) (commV L ⊓ fixV Mp) f) : False := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  have hQ : ∀ e ∈ E, ∀ w : W, ρ e w * w⁻¹ ∈ fixV Mp := fun e he =>
    trivial_mod_fix hSzE (hE3 e he) (hEMp e he) hLMp htL htMp htMp' hsum hSz
  have hall : ∀ w : W, w ∈ fixV Mp := by
    intro w
    obtain ⟨g, hg⟩ : ∃ g : W, g = ∏ e : E, (ρ (e : Y) w * w⁻¹) := ⟨_, rfl⟩
    have hgF : g ∈ fixV Mp := by
      rw [hg]
      exact Subgroup.prod_mem _ fun e _ => hQ e e.2 w
    have hNm : ∏ e : E, ρ (e : Y) w = g * w := by
      have h1 : ∀ e : E, ρ (e : Y) w = (ρ (e : Y) w * w⁻¹) * w := fun e => by
        rw [inv_mul_cancel_right]
      calc ∏ e : E, ρ (e : Y) w = ∏ e : E, ((ρ (e : Y) w * w⁻¹) * w) :=
            Finset.prod_congr rfl fun e _ => h1 e
        _ = (∏ e : E, (ρ (e : Y) w * w⁻¹)) * ∏ _e : E, w := Finset.prod_mul_distrib
        _ = g * w ^ Nat.card E := by
            rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hg]
        _ = g * w := by
            obtain ⟨k, hk⟩ := hodd
            rw [hk, pow_succ, pow_mul, hW w, one_pow, one_mul]
    have hfix : ∀ e' ∈ E, ρ e' (∏ e : E, ρ (e : Y) w) = ∏ e : E, ρ (e : Y) w := by
      intro e' he'
      have h1 : ρ e' (∏ e : E, ρ (e : Y) w) = ∏ e : E, ρ ((⟨e', he'⟩ * e : E) : Y) w := by
        rw [map_prod]
        refine Finset.prod_congr rfl fun e _ => ?_
        simp [map_mul]
      rw [h1]
      exact Fintype.prod_equiv (Equiv.mulLeft (⟨e', he'⟩ : E)) _ _ (fun e => rfl)
    have h1 : ∏ e : E, ρ (e : Y) w = 1 := hfpf _ hfix
    rw [hNm] at h1
    have : w = g⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact (fixV Mp).inv_mem hgF
  exact false_of_binaryNaturalSz_le hSz fun u hu => ⟨hu, hall u⟩

theorem false_of_modFiveIii_grp [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hSzE : SzEnd) {Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W} {n : ℕ}
    {Y : Type*} [Group Y] (ρ : Y →* MulAut W) (E : Subgroup Y) [Finite E]
    (hodd : Odd (Nat.card E)) (hE3 : ∀ e ∈ E, ∃ k : ℕ, ρ e ^ 3 ^ k = 1)
    (hfpf : ∀ w : W, (∀ e ∈ E, ρ e w = w) → w = 1)
    (hEMp : ∀ e ∈ E, ∀ m ∈ Mp, ρ e * m = m * ρ e) (hL : IsSz n ↥L) (hLMp : L ≤ Mp)
    (htL : ∀ h ∈ L, t * h * t⁻¹ ∈ Mp) (htMp : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp)
    (htMp' : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp) (h : ModFiveIii Mp T L V t) : False := by
  obtain ⟨hsum, -, hcase⟩ := h
  have h3 := SzCase.not_three_dvd_of_isSz hL
  obtain ⟨a₀, ha₀, hn⟩ : ∃ a₀, 1 ≤ a₀ ∧ n = 2 * a₀ + 1 := by
    obtain ⟨-, a, ha, -, -, -, hf, -⟩ := hL
    exact ⟨a, ha, hf⟩
  have hn3 : 3 ≤ n := by omega
  have hodd' : Odd n := ⟨a₀, hn⟩
  have h504 := le_card_of_psl2_or_sz hn3 (Or.inr hL)
  have h168 : ¬ IsPSL 3 2 1 ↥L := fun hp => h3 (by
    rw [SBc11.card_of_isPSL_three_two hp]
    norm_num)
  rcases hcase with ⟨⟨hcomm, hmod⟩, -⟩ | hB | hD2 | hD3
  · rcases hmod with ⟨n', hn'⟩ | h31 | ⟨f, hf⟩ | ⟨a, ha1, ha⟩ | h5
    · exact h3 (three_dvd_card_of_natural_sl2 hn')
    · have := card_le_168_of_natural_sl3 h31
      omega
    · rw [← hcomm] at hf
      exact false_of_szEnd_grp hW hSzE ρ E hodd hE3 hfpf hEMp hLMp htL htMp htMp' hsum hf
    · exact orthExcl_of W n hn3 hodd' L V _ (Or.inr hL) ⟨a, ha1, ha⟩
    · have := card_le_sixty_of_alternating_five h5
      omega
  · exact h168 hB.1
  · exact h168 hD2.1
  · obtain ⟨n', hpsl, -⟩ := hD3
    exact h3 (L2Case.three_dvd_card (Or.inl ⟨n', hpsl⟩))

theorem false_of_modFive_grp [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hSzE : SzEnd) {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W} {n : ℕ}
    {Y : Type*} [Group Y] (ρ : Y →* MulAut W) (E : Subgroup Y) [Finite E]
    (hodd : Odd (Nat.card E)) (hE3 : ∀ e ∈ E, ∃ k : ℕ, ρ e ^ 3 ^ k = 1)
    (hfpf : ∀ w : W, (∀ e ∈ E, ρ e w = w) → w = 1)
    (hEMp : ∀ e ∈ E, ∀ m ∈ Mp, ρ e * m = m * ρ e) (hL : IsSz n ↥L)
    (hMp : Mp = L ⊔ conjAutSub t L) (htMp : t ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (h : ModFive M Mp T L V t) : False := by
  have h3 := SzCase.not_three_dvd_of_isSz hL
  have hdvd : Nat.card ↥(autSub L V) ∣ Nat.card ↥L := by
    refine (Subgroup.card_map_dvd _ _).trans ?_
    have e : Nat.card ↥(L.subgroupOf (stabSub V)) = Nat.card ↥(L ⊓ stabSub V) := by
      rw [← Subgroup.card_subtype (stabSub V) (L.subgroupOf (stabSub V)),
        Subgroup.subgroupOf_map_subtype]
    rw [e]
    exact Subgroup.card_dvd_of_le inf_le_left
  have htMp1 : ∀ m ∈ Mp, t * m * t⁻¹ ∈ Mp := fun m hm =>
    (Subgroup.mem_normalizer_iff.mp htMp m).mp hm
  have htMp2 : ∀ m ∈ Mp, t⁻¹ * m * t ∈ Mp := fun m hm => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htMp) m).mp hm
    simpa using this
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hLtMp : conjAutSub t L ≤ Mp := by
    rw [hMp]
    exact le_sup_right
  rcases h with ⟨-, -, n', hpsl, -⟩ | ⟨-, -, hpsl, -⟩ | hiii | hiii
  · exact h3 ((L2Case.three_dvd_card (Or.inl ⟨n', hpsl⟩)).trans hdvd)
  · refine h3 (dvd_trans ?_ hdvd)
    rw [SBc11.card_of_isPSL_three_two hpsl]
    norm_num
  · exact false_of_modFiveIii_grp hW hSzE ρ E hodd hE3 hfpf hEMp hL hLMp
      (fun h hh => hLtMp ⟨h, hh, rfl⟩) htMp1 htMp2 hiii
  · have hL' : IsSz n ↥(conjAutSub t L) :=
      isSz_congr (L.equivMapOfInjective _ (MulAut.conj t).injective) hL
    refine false_of_modFiveIii_grp hW hSzE ρ E hodd hE3 hfpf hEMp hL' hLtMp ?_
      (fun m hm => by simpa using htMp2 m hm) (fun m hm => by simpa using htMp1 m hm) hiii
    rintro _ ⟨h, hh, rfl⟩
    have e : t⁻¹ * (MulAut.conj t).toMonoidHom h * t⁻¹⁻¹ = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    exact hLMp hh

end SzMod

end CFSG.Quasithin.H13.A6
