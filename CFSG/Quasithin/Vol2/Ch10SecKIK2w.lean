module

public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {Γ : Type} [Group Γ] {J L V₁ : Subgroup Γ}

theorem inf_centralizer_V₁ (hLN : L ≤ Subgroup.normalizer (V₁ : Set Γ))
    (hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ))
    (hLs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLV : ¬ L ≤ Subgroup.centralizer (V₁ : Set Γ)) :
    L ⊓ Subgroup.centralizer (V₁ : Set Γ) = pCoreOf 2 L := by
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hO2L)
  set K := (L ⊓ Subgroup.centralizer (V₁ : Set Γ)).subgroupOf L with hK
  have hKn : K.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [hK, Subgroup.mem_subgroupOf] at hk ⊢
    refine ⟨L.mul_mem (L.mul_mem g.2 hk.1) (L.inv_mem g.2), ?_⟩
    have hmem : (g : Γ) * (k : Γ) * (g : Γ)⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hj' : (g : Γ)⁻¹ ∈ Subgroup.normalizer (V₁ : Set Γ) := Subgroup.inv_mem _ (hLN g.2)
      have hv' : (g : Γ)⁻¹ * v * (g : Γ)⁻¹⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp hj' v).mp hv
      rw [inv_inv] at hv'
      have hc := Subgroup.mem_centralizer_iff.mp hk.2 _ hv'
      calc v * ((g : Γ) * (k : Γ) * (g : Γ)⁻¹)
          = (g : Γ) * ((g : Γ)⁻¹ * v * g * k) * (g : Γ)⁻¹ := by group
        _ = (g : Γ) * (k * ((g : Γ)⁻¹ * v * g)) * (g : Γ)⁻¹ := by rw [hc]
        _ = (g : Γ) * (k : Γ) * (g : Γ)⁻¹ * v := by group
    simpa using hmem
  have := hKn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
  · intro x hx
    have hxK : (⟨x, hx.1⟩ : ↥L) ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf]
      exact hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨x, hx.1⟩ ∈
        K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := ⟨_, hxK, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (C1Pack.coe_mem_pCoreOf_iff L ⟨x, hx.1⟩).mpr h1
  · exfalso
    apply hLV
    intro l hl
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) ⟨l, hl⟩ ∈
        K.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by rw [h]; trivial
    obtain ⟨k, hk, hkl⟩ := h1
    have h2 : k⁻¹ * ⟨l, hl⟩ ∈ CFSG.pCore 2 ↥L := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
      exact hkl
    have h3 : ((k⁻¹ * ⟨l, hl⟩ : ↥L) : Γ) ∈ Subgroup.centralizer (V₁ : Set Γ) :=
      hO2L ((C1Pack.coe_mem_pCoreOf_iff L _).mpr h2)
    have h4 : (k : Γ) ∈ Subgroup.centralizer (V₁ : Set Γ) := (Subgroup.mem_subgroupOf.mp hk).2
    have e : l = (k : Γ) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : Γ) := by simp
    rw [e]
    exact Subgroup.mul_mem _ h4 h3

theorem exists_torus_of_scalar [Finite Γ] (hV₁ : IsElemAbelian 2 V₁) {n : ℕ} (hn : 1 ≤ n)
    (hLN : L ≤ Subgroup.normalizer (V₁ : Set Γ))
    (hNJ : J ⊓ Subgroup.normalizer (V₁ : Set Γ) ≤ Subgroup.normalizer (L : Set Γ))
    (hO2L : pCoreOf 2 L ≤ Subgroup.centralizer (V₁ : Set Γ))
    (hLs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hLV : ¬ L ≤ Subgroup.centralizer (V₁ : Set Γ)) {y : Γ}
    (hy : y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ))
    (hyV : y ∉ Subgroup.centralizer (V₁ : Set Γ))
    (hyL : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ))
    (hyq : y ^ (2 ^ n - 1) ∈ Subgroup.centralizer (V₁ : Set Γ)) :
    ∃ x ∈ J ⊓ Subgroup.normalizer (L : Set Γ), Odd (orderOf x) ∧
      (∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∣ 2 ^ n - 1) ∧
      (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) ∧
      x ∉ Subgroup.centralizer (V₁ : Set Γ) := by
  set ψ := convI hV₁ ⟨y, hy.2⟩ with hψ
  have hpow : ∀ k : ℕ, convI hV₁ ⟨y ^ k, Subgroup.pow_mem _ hy.2 k⟩ = ψ ^ k := fun k => by
    rw [hψ, ← map_pow]
    rfl
  have ha : orderOf ψ ∣ 2 ^ n - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← hpow]
    exact (convI_eq_one_iff hV₁ _).2 hyq
  have ha1 : orderOf ψ ≠ 1 := fun h => hyV ((convI_eq_one_iff hV₁ _).1 (orderOf_eq_one_iff.1 h))
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  have hpm : p ∣ 2 ^ n - 1 := hpa.trans ha
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : Odd (2 ^ n - 1) := CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    exact (Nat.not_even_iff_odd.2 this) (even_iff_two_dvd.2 hpm)
  have ho : orderOf y ≠ 0 := (orderOf_pos y).ne'
  set k := ordCompl[p] (orderOf y) with hk
  have hk0 : k ≠ 0 := (Nat.ordCompl_pos p ho).ne'
  refine ⟨y ^ k, ⟨J.pow_mem hy.1 k, hNJ ⟨J.pow_mem hy.1 k, Subgroup.pow_mem _ hy.2 k⟩⟩, ?_, ?_,
    ?_, ?_⟩
  · rw [orderOf_pow_of_dvd hk0 (Nat.ordCompl_dvd _ p),
      Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hk0)
        (Nat.ordProj_mul_ordCompl_eq_self _ p).symm]
    exact (hp.odd_of_ne_two hp2).pow
  · intro q hq hqd
    rw [orderOf_pow_of_dvd hk0 (Nat.ordCompl_dvd _ p),
      Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hk0)
        (Nat.ordProj_mul_ordCompl_eq_self _ p).symm] at hqd
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hqd)]
    exact hpm
  · intro l hl
    have hxN : y ^ k ∈ Subgroup.normalizer (L : Set Γ) :=
      hNJ ⟨J.pow_mem hy.1 k, Subgroup.pow_mem _ hy.2 k⟩
    have hmemL : y ^ k * l * (y ^ k)⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN l).mp hl) (L.inv_mem hl)
    rw [← inf_centralizer_V₁ hLN hO2L hLs hLV]
    refine ⟨hmemL, ?_⟩
    have hc : Commute ψ (convI hV₁ ⟨l, hLN hl⟩) := by
      have h1 := (convI_eq_one_iff hV₁ ⟨y * l * y⁻¹ * l⁻¹, Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy.2 (hLN hl)) (Subgroup.inv_mem _ hy.2))
        (Subgroup.inv_mem _ (hLN hl))⟩).2 (hyL l hl)
      have e : (⟨y * l * y⁻¹ * l⁻¹, _⟩ : ↥(Subgroup.normalizer (V₁ : Set Γ))) =
          ⟨y, hy.2⟩ * ⟨l, hLN hl⟩ * ⟨y, hy.2⟩⁻¹ * ⟨l, hLN hl⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hc' := hc.pow_left k
    rw [← hpow] at hc'
    apply (convI_eq_one_iff hV₁ ⟨y ^ k * l * (y ^ k)⁻¹ * l⁻¹, Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hy.2 k) (hLN hl))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ hy.2 k))) (Subgroup.inv_mem _ (hLN hl))⟩).1
    have e : (⟨y ^ k * l * (y ^ k)⁻¹ * l⁻¹, _⟩ : ↥(Subgroup.normalizer (V₁ : Set Γ))) =
        ⟨y ^ k, Subgroup.pow_mem _ hy.2 k⟩ * ⟨l, hLN hl⟩ * ⟨y ^ k, Subgroup.pow_mem _ hy.2 k⟩⁻¹ *
          ⟨l, hLN hl⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc'.eq, mul_inv_cancel_right,
      mul_inv_cancel]
  · intro hx
    have h1 : ψ ^ k = 1 := by
      rw [← hpow]
      exact (convI_eq_one_iff hV₁ _).2 hx
    exact Nat.not_dvd_ordCompl hp ho (hpa.trans (orderOf_dvd_of_pow_eq_one h1))

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
