module

public import CFSG.Sporadic.SuzRecog.LocalRNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification

variable {G : Type} [Group G] {H : Type*} [Group H]

structure SuzLocalR (z : G) (σ : ↥(centralizer ({z} : Set G)) ≃* H) (l : H) (T : Subgroup H)
    (A R : Subgroup G) : Prop where
  comp : Comp z A R
  not_isConj : ∀ r ∈ R, ¬ IsConj r z
  isConj_l : ∀ r (hr : r ∈ R), r ≠ 1 → IsConj (σ ⟨r, comp.R_le_M hr⟩) l
  sylow : ∀ r ∈ R, r ≠ 1 →
    IsSylowOf 2 (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G))
        (centralizer ({r} : Set G)) ∧
      Nat.card (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) : Subgroup G) = 512
  center_eq_bot : center A = ⊥
  equivS : Nonempty (↥A ≃* PSL3Four.S)
  centralizer_inf : ∀ r ∈ R, r ≠ 1 → centralizer ({r} : Set G) ⊓ centralizer (A : Set G) = R
  inf_R : A ⊓ R = ⊥
  card_centralizer : ∀ r ∈ R, r ≠ 1 → Nat.card (centralizer ({r} : Set G)) = 161280
  relIndex : ∀ r ∈ R, r ≠ 1 → (A ⊔ R).relIndex (centralizer ({r} : Set G)) = 2
  tau : ∀ r (hr : r ∈ R), r ≠ 1 →
    ∃ σ' : ↥(centralizer ({z} : Set G)) ≃* H, σ' ⟨r, comp.R_le_M hr⟩ = l ∧
      (∀ t, IsConj (σ' t) (σ t)) ∧
      trS σ' (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) =
        centralizer ({l} : Set H) ∧
      trS σ' (A ⊓ centralizer ({z} : Set G)) = T ∧
      trS σ' ((A ⊓ centralizer ({z} : Set G)) ⊔ R) = T ⊔ locC l T ∧
      ∃ τ : ↥(centralizer ({z} : Set G)),
        (τ : G) ∈ centralizer ({r} : Set G) ∧ (τ : G) * τ = 1 ∧ (τ : G) ∉ A ⊔ R ∧
        centralizer ({r} : Set G) = (A ⊔ R) ⊔ zpowers (τ : G) ∧
        σ' τ ∈ centralizer ({l} : Set H) ∧ σ' τ ∉ T ⊔ locC l T ∧
        (∃ s ∈ R, s ≠ 1 ∧ s ≠ r ∧ (τ : G) * s * (τ : G)⁻¹ = r * s) ∧
        (∃ E₁ E₂ : Subgroup G, E₁ ≤ A ⊓ centralizer ({z} : Set G) ∧
          E₂ ≤ A ⊓ centralizer ({z} : Set G) ∧ IsElemAbelian 2 E₁ ∧ IsElemAbelian 2 E₂ ∧
          Nat.card E₁ = 16 ∧ Nat.card E₂ = 16 ∧ E₁ ≠ E₂ ∧
          (∀ E : Subgroup G, E ≤ A ⊓ centralizer ({z} : Set G) → IsElemAbelian 2 E →
            Nat.card E = 16 → E = E₁ ∨ E = E₂) ∧
          E₁.map (MulAut.conj (τ : G)).toMonoidHom = E₂) ∧
        normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ zpowers (τ : G)
  rho : ∃ ρ ∈ centralizer (A : Set G) ⊓ centralizer ({z} : Set G), orderOf ρ = 3 ∧
    ρ ∈ normalizer (R : Set G) ∧ centralizer (A : Set G) = R ⊔ zpowers ρ ∧
    Nat.card (centralizer (A : Set G)) = 12
  normalizer_eq : normalizer (R : Set G) = normalizer (A : Set G)
  card_normalizer : Nat.card (normalizer (A : Set G)) = 483840

variable [Finite G]

theorem suzLocalR_of {z : G} (hz : orderOf z = 2) {σ : ↥(centralizer ({z} : Set G)) ≃* H}
    {l : H} {T : Subgroup H} {A R : Subgroup G} (hc : Comp z A R)
    (hM : Nat.card (centralizer ({z} : Set G)) = 3317760) (hH : NonCentralSylow z)
    (hiff : ∀ t : ↥(centralizer ({z} : Set G)), orderOf t = 2 →
      (¬ IsConj (t : G) z ↔ IsConj (σ t) l))
    (hMF : LocModel l T) : SuzLocalR z σ l T A R := by
  have hZ := hc.center_eq_bot hM hH
  have hl : ∀ r (hr : r ∈ R), r ≠ 1 → IsConj (σ ⟨r, hc.R_le_M hr⟩) l := fun r hr hr1 =>
    (hiff ⟨r, hc.R_le_M hr⟩ (by rw [Subgroup.orderOf_mk]; exact hc.orderOf_eq_two hr hr1)).1
      (hc.not_isConj hM hr)
  have hnorm : ∀ r (hr : r ∈ R), r ≠ 1 →
      ∃ σ' : ↥(centralizer ({z} : Set G)) ≃* H, σ' ⟨r, hc.R_le_M hr⟩ = l ∧
        (∀ t, IsConj (σ' t) (σ t)) ∧
        ∀ t : ↥(centralizer ({z} : Set G)), orderOf t = 2 →
          (¬ IsConj (t : G) z ↔ IsConj (σ' t) l) := fun r hr hr1 => by
    obtain ⟨σ', h1, h2⟩ := exists_normalize σ ⟨r, hc.R_le_M hr⟩ (hl r hr hr1)
    exact ⟨σ', h1, h2, fun t ht => (hiff t ht).trans ⟨fun h => (h2 t).trans h,
      fun h => (h2 t).symm.trans h⟩⟩
  obtain ⟨r₀, hr₀, hr₀1⟩ := hc.exists_ne_one
  obtain ⟨σ₀, hσ₀, -, hiff₀⟩ := hnorm r₀ hr₀ hr₀1
  obtain ⟨ρ, hρ, hρ3, hρR, hρr, hCA, h12⟩ :=
    hc.exists_rho hz hM hH hiff₀ hMF hr₀ hr₀1 hσ₀
  obtain ⟨τ₀, hτ₀r, hτ₀2, hτ₀AR, hCr₀, -, -, -, -⟩ :=
    exists_tau hc hz hM hH hiff₀ hr₀ hr₀1 hσ₀ hMF
  obtain ⟨hNRA, -, hcardN⟩ := hc.normalizer_eq hz hM hH hr₀ hr₀1 hρ hρ3 hρR hρr hCA h12
    hτ₀r hτ₀2 hτ₀AR hCr₀
  refine ⟨hc, fun r hr => hc.not_isConj hM hr, hl, fun r hr hr1 => hc.isSylowOf_inf hM hH hr hr1,
    hZ, ⟨hc.equivS hZ⟩, fun r hr hr1 => hc.centralizer_inf_eq hM hH hr hr1, hc.inf_R_eq_bot hZ,
    fun r hr hr1 => hc.card_centralizer hM hH hz hr hr1,
    fun r hr hr1 => hc.relIndex_sup_R hM hH hz hr hr1, fun r hr hr1 => ?_,
    ⟨ρ, hρ, hρ3, hρR, hCA, h12⟩, hNRA, hcardN⟩
  obtain ⟨σ', hσ', hconj, hiff'⟩ := hnorm r hr hr1
  obtain ⟨τ, hτr, hτ2, hτAR, hCr, hτV, hτout, hs, hE⟩ :=
    exists_tau hc hz hM hH hiff' hr hr1 hσ' hMF
  obtain ⟨-, hNA, -⟩ := hc.normalizer_eq hz hM hH hr hr1 hρ hρ3 hρR
    (fun h => by
      have hρV : ρ ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) :=
        ⟨mem_centralizer_singleton_iff.2 (by
          calc ρ * r = ρ * r * ρ⁻¹ * ρ := by group
            _ = r * ρ := by rw [h]), hρ.2⟩
      obtain ⟨k, hk⟩ := hc.isPGroup_inf hM hH hr hr1 ⟨_, hρV⟩
      have hdvd : orderOf ρ ∣ 2 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        have := congrArg Subtype.val hk
        simpa using this
      rw [hρ3] at hdvd
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
      omega) hCA h12 hτr hτ2 hτAR hCr
  exact ⟨σ', hσ', hconj, trS_V hc hr hσ', trS_T hc hz hM hH hiff' hr hσ' hMF,
    trS_TR hc hz hM hH hiff' hr hσ' hMF, τ, hτr, hτ2, hτAR, hCr, hτV, hτout, hs, hE, hNA⟩

theorem exists_suzLocalR
    (S : CFSG.LargeExtraspecial.Setting G) (σ : S.M ≃* CFSG.Sporadic.SuzOddCore.invE 1)
    {l : CFSG.Sporadic.SuzOddCore.invE 1} {T : Subgroup (CFSG.Sporadic.SuzOddCore.invE 1)}
    (hL34 : SuzL34Data S.z) (hH : NonCentralSylow S.z)
    (hiff : ∀ t : S.M, orderOf t = 2 → (¬ IsConj (t : G) S.z ↔ IsConj (σ t) l))
    (hMF : LocModel l T) : ∃ A R : Subgroup G, SuzLocalR S.z σ l T A R := by
  obtain ⟨A, R, hc⟩ := exists_comp hL34
  exact ⟨A, R, suzLocalR_of S.orderOf_z hc (card_M_of_mulEquiv S σ) hH hiff hMF⟩

end CFSG.Sporadic.SuzRecog.LocalR
