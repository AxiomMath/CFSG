module

public import CFSG.LieType.Steinberg.CentralExt.SUThree
public import CFSG.RankThree.CentralLift.LargeLift
public import CFSG.CharacterTheory.Semidihedral.CentralTransferSplitting
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.RankThree.CentralLiftU

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.CentralLift

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

local notation "σ₀" => unitaryInvolution K ℓ f

theorem exists_section_SUid_three_of_coprime (hK : Nat.card K = (ℓ ^ f) ^ 2) (hℓ2 : ℓ ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    (hpq : ¬ p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1)
    {E : Type*} [Group E] [Finite E] {π : E →* SUid (unitaryInvolution K ℓ f) 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hpk : IsPGroup p π.ker) :
    ∃ s : SUid (unitaryInvolution K ℓ f) 3 →* E, ∀ x, π (s x) = x := by
  have hσ : ∀ c, σ₀ (σ₀ c) = c := unitaryInvolution_involutive hK
  have hk : ringChar (fixedSubfield K ℓ f) ≠ 2 := by
    rw [ringChar_fixedSubfield]
    exact hℓ2
  have hπL : IsLargeCentralExt π := ⟨hπ, hcen, ⟨p, hp, hp3, hpk⟩⟩
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  let e : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K ℓ f) ≃* SUid σ₀ 2 :=
    (hypEquiv hζ0 hζ).trans (conjEquiv P hP)
  let α₂ := (embSUid σ₀ 2).comp e.toMonoidHom
  have hα₂ : Function.Injective α₂ := (embSUid_injective σ₀ 2).comp e.injective
  set L := α₂.range
  have hL : ∀ x, x ∈ L ↔ ∃ A, embSUid σ₀ 2 A = x := by
    intro x
    constructor
    · rintro ⟨A, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨A, rfl⟩
      exact ⟨e.symm A, by simp [α₂]⟩
  let ψ := MonoidHom.ofInjective hα₂
  obtain ⟨β₀, hβ₀⟩ := (existsUnique_lift_large hk hπL α₂).exists
  let β : L →* E := β₀.comp ψ.symm.toMonoidHom
  have hβ : ∀ x, π (β x) = x := by
    intro x
    have h1 := DFunLike.congr_fun hβ₀ (ψ.symm x)
    have h2' := MonoidHom.ofInjective_apply hα₂ (x := ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at h2'
    rw [MonoidHom.comp_apply] at h1
    change π (β₀ (ψ.symm x)) = x
    rw [h1, ← h2']
  have huniq : ∀ β₁ β₂ : L →* E, π.comp β₁ = π.comp β₂ → β₁ = β₂ := by
    intro β₁ β₂ h
    have h' : β₁.comp ψ.toMonoidHom = β₂.comp ψ.toMonoidHom :=
      (existsUnique_lift_large hk hπL (π.comp (β₁.comp ψ.toMonoidHom))).unique rfl
        (by rw [← MonoidHom.comp_assoc, ← h, MonoidHom.comp_assoc])
    ext x
    have := DFunLike.congr_fun h' (ψ.symm x)
    simpa using this
  obtain ⟨l, hl, hlo⟩ := exists_norm_one_orderOf_eq hK
  let u : normOne σ₀ := ⟨l, hl⟩
  set δ := embSUid σ₀ 1 (torusTwo σ₀ u)
  have hδo : orderOf δ = orderOf (torusTwo σ₀ u) :=
    orderOf_injective _ (embSUid_injective σ₀ 1) _
  have hδq : orderOf δ = ℓ ^ f + 1 := by
    rw [hδo, orderOf_torusTwo]
    exact hlo
  obtain ⟨β₁, hβ₁⟩ := (existsUnique_lift_large hk hπL ((embSUid σ₀ 1).comp e.toMonoidHom)).exists
  set δ' := β₁ (e.symm (torusTwo σ₀ u))
  have hδ' : π δ' = δ := by
    have := DFunLike.congr_fun hβ₁ (e.symm (torusTwo σ₀ u))
    simpa using this
  have hord : δ' ^ orderOf δ = 1 := by
    rw [← map_pow, ← map_pow, hδo, pow_orderOf_eq_one, map_one, map_one]
  have hconj : ∀ (v : normOne σ₀) (x : SUid σ₀ 3), x ∈ L →
      embSUid σ₀ 1 (torusTwo σ₀ v) * x * (embSUid σ₀ 1 (torusTwo σ₀ v))⁻¹ ∈ L := by
    intro v x hx
    obtain ⟨A, rfl⟩ := (hL x).1 hx
    obtain ⟨B, hB⟩ := embSUid_one_mul_embSUid_two hσ v A
    rw [hB, mul_inv_cancel_right]
    exact (hL _).2 ⟨B, rfl⟩
  have hδn : δ ∈ Subgroup.normalizer (L : Set (SUid σ₀ 3)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj u x, fun hx => ?_⟩
    have h := hconj u⁻¹ _ hx
    have hinv : embSUid σ₀ 1 (torusTwo σ₀ u⁻¹) = δ⁻¹ := by rw [map_inv, map_inv]
    rwa [hinv, show δ⁻¹ * (δ * x * δ⁻¹) * δ⁻¹⁻¹ = x by group] at h
  have hdisj : ∀ k : ℤ, δ ^ k ∈ L → δ ^ k = 1 := by
    intro k hk'
    obtain ⟨A, hA⟩ := (hL _).1 hk'
    rw [← map_zpow, ← map_zpow] at hA ⊢
    have h22 := congrFun (congrFun (congrArg (fun g : SUid σ₀ 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hA) 2) 2
    simp only [coe_embSUid, coe_torusTwo] at h22
    simp [embPair] at h22
    have hu1 : u ^ k = 1 := Subtype.ext (Units.ext (by
      simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, Subgroup.coe_one, Units.val_one]
      exact h22))
    rw [hu1, map_one, map_one]
  obtain ⟨s, hs⟩ := exists_section_sup_zpowers hβ huniq hδn hdisj hδ' hord
  set q := ℓ ^ f
  have hq2 : 2 ≤ q := (CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hK)
  have hcardG : Nat.card (SUid σ₀ 3) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
    obtain ⟨P₃, hP₃⟩ := exists_wittMatrix hK 3
    rw [← Nat.card_congr (conjEquiv P₃ hP₃).toEquiv, card_SU_three hK]
  have hcardL : Nat.card L = q * (q ^ 2 - 1) := by
    rw [← Nat.card_congr ψ.toEquiv, card_specialLinearGroup_fin_two, card_fixedSubfield hK]
  have hcardM := card_sup_zpowers hδn hdisj
  rw [hcardL, hδq] at hcardM
  have hidx : (L ⊔ Subgroup.zpowers δ).index = q ^ 2 * (q ^ 2 - q + 1) := by
    have h := Subgroup.card_mul_index (L ⊔ Subgroup.zpowers δ)
    rw [hcardM, hcardG] at h
    have hq1 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
    have hq3 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have key : q * (q ^ 2 - 1) * (q + 1) * (q ^ 2 * (q ^ 2 - q + 1)) =
        q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) := by
      zify [hq1, hq3]
      ring
    rw [← key] at h
    have hq4 : 0 < q ^ 2 - 1 := by
      have : 4 ≤ q ^ 2 := by nlinarith
      omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.mul_pos (by omega) hq4) (by omega)) h
  have hcop : Nat.Coprime p (L ⊔ Subgroup.zpowers δ).index := by
    rw [hidx, Nat.Coprime, Nat.Coprime.gcd_eq_one]
    refine Nat.Coprime.mul_right ?_ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpq)
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hdvd => hpℓ ?_
    have hdvd' : p ∣ ℓ ^ (f * 2) := by rwa [pow_mul]
    exact (Nat.prime_dvd_prime_iff_eq hp Fact.out).1 (hp.dvd_of_dvd_pow hdvd')
  exact CFSG.Semidihedral.CentralTransferSplitting.exists_section_of_coprime_index p π hπ hcen
    hpk _ hcop s hs

end CFSG.RankThree.CentralLiftU
