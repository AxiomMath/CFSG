module

public import CFSG.Quasithin.EmptyFaithful.SzF53MSecB
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecC

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.LieType.BorelTits Equiv

variable {G : Type} [Group G]

theorem exists_conj_mul_five (σ : Perm (Fin 5)) (hs : Perm.sign σ = 1) (h1 : σ ≠ 1)
    (h2 : σ * σ = 1) :
    ∃ ρ : Perm (Fin 5), (σ * (ρ * σ * ρ⁻¹)) ^ 5 = 1 ∧ σ * (ρ * σ * ρ⁻¹) ≠ 1 := by
  revert σ
  decide +kernel

variable [Finite G]

theorem two_lt_secIdx_of_A5_involution {H : Subgroup G}
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5)))
    {U A B : Subgroup G} (hUH : U ≤ H) (hUQ : U ≤ pCoreOf 2 H) (hs : IsChiefStep H U A B)
    (hnc : ¬ IsCentralStep H A B) {a : G} (ha : a ∈ H) (haQ : a ∉ pCoreOf 2 H)
    (ha2 : a ^ 2 ∈ pCoreOf 2 H) (haA : a ∈ oTwoRes H ⊔ pCoreOf 2 H) :
    2 < secIdx (Subgroup.zpowers a) A B := by
  by_contra hlt
  push Not at hlt
  obtain ⟨φ, hφs, hφk⟩ := exists_toPerm hq
  have hHA := normalizer_left hs
  have hHB := normalizer_right hs
  have hAB : A ≤ B := hs.2.2.1.le
  have hBH : B ≤ H := hs.1.1.trans hUH
  have hBA : B ≤ Subgroup.normalizer (A : Set G) := hBH.trans hHA
  have hB2 : IsPGroup 2 B := (pCoreOf_isPGroup 2 H).to_le (hs.1.1.trans hUQ)
  have hCQ := cSecIn_eq_pCoreOf_of_noncentral hq hUH hUQ hs hnc
  have hQC := pCoreOf_le_cSecIn_of_chiefStep hUH hUQ hs
  let aH : ↥H := ⟨a, ha⟩
  have hσ1 : φ aH ≠ 1 := fun h => haQ ((hφk aH).mp h)
  have hσ2 : φ aH * φ aH = 1 := by
    have h : φ (aH * aH) = 1 := (hφk _).mpr (by simpa [pow_two] using ha2)
    rwa [map_mul] at h
  have hσs : Perm.sign (φ aH) = 1 := by
    have hle : oTwoRes H ⊔ pCoreOf 2 H ≤ (Perm.sign.comp φ).ker.map H.subtype := by
      refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
      · rintro x ⟨hxH, m, hm, hxm⟩
        refine ⟨⟨x, hxH⟩, ?_, rfl⟩
        show Perm.sign (φ ⟨x, hxH⟩) = 1
        refine sign_eq_one_of_pow_eq_one hm ?_
        rw [← map_pow]
        have : (⟨x, hxH⟩ : ↥H) ^ m = 1 := Subtype.ext (by simpa using hxm)
        rw [this, map_one]
      · intro x hx
        refine ⟨⟨x, pCoreOf_le 2 H hx⟩, ?_, rfl⟩
        show Perm.sign (φ ⟨x, _⟩) = 1
        rw [(hφk _).mpr hx, map_one]
    obtain ⟨t, ht, hta⟩ := hle haA
    have : t = aH := Subtype.ext hta
    rw [← this]
    exact ht
  obtain ⟨ρ, hρ5, hρ1⟩ := exists_conj_mul_five (φ aH) hσs hσ1 hσ2
  obtain ⟨hH, hhρ⟩ := hφs ρ
  let cH : ↥H := aH * (hH * aH * hH⁻¹)
  have hcφ : φ cH = φ aH * (ρ * φ aH * ρ⁻¹) := by
    simp only [cH, map_mul, map_inv, hhρ]
  have hcval : (cH : G) = a * ((hH : G) * a * (hH : G)⁻¹) := rfl
  have hc5 : (cH : G) ^ 5 ∈ pCoreOf 2 H := by
    have h : φ (cH ^ 5) = 1 := by rw [map_pow, hcφ]; exact hρ5
    exact (hφk _).mp h
  have hcQ : (cH : G) ∉ pCoreOf 2 H := fun h => hρ1 (hcφ ▸ (hφk _).mpr h)
  have hhA : (hH : G) ∈ Subgroup.normalizer (A : Set G) := hHA hH.2
  have hhB : (hH : G) ∈ Subgroup.normalizer (B : Set G) := hHB hH.2
  have haA' : a ∈ Subgroup.normalizer (A : Set G) := hHA ha
  have ha'A : (hH : G) * a * (hH : G)⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    hHA (H.mul_mem (H.mul_mem hH.2 ha) (H.inv_mem hH.2))
  have hidx1 : (fixSecIn (Subgroup.zpowers a) A B).relIndex B ≤ 2 := hlt
  have hidx2 : (fixSecIn (Subgroup.zpowers ((hH : G) * a * (hH : G)⁻¹)) A B).relIndex B ≤ 2 := by
    rw [relIndex_fixSecIn_zpowers_conj hBA haA' hhA hhB]
    exact hidx1
  have hidx : (fixSecIn (Subgroup.zpowers (cH : G)) A B).relIndex B ≤ 4 := by
    rw [hcval]
    exact (relIndex_fixSecIn_zpowers_mul_le hBA haA' ha'A).trans (Nat.mul_le_mul hidx1 hidx2)
  have hcH : (cH : G) ∈ H := cH.2
  have hc5' : ∀ x ∈ B, (cH : G) ^ 5 * x * ((cH : G) ^ 5)⁻¹ * x⁻¹ ∈ A := fun x hx =>
    ((mem_cSecIn_iff hHA).mp (hQC hc5)).2 x hx
  have hall := commutator_mem_of_relIndex_le_four hAB hBA hB2 (hHA hcH) (hHB hcH) hc5' hidx
  have hcC : (cH : G) ∈ cSecIn H A B := Subgroup.subset_closure ⟨hcH, hall⟩
  exact hcQ (hCQ ▸ hcC)

end CFSG.Quasithin.F53Mod
