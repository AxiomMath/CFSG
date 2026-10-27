module

public import CFSG.LocalAnalysis.StandardType.GGCentralExtTwoSubgroup
public import CFSG.LocalAnalysis.StandardType.GGPowTwoPowFactor
public import CFSG.LocalAnalysis.StandardType.GGSummandSigmaRho

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Config

variable {X : Type} [Group X] [Finite X] (V E K : Subgroup X)
  [hN : ((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

theorem ggSum_rho_eq_one_of_mem_U (h : ↥(E ⊔ (K ⊓ V))) (hh : (h : X) ∈ ggRCSU V E K) :
    ggSumRho V E K h = 1 := by
  change QuotientGroup.mk' (CFSG.pCore 2 ↥(ggSumT V E K)) (ggSumSigma V E K h) = 1
  rw [(ggSum_sigma_eq_one V E K h).mpr hh]
  exact map_one _

variable {p : ℕ} {Q : Subgroup X} {𝒞 : Set (Subgroup X)}
  (hp : p.Prime) (hp2 : p ≠ 2) (hE : IsElemAbelian p E) (hEV : E ≤ V)
  (hEK : E ≤ Subgroup.normalizer (K : Set X)) (hS : GGSummandStruct E K V Q 𝒞)

include hp hp2 hE hEV hEK hS

theorem ggSum_ker_rho (h : ↥(E ⊔ (K ⊓ V))) :
    ggSumRho V E K h = 1 ↔ (h : X) ∈ Q ⊔ ggRCSU V E K := by
  have hQ : pCoreOf 2 (K ⊓ V) = Q := hS.1
  have hNH : K ⊓ V ≤ E ⊔ (K ⊓ V) := le_sup_right
  have hUH : ggRCSU V E K ≤ E ⊔ (K ⊓ V) := inf_le_left
  have hENV : E ≤ Subgroup.normalizer ((K ⊓ V : Subgroup X) : Set X) :=
    le_normalizer_inf_of_le hEV hEK
  constructor
  · intro hh
    obtain ⟨k, hk⟩ := ggSum_exists_pow_mem_U V E K h hh
    obtain ⟨n, hn, u, hu, hnu⟩ :=
      exists_mul_of_pow_two_pow_mem hp hp2 hE hENV hUH h.2 hk
    let R : Subgroup X := ((ggSumRho V E K).ker.map (E ⊔ (K ⊓ V)).subtype) ⊓ (K ⊓ V)
    have hmemR : ∀ x : X, x ∈ R ↔ ∃ hx : x ∈ E ⊔ (K ⊓ V), ggSumRho V E K ⟨x, hx⟩ = 1 ∧
        x ∈ K ⊓ V := by
      intro x
      constructor
      · rintro ⟨hx1, hx2⟩
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx1
        exact ⟨y.2, hy, hx2⟩
      · rintro ⟨hx, hρ, hxN⟩
        exact ⟨Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hρ, rfl⟩, hxN⟩
    have hnR : n ∈ R := by
      rw [hmemR]
      have hnH : n ∈ E ⊔ (K ⊓ V) := hNH hn
      refine ⟨hnH, ?_, hn⟩
      have h1 : (⟨n, hnH⟩ : ↥(E ⊔ (K ⊓ V))) = h * ⟨u, hUH hu⟩⁻¹ := by
        apply Subtype.ext
        simp [hnu]
      rw [h1, map_mul, map_inv, hh, ggSum_rho_eq_one_of_mem_U V E K _ hu]
      simp
    have hRN : R ≤ K ⊓ V := inf_le_right
    have hRnorm : ∀ n' ∈ K ⊓ V, ∀ x ∈ R, n' * x * n'⁻¹ ∈ R := by
      intro n' hn' x hx
      rw [hmemR] at hx ⊢
      obtain ⟨hxH, hρ, hxN⟩ := hx
      refine ⟨(E ⊔ (K ⊓ V)).mul_mem ((E ⊔ (K ⊓ V)).mul_mem (hNH hn') hxH)
        ((E ⊔ (K ⊓ V)).inv_mem (hNH hn')), ?_, ?_⟩
      · have h2 : (⟨n' * x * n'⁻¹, (E ⊔ (K ⊓ V)).mul_mem ((E ⊔ (K ⊓ V)).mul_mem (hNH hn') hxH)
            ((E ⊔ (K ⊓ V)).inv_mem (hNH hn'))⟩ : ↥(E ⊔ (K ⊓ V))) =
            ⟨n', hNH hn'⟩ * ⟨x, hxH⟩ * ⟨n', hNH hn'⟩⁻¹ := rfl
        rw [h2, map_mul, map_mul, hρ, map_inv]
        simp
      · exact (K ⊓ V).mul_mem ((K ⊓ V).mul_mem hn' hxN) ((K ⊓ V).inv_mem hn')
    have hcent : ∀ x ∈ R ⊓ ggRCSU V E K, ∀ y ∈ R, x * y = y * x := by
      intro x hx y hy
      have hxU : x ∈ Subgroup.centralizer (K : Set X) := (inf_le_right : ggRCSU V E K ≤ _)
        (Subgroup.mem_inf.mp hx).2
      have hyK : y ∈ K := (hRN hy).1
      exact (Subgroup.mem_centralizer_iff.mp hxU y hyK).symm
    have h2pow : ∀ y ∈ R, ∃ k : ℕ, y ^ (2 ^ k) ∈ ggRCSU V E K := by
      intro y hy
      obtain ⟨hyH, hρ, -⟩ := (hmemR y).mp hy
      have := ggSum_exists_pow_mem_U V E K ⟨y, hyH⟩ hρ
      simpa using this
    obtain ⟨P, hPR, hP2, hPn, hRP⟩ :=
      exists_normal_two_subgroup_of_central_ext hRN hRnorm hcent h2pow
    have hPQ : P ≤ Q := by
      rw [← hQ]
      exact le_pCoreOf_of_normalized 2 (hPR.trans hRN) hP2 hPn
    have hnQU : n ∈ Q ⊔ ggRCSU V E K :=
      (sup_le_sup_right hPQ _) (hRP hnR)
    have hQU : (h : X) = n * u := hnu
    rw [hQU]
    exact (Q ⊔ ggRCSU V E K).mul_mem hnQU
      ((le_sup_right : ggRCSU V E K ≤ Q ⊔ ggRCSU V E K) hu)
  · intro hh
    let K₀ : Subgroup X := (ggSumRho V E K).ker.map (E ⊔ (K ⊓ V)).subtype
    have hQK : Q ≤ K₀ := by
      intro q hq
      have hq' : q ∈ pCoreOf 2 (K ⊓ V) := hQ ▸ hq
      have hqH : q ∈ E ⊔ (K ⊓ V) := hNH (pCoreOf_le' 2 _ hq')
      exact Subgroup.mem_map.mpr ⟨⟨q, hqH⟩, ggSum_rho_eq_one_of_mem_pCore V E K hEV hEK _ hq', rfl⟩
    have hUK : ggRCSU V E K ≤ K₀ := by
      intro u hu
      exact Subgroup.mem_map.mpr ⟨⟨u, hUH hu⟩,
        ggSum_rho_eq_one_of_mem_U V E K _ hu, rfl⟩
    obtain ⟨h', hh', hh'eq⟩ := Subgroup.mem_map.mp ((sup_le hQK hUK) hh)
    have : h' = h := Subtype.ext hh'eq
    rw [← this]
    exact hh'

end Config

end CFSG.StandardType
