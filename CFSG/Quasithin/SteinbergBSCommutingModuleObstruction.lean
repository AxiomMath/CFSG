module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_commutator_eq {U : Subgroup G} (hU : ∀ s ∈ U, ∀ t ∈ U, s * t = t * s)
    {k d u : G} (hk : k ∈ normalizer (U : Set G)) (hd : d ∈ normalizer (U : Set G))
    (hkd : ⁅k, d⁆ ∈ centralizer (U : Set G)) (hu : u ∈ U) :
    ⁅⁅u, d⁆, k⁆ = ⁅k * u * k⁻¹ * u⁻¹, d⁆⁻¹ := by
  have hkU : ∀ s ∈ U, k * s * k⁻¹ ∈ U := fun s hs => (mem_normalizer_iff.1 hk s).1 hs
  have hdU : ∀ s ∈ U, d * s * d⁻¹ ∈ U := fun s hs => (mem_normalizer_iff.1 hd s).1 hs
  have hb : d * u * d⁻¹ ∈ U := hdU u hu
  have hc : k * u * k⁻¹ ∈ U := hkU u hu
  have hee : k * (d * u * d⁻¹) * k⁻¹ = d * (k * u * k⁻¹) * d⁻¹ := by
    have hz := mem_centralizer_iff.1 hkd _ (hdU _ hc)
    rw [commutatorElement_def] at hz
    calc k * (d * u * d⁻¹) * k⁻¹
        = k * d * k⁻¹ * d⁻¹ * (d * (k * u * k⁻¹) * d⁻¹) * (k * d * k⁻¹ * d⁻¹)⁻¹ := by group
      _ = d * (k * u * k⁻¹) * d⁻¹ * (k * d * k⁻¹ * d⁻¹) * (k * d * k⁻¹ * d⁻¹)⁻¹ := by rw [← hz]
      _ = d * (k * u * k⁻¹) * d⁻¹ := by group
  have hlhs : ⁅⁅u, d⁆, k⁆ =
      u * (d * u * d⁻¹)⁻¹ * (k * (d * u * d⁻¹) * k⁻¹) * (k * u * k⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  have hrhs : ⁅k * u * k⁻¹ * u⁻¹, d⁆⁻¹ =
      d * (k * u * k⁻¹) * d⁻¹ * (d * u * d⁻¹)⁻¹ * u * (k * u * k⁻¹)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hlhs, hrhs, ← hee]
  generalize hB : d * u * d⁻¹ = B at hb ⊢
  generalize hC : k * u * k⁻¹ = C
  have he' : k * B * k⁻¹ ∈ U := hkU B hb
  generalize hE : k * B * k⁻¹ = E at he' ⊢
  have h1 : B⁻¹ * E = E * B⁻¹ := hU _ (U.inv_mem hb) _ he'
  have h2 : u * (B⁻¹ * E) = B⁻¹ * E * u := hU _ hu _ (U.mul_mem (U.inv_mem hb) he')
  calc u * B⁻¹ * E * C⁻¹ = u * (B⁻¹ * E) * C⁻¹ := by rw [mul_assoc u]
    _ = B⁻¹ * E * u * C⁻¹ := by rw [h2]
    _ = E * B⁻¹ * u * C⁻¹ := by rw [h1]

theorem five_commuting_module_centralizer_obstruction {p : ℕ} {U K D : Subgroup G}
    [IsElementaryAbelian p U] (hK : K ≤ normalizer (U : Set G)) (hD : D ≤ normalizer (U : Set G))
    (hKD : ⁅K, D⁆ ≤ centralizer (U : Set G)) (hUKD : ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥) :
    K ≤ centralizer ((⁅U, D⁆ : Subgroup G) : Set G) ∧
      ∀ (M : Subgroup G) (v : G), v ∈ ⁅U, D⁆ → v ≠ 1 → centralizer ({v} : Set G) ≤ M → K ≤ M := by
  have hU : ∀ s ∈ U, ∀ t ∈ U, s * t = t * s := fun s hs t ht =>
    congrArg Subtype.val (mul_comm' (⟨s, hs⟩ : U) ⟨t, ht⟩)
  have hcent : K ≤ centralizer ((⁅U, D⁆ : Subgroup G) : Set G) := by
    rw [le_centralizer_iff, commutator_le]
    intro u hu d hd k hk
    have hx : ⁅u, d⁆ ∈ U := by
      have h1 : d * u⁻¹ * d⁻¹ ∈ U := (mem_normalizer_iff.1 (hD hd) _).1 (U.inv_mem hu)
      have h2 := U.mul_mem hu h1
      rw [commutatorElement_def]
      rwa [show u * (d * u⁻¹ * d⁻¹) = u * d * u⁻¹ * d⁻¹ by group] at h2
    have hy1 : ⁅⁅u, d⁆, k⁆ ∈ ⁅U, K⁆ := commutator_mem_commutator hx hk
    have hy2 : ⁅⁅u, d⁆, k⁆ ∈ ⁅U, D⁆ := by
      rw [commutatorElement_commutator_eq hU (hK hk) (hD hd)
        (hKD (commutator_mem_commutator hk hd)) hu]
      refine inv_mem (commutator_mem_commutator ?_ hd)
      have h1 : k * u * k⁻¹ ∈ U := (mem_normalizer_iff.1 (hK hk) u).1 hu
      exact U.mul_mem h1 (U.inv_mem hu)
    have hy : ⁅⁅u, d⁆, k⁆ = 1 := by
      have h := mem_inf.2 ⟨hy1, hy2⟩
      rwa [hUKD, mem_bot] at h
    rw [commutatorElement_eq_one_iff_mul_comm] at hy
    exact hy.symm
  refine ⟨hcent, fun M v hv _ hvM => le_trans ?_ hvM⟩
  exact hcent.trans (centralizer_le (Set.singleton_subset_iff.2 hv))

end CFSG.Quasithin.SteinbergBS
