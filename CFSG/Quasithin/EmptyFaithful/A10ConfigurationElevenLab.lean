module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationElevenModel
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTenK

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem isConj_ι {x y m : Wc} (h : m⁻¹ * x * m = y) : IsConj (E.ι x) (E.ι y) := by
  rw [isConj_iff]
  refine ⟨(E.ι m)⁻¹, ?_⟩
  rw [inv_inv, ← map_inv, ← map_mul, ← map_mul, h]

theorem frame_eq_false [Finite G] (hT : quasithinIsSylowTwo T) (hM : quasithinIsMaxTwoLocal M)
    {ℓ : Bool} {c : G} (hF : E.Frame ℓ) (hcs : E.Acts ℓ c s3)
    (hEc : ∀ x ∈ E.E₀, x * c = c * x)
    (htK : E.tK = (E.B : Set G) \ ({1} ∪ E.zK)) : ℓ = false := by
  by_contra hℓ
  have hℓ' : ℓ = true := by simpa using hℓ
  subst hℓ'
  obtain ⟨m₀, hm₀⟩ := z0_conj_e1u1
  obtain ⟨m₁, hm₁⟩ := e1u1_conj_e1t0'
  obtain ⟨m₂, hm₂⟩ := wrong_conj
  have he₁E : E.e₁ ∈ E.E₀ := ⟨e1, e1_mem_E0h, rfl⟩
  have hec : E.e₁ * c = c * E.e₁ := hEc _ he₁E
  have h1 : IsConj E.z (E.e₁ * E.u₁) := by
    have := E.isConj_ι hm₀
    rwa [map_mul] at this
  have h2 : IsConj (E.e₁ * E.u₁) (E.e₁ * (E.pt true 3 * E.pt true 4)) := by
    have := E.isConj_ι hm₁
    have e3 : E.ι t0' = E.pt true 3 * E.pt true 4 := by
      show E.ι t0' = E.ι (ptm true 3) * E.ι (ptm true 4)
      rw [← map_mul, ptm_three_four]
    rwa [map_mul, map_mul, e3] at this
  have h3 : IsConj (E.e₁ * (E.pt true 3 * E.pt true 4)) (E.e₁ * (E.pt true 0 * E.pt true 4)) := by
    rw [isConj_iff]
    refine ⟨c, ?_⟩
    have hk := E.acts_conj_pair hcs 3 4
    have hs : s3 3 = 4 ∧ s3 4 = 0 := ⟨s3_apply.2.1, s3_apply.2.2.1⟩
    rw [hs.1, hs.2] at hk
    calc c * (E.e₁ * (E.pt true 3 * E.pt true 4)) * c⁻¹
        = (c * E.e₁ * c⁻¹) * (c * (E.pt true 3 * E.pt true 4) * c⁻¹) := by group
      _ = E.e₁ * (E.pt true 4 * E.pt true 0) := by
          rw [hk, ← hec]
          group
      _ = E.e₁ * (E.pt true 0 * E.pt true 4) := by rw [E.pt_comm true 4 0]
  have h4 : IsConj (E.e₁ * (E.pt true 0 * E.pt true 4)) (E.pt true 0 * E.pt true 4) := by
    have h := E.isConj_ι hm₂
    simp only [map_mul] at h
    exact h
  have h5 : IsConj (E.pt true 0 * E.pt true 4) E.t := by
    have hmem : E.pt true 0 * E.pt true 4 ∈ E.tK := by
      rw [htK]
      refine ⟨E.B.mul_mem (E.pt_mem_B true 0) (E.pt_mem_B true 4), ?_⟩
      rintro (h | h)
      · have h' : E.ι (ptm true 0 * ptm true 4) = E.ι 1 := by
          rw [map_mul, map_one]
          exact h
        exact pair_ne_one true 0 4 (by decide) (E.injective h')
      · obtain ⟨i, hi⟩ := (E.mem_zK_iff_pt hF).1 h
        have hi' : E.ι (ptm true 0 * ptm true 4) = E.ι (ptm true i) := by
          rw [map_mul]
          exact hi
        exact pair_ne_pt true 0 4 i (by decide) (E.injective hi')
    obtain ⟨k, -, hk⟩ := hmem
    rw [isConj_iff]
    exact ⟨k, by rw [← hk]; group⟩
  have hzt : IsConj E.z E.t := h1.trans (h2.trans (h3.trans (h4.trans h5)))
  rw [isConj_iff] at hzt
  obtain ⟨g, hg⟩ := hzt
  exact E.t_not_conj_z hT hM ⟨g⁻¹, by rw [inv_inv]; exact hg⟩

end Emb

end CFSG.Quasithin.A10
