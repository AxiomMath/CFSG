module

public import CFSG.Quasithin.Vol2.Ch12Sec8OnePara

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L1294

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizerMod_of_mem_normalizer {T L V : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (hs : Setting1282One G T L V n V₁ V₂) {h : G}
    (hh₁ : h ∈ Subgroup.normalizer (V₁ : Set G)) (hh₂ : h ∈ Subgroup.normalizer (V₂ : Set G)) :
    h ∈ centralizerMod V₁ (Subgroup.normalizer (V₁ : Set G)) V₂ := by
  obtain ⟨-, -, hab⟩ := hs.hyp.card_sq
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, a, ha, haV₁⟩ := L128P.exists_gens hV₁2 hV₂4
  have hhz : h * z * h⁻¹ = z := L1297.conj_eq_of_mem_normalizer hV₁2 hz hh₁
  have hcomm : h * a * h⁻¹ * a⁻¹ ∈ V₁ := by
    have hha : h * a * h⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.1 hh₂ a).1 ha
    have hhaV₁ : h * a * h⁻¹ ∉ V₁ := fun hm => haV₁ ((Subgroup.mem_normalizer_iff.1 hh₁ a).2 hm)
    rcases L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ ha hha with e | e | e | e
    · exact absurd (by rw [e]; exact V₁.one_mem) hhaV₁
    · exact absurd (by rw [e]; exact hz) hhaV₁
    · rw [e, mul_inv_cancel]
      exact V₁.one_mem
    · rw [e, mul_inv_cancel_right]
      exact hz
  refine ⟨hh₁, hh₁, fun w hw => ?_⟩
  rcases L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ ha hw with e | e | e | e <;> rw [e]
  · simp
  · rw [hhz, mul_inv_cancel]
    exact V₁.one_mem
  · exact hcomm
  · have e2 : h * (z * a) * h⁻¹ * (z * a)⁻¹ = (h * z * h⁻¹) * (h * a * h⁻¹ * a⁻¹) * z⁻¹ := by
      group
    rw [e2, hhz]
    have hc' : h * a * h⁻¹ * a⁻¹ ∈ V := hs.v1.1 hcomm
    rw [hab z (hs.v1.1 hz) _ hc']
    have e3 : h * a * h⁻¹ * a⁻¹ * z * z⁻¹ = h * a * h⁻¹ * a⁻¹ := by group
    rw [e3]
    exact hcomm

end L1294

end CFSG.Quasithin.H13
