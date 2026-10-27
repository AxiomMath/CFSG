module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.Sylow

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T73Inf

variable {G : Type*} [Group G]

theorem exists_mul_of_sylow [Finite G] {Ω : Set (Subgroup G)} {H P : Subgroup G}
    (hΩ : IsDirectProduct Ω H) {r : ℕ} (hr : r.Prime) (hPH : P ≤ H) (hP : IsPGroup r P)
    (hidx : Nat.Coprime (P.relIndex H) r) {R : Subgroup G} (hR : R ∈ Ω) :
    ∀ x ∈ P, ∃ k ∈ P ⊓ R, ∃ l ∈ P ⊓ sSup (Ω \ {R}), x = k * l :=
  (exists_mul_of_maximal_of_isDirectPair (hΩ.isDirectPair hR) hPH hP fun _ hQH hQ hPQ =>
    eq_of_le_of_coprime_relIndex hr hPH hP hidx hQH hQ hPQ).1

theorem mem_zOf_of_mul_eq [Finite G] {Ω : Set (Subgroup G)} {H P : Subgroup G}
    (hΩ : IsDirectProduct Ω H) {r : ℕ} (hr : r.Prime) (hPH : P ≤ H) (hP : IsPGroup r P)
    (hidx : Nat.Coprime (P.relIndex H) r) {R : Subgroup G} (hR : R ∈ Ω) {y t l : G}
    (hy : y ∈ zOf P) (ht : t ∈ R) (hl : l ∈ sSup (Ω \ {R})) (hytl : t * l = y) :
    t ∈ zOf P := by
  obtain ⟨hyP, hyc⟩ := mem_zOf_iff.mp hy
  have hsplit := exists_mul_of_sylow hΩ hr hPH hP hidx hR
  obtain ⟨k, hk, l', hl', hkl⟩ := hsplit y hyP
  have hdp := hΩ.isDirectPair hR
  have htk : t = k := by
    have h1 : k⁻¹ * t = l' * l⁻¹ := by
      have h2 : k * l' = t * l := hkl.symm.trans hytl.symm
      calc k⁻¹ * t = k⁻¹ * (t * l) * l⁻¹ := by group
        _ = k⁻¹ * (k * l') * l⁻¹ := by rw [h2]
        _ = l' * l⁻¹ := by group
    have h3 : k⁻¹ * t ∈ R ⊓ sSup (Ω \ {R}) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hk).2) ht, ?_⟩
      rw [h1]
      exact mul_mem (Subgroup.mem_inf.mp hl').2 (inv_mem hl)
    rw [hdp.inf_eq_bot, Subgroup.mem_bot] at h3
    exact (inv_mul_eq_one.mp h3).symm
  have htP : t ∈ P := htk ▸ (Subgroup.mem_inf.mp hk).1
  refine mem_zOf_iff.mpr ⟨htP, fun w hw => ?_⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, hww⟩ := hsplit w hw
  have hw₁t : w₁ * t = t * w₁ := by
    have h1 := hyc w₁ (Subgroup.mem_inf.mp hw₁).1
    have h2 : w₁ * l = l * w₁ := (hdp.commute w₁ (Subgroup.mem_inf.mp hw₁).2 l hl).eq
    have h3 : w₁ * t * l = t * w₁ * l := by
      calc w₁ * t * l = w₁ * (t * l) := by group
        _ = w₁ * y := by rw [hytl]
        _ = y * w₁ := h1
        _ = t * (l * w₁) := by rw [← hytl]; group
        _ = t * (w₁ * l) := by rw [h2]
        _ = t * w₁ * l := by group
    exact mul_right_cancel h3
  have htw₂ : t * w₂ = w₂ * t := (hdp.commute t ht w₂ (Subgroup.mem_inf.mp hw₂).2).eq
  rw [hww]
  calc w₁ * w₂ * t = w₁ * (w₂ * t) := by group
    _ = w₁ * (t * w₂) := by rw [htw₂]
    _ = (w₁ * t) * w₂ := by group
    _ = (t * w₁) * w₂ := by rw [hw₁t]
    _ = t * (w₁ * w₂) := by group

end T73Inf

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
