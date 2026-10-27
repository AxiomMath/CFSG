module

public import CFSG.Quasithin.Vol2.Ch3E213MG41PC2

public section

namespace CFSG.Quasithin.Ch3E213M.G41.Big

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp)

variable {k : Type} [Field k] [CharP k 2] {G₀ : Subgroup (antiSp k)} {F₁ : Subfield k}
  {e e' : Fin 4 → k}

theorem exists_quad_of_caseB (hone : Refl.OnePerCentre G₀) (hB : CaseB G₀ F₁ e e') :
    ∃ Q : QuadraticForm k (Fin 4 → k), (∀ x y, QuadraticMap.polar Q x y = spBil x y) ∧
      Q (eOne k) ≠ 0 ∧ ∀ z ∈ Refl.normC G₀, z 2 = 0 → proj z ≠ 0 → Q z = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨μ, hμ0, hμ1⟩ := hB.exists_ne
  have : Finite F₁ := Nat.finite_of_card_ne_zero (by have := hB.four; omega)
  have hsq : ∀ a : F₁, ∃ r : F₁, r ^ 2 = a := fun a => Refl.exists_sq_eq a
  choose r hr using hsq
  obtain ⟨L, hLc, hL⟩ := hB.exists_lift hone
  obtain ⟨A, B, θ, hABθ⟩ := exists_eq_lin_add_h (fun a => ⟨r a, hr a⟩) hr hμ0 hμ1 hLc
  have hABθ' : ∀ x : F₁ × F₁, x ≠ 0 →
      L x = (x.1 : k) * A + (x.2 : k) * B + θ * (1 + (r (x.1 * x.2) : k)) := hABθ
  have hθ : θ ≠ 0 := by
    intro hθ0
    have hx1 : ((1 : F₁), (0 : F₁)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)
    have hxμ : (μ, (0 : F₁)) ≠ 0 := fun h => hμ0 (congrArg Prod.fst h)
    have m1 : e + A • eOne k ∈ Refl.normC G₀ := by
      have h := hL _ hx1
      rw [hABθ' _ hx1, hθ0] at h
      simpa using h
    have m2 : (μ : k) • (e + A • eOne k) ∈ Refl.normC G₀ := by
      have h := hL _ hxμ
      rw [hABθ' _ hxμ, hθ0] at h
      rw [smul_add, smul_smul]
      simpa using h
    exact hμ1 (Subtype.ext (Refl.eq_one_of_smul_mem hone m1 m2))
  let Q : QuadraticForm k (Fin 4 → k) :=
    QuadraticMap.linMulLin (spBil e') (spBil e) +
      QuadraticMap.linMulLin (spBil (Pi.single 2 1)) (spBil (eOne k)) +
      θ⁻¹ ^ 2 • QuadraticMap.linMulLin (spBil (A • e' + B • e + Pi.single 2 1))
        (spBil (A • e' + B • e + Pi.single 2 1))
  have hQ : ∀ x, Q x = spBil e' x * spBil e x + x 1 * x 2 +
      θ⁻¹ ^ 2 * (A * spBil e' x + B * spBil e x + x 1) ^ 2 := by
    intro x
    simp only [Q, add_apply, smul_apply, QuadraticMap.linMulLin_apply,
      smul_eq_mul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, bil_eTwo_left,
      bil_eOne_left]
    ring
  refine ⟨Q, fun x y => ?_, ?_, fun z hz hz2 hp0 => ?_⟩
  ·
    unfold QuadraticMap.polar
    rw [hQ, hQ, hQ, hB.bil_eq x y]
    simp only [map_add, Pi.add_apply]
    linear_combination (θ⁻¹ ^ 2 * (A * spBil e' x + B * spBil e x + x 1) *
      (A * spBil e' y + B * spBil e y + y 1)) * h2
  ·
    rw [hQ, bil_eOne, bil_eOne, hB.supp.2.1, hB.supp.2.2.2]
    simp [eOne, hθ]
  ·
    obtain ⟨a, ha, b, hb, hzp⟩ := hB.image z hz hz2 hp0
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      apply hp0
      rw [hzp, h.1, h.2, zero_smul, zero_smul, add_zero]
    have hzf : z = a • e + b • e' + z 1 • eOne k := by
      rw [← hzp]
      exact eq_proj_add hz2
    have hx : ((⟨a, ha⟩ : F₁), (⟨b, hb⟩ : F₁)) ≠ 0 := by
      intro h
      rcases hab with hab | hab
      · exact hab (congrArg (fun p : F₁ × F₁ => (p.1 : k)) h)
      · exact hab (congrArg (fun p : F₁ × F₁ => (p.2 : k)) h)
    have hz' : a • e + b • e' + z 1 • eOne k ∈ Refl.normC G₀ := by
      rw [← hzf]
      exact hz
    have hl : z 1 = a * A + b * B + θ * (1 + ((r (⟨a, ha⟩ * ⟨b, hb⟩) : F₁) : k)) :=
      (hB.eq_of_mem hone hab hz' (hL _ hx)).trans (hABθ' _ hx)
    have hs : ((r (⟨a, ha⟩ * ⟨b, hb⟩) : F₁) : k) ^ 2 = a * b := by
      have := congrArg (fun t : F₁ => (t : k)) (hr (⟨a, ha⟩ * ⟨b, hb⟩))
      simpa using this
    generalize ((r (⟨a, ha⟩ * ⟨b, hb⟩) : F₁) : k) = s at hl hs
    have he'z : spBil e' z = a := by rw [hzf]; exact hB.bil_left_frame a b (z 1)
    have hez : spBil e z = b := by rw [hzf]; exact hB.bil_right_frame a b (z 1)
    have ht : θ⁻¹ * θ = 1 := inv_mul_cancel₀ hθ
    rw [hQ, he'z, hez, hz2]
    linear_combination (a * b + s + 2 * θ⁻¹ ^ 2 * (a * A + b * B) ^ 2 +
      2 * θ⁻¹ ^ 2 * θ * (a * A + b * B) * (1 + s)) * h2 + hs +
      (1 + s) ^ 2 * (θ⁻¹ * θ + 1) * ht +
      θ⁻¹ ^ 2 * (3 * (a * A + b * B) + θ * (1 + s) + z 1) * hl

end CFSG.Quasithin.Ch3E213M.G41.Big
