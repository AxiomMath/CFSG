module

public import CFSG.RankThree.PartTwo.Sec8.HeringU38MNF
public import CFSG.RankThree.PartTwo.Sec8.HeringU38MTransport

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.KFacts
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem congr_eq_mul {M : Type*} [Group M] (ψ φ : MulAut M) :
    MulAut.congr (ψ : M ≃* M) φ = ψ * φ * ψ⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

section SU

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem suDescend_unitaryProj (hq : 2 < 2 ^ 3) (β : MulAut (unitarySU 2 3 K 3))
    (x : unitarySU 2 3 K 3) :
    suDescend h hq β (unitaryProj h 3 x) = unitaryProj h 3 (β x) := rfl

theorem pow_three_eq_one_of_mem_unitaryScalars {z : unitarySU 2 3 K 3}
    (hz : z ∈ unitaryScalars h 3) : z ^ 3 = 1 := by
  obtain ⟨c, -, hc3, hzc⟩ := hz
  apply Subtype.ext
  rw [Subgroup.coe_pow, hzc, ← map_pow, hc3, map_one]
  rfl

theorem U38Hyps.descend (hq : 2 < 2 ^ 3) {α β : MulAut (unitarySU 2 3 K 3)}
    (hyps : U38Hyps (unitarySU 2 3 K 3) α β) :
    U38Hyps (unitaryPSU h 3) (suDescend h hq α) (suDescend h hq β) := by
  have := h.finite
  obtain ⟨hα3, hβ3, hαβ, hαout, ⟨u, hu, hu4, hu2⟩, hβ1, h7⟩ := hyps
  refine ⟨?_, ?_, ?_, ?_, ⟨unitaryProj h 3 u, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← map_pow, hα3, map_one]
  · rw [← map_pow, hβ3, map_one]
  · rw [← map_mul, ← map_mul, hαβ]
  · intro hin
    exact hαout ((isInnerAut_congr_centerDescend_iff h hq).mp hin)
  · rw [mem_u38Fix, suDescend_unitaryProj]
    exact congrArg _ ((mem_u38Fix).mp hu)
  · rw [← map_pow, hu4, map_one]
  · intro h1
    apply hu2
    have h2 : unitaryProj h 3 (u ^ 2) = 1 := by rw [map_pow, h1]
    have h3 : u ^ 2 ∈ unitaryScalars h 3 := by
      rw [← ker_unitaryProj]
      exact h2
    have h4 := pow_three_eq_one_of_mem_unitaryScalars h h3
    calc u ^ 2 = (u ^ 2) ^ 3 * ((u ^ 2) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h4, ← pow_mul, show 2 * 2 = 4 by norm_num, hu4]; group
  · intro h1
    apply hβ1
    exact eq_of_suDescend_eq h hq (h1.trans (map_one _).symm)
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨x, hx7⟩ := exists_prime_orderOf_dvd_card' (G := u38Fix β) 7 h7
    have hxfix : β (x : unitarySU 2 3 K 3) = x := x.2
    have hx7' : orderOf (x : unitarySU 2 3 K 3) = 7 := by rw [Subgroup.orderOf_coe, hx7]
    have hπx : orderOf (unitaryProj h 3 (x : unitarySU 2 3 K 3)) = 7 := by
      have hdvd : orderOf (unitaryProj h 3 (x : unitarySU 2 3 K 3)) ∣ 7 := by
        rw [← hx7']
        exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h1
      · exfalso
        rw [orderOf_eq_one_iff] at h1
        have h2 : (x : unitarySU 2 3 K 3) ∈ unitaryScalars h 3 := by
          rw [← ker_unitaryProj]
          exact h1
        have h3 := pow_three_eq_one_of_mem_unitaryScalars h h2
        have h4 := orderOf_dvd_of_pow_eq_one h3
        rw [hx7'] at h4
        norm_num at h4
      · exact h1
    let z : u38Fix (suDescend h hq β) := ⟨_, by
      rw [mem_u38Fix, suDescend_unitaryProj, hxfix]⟩
    have hz : orderOf z = 7 := by
      rw [← Subgroup.orderOf_coe]
      exact hπx
    have h1 := orderOf_dvd_natCard z
    rwa [hz] at h1

theorem su_nf {α β : MulAut (unitarySU 2 3 K 3)} (hyps : U38Hyps (unitarySU 2 3 K 3) α β) :
    ∃ (G D : unitaryIsom3 h) (σ : K ≃+* K) (ι : F →+* K) (l m : F), orderOf σ = 3 ∧
      (∀ a, σ (ι a) = ι a) ∧ (∀ y : K, σ y = y → ∃ a, ι a = y) ∧ RefData h ι l m D ∧
      α = suConj h G * suField h σ * (suConj h G)⁻¹ ∧
      β = suConj h G * suConj h D * (suConj h G)⁻¹ := by
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨hα3, hβ3, hαβ, hαout, hu4, hβ1, h7⟩ := U38Hyps.descend h hq hyps
  obtain ⟨G, D, σ, ι, l, m, hσ, hισ, hιs, hD, hα, hβ⟩ := nf_psu h hα3 hβ3 hαβ hαout
    (by obtain ⟨u, hu, h4, h2⟩ := hu4; exact ⟨u, mem_u38Fix.mp hu, h4, h2⟩) hβ1 h7
  refine ⟨G, D, σ, ι, l, m, hσ, hισ, hιs, hD, ?_, ?_⟩
  · apply eq_of_suDescend_eq h hq
    rw [hα, map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suField]
  · apply eq_of_suDescend_eq h hq
    rw [hβ, map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suConj]

include h in
theorem su_syl {α β : MulAut (unitarySU 2 3 K 3)} (hyps : U38Hyps (unitarySU 2 3 K 3) α β) :
    ∃ T : Subgroup (unitarySU 2 3 K 3), T ≤ u38Fix α ∧ Nat.card T = 8 ∧ (∀ x ∈ T, β x ∈ T) ∧
      T ≤ u38Comm T β := by
  obtain ⟨G, D, σ, ι, l, m, hσ, hισ, hιs, hD, hα, hβ⟩ := su_nf h hyps
  set ψ : MulAut (unitarySU 2 3 K 3) := suConj h G with hψ
  have e1 : MulAut.congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) α = suField h σ := by
    rw [congr_eq_mul, hα]
    group
  have e2 : MulAut.congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) β = suConj h D := by
    rw [congr_eq_mul, hβ]
    group
  apply syl_conclusion_congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3))
  rw [e1, e2]
  exact core_syl h ι ι.injective hισ hD

include h in
theorem su_p3 {α β : MulAut (unitarySU 2 3 K 3)} (hyps : U38Hyps (unitarySU 2 3 K 3) α β)
    {x : unitarySU 2 3 K 3} (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hαx : α x = x)
    (hxK : x ∈ (perfectResidual (u38Fix β)).map (u38Fix β).subtype) :
    x ∈ u38Two α ∧ ∀ z ∈ u38Two α, (∃ j : ℕ, z ^ 3 ^ j = 1) →
      z ∈ Subgroup.closure {y | ∃ g ∈ u38Two α, y = g * x * g⁻¹} := by
  obtain ⟨G, D, σ, ι, l, m, hσ, hισ, hιs, hD, hα, hβ⟩ := su_nf h hyps
  have := h.finite
  set ψ : MulAut (unitarySU 2 3 K 3) := suConj h G with hψ
  have e1 : MulAut.congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) α = suField h σ := by
    rw [congr_eq_mul, hα]
    group
  have e2 : MulAut.congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) β = suConj h D := by
    rw [congr_eq_mul, hβ]
    group
  have hαx' : suField h σ ((ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) x) =
      (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) x := by
    have h1 := congr_apply_e (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) α x
    rw [e1, hαx] at h1
    exact h1
  have hxK' := (mem_perfectResidual_congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) β x).mpr hxK
  rw [e2] at hxK'
  have hx1' : (ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) x ≠ 1 := by
    intro h1
    exact hx1 ((ψ⁻¹ : MulAut (unitarySU 2 3 K 3)).injective (h1.trans (map_one _).symm))
  have hx3' : ((ψ⁻¹ : MulAut (unitarySU 2 3 K 3)) x) ^ 3 = 1 := by
    rw [← map_pow, hx3, map_one]
  apply p3_conclusion_congr (ψ⁻¹ : MulAut (unitarySU 2 3 K 3))
  rw [e1]
  exact core_p3 h ι ι.injective hισ hιs hσ hD hx1' hx3' hαx' hxK'

end SU

end CFSG.RankThree.PartTwo.Sec8.HeringU38M
