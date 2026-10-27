
module

public import CFSG.Quasithin.Background.A3Structure36BCommonBase

public import CFSG.Quasithin.Background.A3Structure36BElem
public import CFSG.Quasithin.Background.A3Structure36BHeis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement

variable {X : Type} [Group X]

theorem pCore_le_commutator_radical (hF : A36CaseBFacts) (h : A36BHyp X) {K : Subgroup X}
    (hK : KernelSetup X K) {t : X} (ht : t ∈ CFSG.solvableRadical X) (ht2 : t ^ 2 = 1)
    (htK : t ∉ K) {q : ℕ} (hq : q.Prime) (hqF : q ∣ Nat.card (CFSG.fittingSubgroup X)) :
    CFSG.pCore q X ≤ ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ := by
  have hfin : Finite X := h.finite
  have hfq : Fact q.Prime := ⟨hq⟩
  have hπ : IsPi X q := isPi_of_dvd_card_fitting hF h hK hq hqF
  have hq2 : q ≠ 2 := IsPi.ne_two h hπ
  obtain ⟨D, hDK⟩ := hK.prime q hq hπ
  have hRp : IsPGroup q ↥(CFSG.pCore q X) := CFSG.pCore_isPGroup
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hodd : ∀ r : ↥(CFSG.pCore q X), Odd (orderOf r) := by
    intro r
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hRp) r
    rw [hk]
    exact hqodd.pow
  have hOR : CFSG.pCore q X ≤ CFSG.solvableRadical X :=
    (CFSG.pCore_le_fitting X q).trans fitting_le_radical
  have ht2K : t ^ 2 ∈ D.K := by rw [hDK, ht2]; exact K.one_mem
  have htDK : t ∉ D.K := by rw [hDK]; exact htK
  rcases D.iso with hE | hH
  · obtain ⟨-, hinvR, -⟩ := elem_case h hK hq D hDK hE ht2 htK
    intro x hx
    have hcomm : ⁅t, x⁆ ∈ ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ :=
      Subgroup.commutator_mem_commutator ht (hOR hx)
    have h1 := congrArg Subtype.val (hinvR ⟨x, hx⟩)
    simp only [MulAut.conjNormal_apply, Subgroup.coe_inv] at h1
    have h2 : ⁅t, x⁆ = (x ^ 2)⁻¹ := by
      rw [commutatorElement_def, h1, pow_two, mul_inv_rev]
    have h3 : x ^ 2 ∈ ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ := by
      have := inv_mem (h2 ▸ hcomm)
      simpa using this
    refine mem_of_sq_mem_of_odd_orderOf h3 ?_
    have := hodd ⟨x, hx⟩
    rwa [← Subgroup.orderOf_coe] at this
  · have hP : D.P = ⊤ := eq_top_of_isPOnePlusTwo h hK hF.l2mult hq D hDK hH
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : Subgroup X,
        N₀ = ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ := ⟨_, rfl⟩
    rw [← hN₀]
    let ι : ↥D.P →* X := (CFSG.pCore q X).subtype.comp D.P.subtype
    have hdn : ∀ d : ↥D.P, d ^ 2 ∈ N₀.comap ι ⊔ frattini ↥D.P := by
      intro d
      obtain ⟨φ, hφ, hφd⟩ := D.inv_W t htDK ht2K (d : ↥(CFSG.pCore q X)) d.2
      have hφ' : φ ∈ frattini ↥D.P := hφ
      have e1 : ι φ = ι d * (t * ι d * t⁻¹) := by
        have h5 := congrArg (fun z : ↥(CFSG.pCore q X) => (z : X)) hφd
        simpa [ι, MulAut.conjNormal_apply] using h5
      have hc : ι (d⁻¹ * φ * d⁻¹) = ⁅t, ι d⁆ := by
        rw [map_mul, map_mul, map_inv, e1, commutatorElement_def]
        group
      have hcmem : d⁻¹ * φ * d⁻¹ ∈ N₀.comap ι := by
        rw [Subgroup.mem_comap, hc, hN₀]
        exact Subgroup.commutator_mem_commutator ht (hOR (d : ↥(CFSG.pCore q X)).2)
      have hconj : d⁻¹ * φ * d ∈ frattini ↥D.P := by
        have := (inferInstance : (frattini ↥D.P).Normal).conj_mem φ hφ' d⁻¹
        simpa using this
      have e2 : (d ^ 2)⁻¹ = (d⁻¹ * φ * d)⁻¹ * (d⁻¹ * φ * d⁻¹) := by group
      have h6 : (d ^ 2)⁻¹ ∈ N₀.comap ι ⊔ frattini ↥D.P := by
        rw [e2]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (inv_mem hconj))
          (Subgroup.mem_sup_left hcmem)
      simpa using inv_mem h6
    have hall : N₀.comap ι ⊔ frattini ↥D.P = ⊤ := by
      rw [eq_top_iff]
      intro d _
      have hdq : d ^ q = 1 := Subtype.ext (by
        simpa using D.supercritical.pow_eq_one (d : ↥(CFSG.pCore q X)) d.2)
      obtain ⟨m, hm⟩ := hqodd
      have hd : d = (d ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = q + 1 by omega, pow_succ, hdq, one_mul]
      rw [hd]
      exact pow_mem (hdn d) _
    have hclos : N₀.comap ι = ⊤ := frattini_nongenerating hall
    intro x hx
    have hxP : (⟨x, hx⟩ : ↥(CFSG.pCore q X)) ∈ D.P := hP ▸ Subgroup.mem_top _
    have hmem : (⟨⟨x, hx⟩, hxP⟩ : ↥D.P) ∈ N₀.comap ι := hclos ▸ Subgroup.mem_top _
    exact hmem

theorem commutator_radical_eq_fitting (hF : A36CaseBFacts) (h : A36BHyp X) {K : Subgroup X}
    (hK : KernelSetup X K) :
    ⁅CFSG.solvableRadical X, CFSG.solvableRadical X⁆ = CFSG.fittingSubgroup X := by
  have hfin : Finite X := h.finite
  apply le_antisymm (commutator_radical_le_fitting h hK)
  obtain ⟨t, ht, ht2, htK⟩ := exists_involution h hK
  rw [fitting_eq_iSup_primes]
  refine iSup_le fun q => ?_
  have hq : (q : ℕ).Prime := q.2
  have hfq : Fact (q : ℕ).Prime := ⟨hq⟩
  by_cases hqF : (q : ℕ) ∣ Nat.card (CFSG.fittingSubgroup X)
  · exact pCore_le_commutator_radical hF h hK ht ht2 htK hq hqF
  · have hbot : CFSG.pCore (q : ℕ) X = ⊥ := by
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := (q : ℕ)) (G := X)).exists_card_eq
      have hdvd : Nat.card (CFSG.pCore (q : ℕ) X) ∣ Nat.card (CFSG.fittingSubgroup X) :=
        Subgroup.card_dvd_of_le (CFSG.pCore_le_fitting X q)
      have hk0 : k = 0 := by
        by_contra hk0
        exact hqF ((dvd_pow_self (q : ℕ) hk0).trans (hk ▸ hdvd))
      rw [hk0, pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    rw [hbot]
    exact bot_le

end CFSG.Quasithin.A36B
